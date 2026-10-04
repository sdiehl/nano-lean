//! Development driver for the new term representation, importer and checker.

#[path = "../src/checker/mod.rs"]
pub mod checker;
#[path = "../src/import/mod.rs"]
pub mod import;
#[path = "../src/term/mod.rs"]
pub mod term;

use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering::Relaxed};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: nl FILE [THREADS] [--declaration NAME] [--limit N] [--import-only]");
    let mut threads = 1usize;
    let mut selected = None;
    let mut limit = usize::MAX;
    let mut import_only = false;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--declaration" => selected = Some(args.next().expect("missing declaration name")),
            "--limit" => {
                limit = args
                    .next()
                    .expect("missing limit")
                    .parse()
                    .expect("invalid limit")
            }
            "--import-only" => import_only = true,
            _ => threads = arg.parse().expect("invalid thread count or option"),
        }
    }
    assert!(
        (1..=64).contains(&threads),
        "thread count must be between 1 and 64"
    );
    let t = std::time::Instant::now();
    let arena = bumpalo::Bump::new();
    let store = match import::import(&arena, &path) {
        Ok(store) => store,
        Err(e) => {
            println!("{e}");
            std::process::exit(2);
        }
    };
    let s = store.stats;
    eprintln!(
        "import {:.2?} arena {} MiB, {} decls {} exprs {} names {} levels",
        t.elapsed(),
        arena.allocated_bytes() >> 20,
        s.declarations,
        s.expressions,
        s.names,
        s.levels
    );
    if import_only {
        return;
    }
    let indices: Vec<_> = store
        .declars
        .iter()
        .enumerate()
        .filter(|(_, d)| {
            selected
                .as_ref()
                .is_none_or(|name| d.name().to_string() == *name)
        })
        .take(limit)
        .map(|(i, _)| i as u32)
        .collect();
    if selected.is_some() && indices.is_empty() {
        eprintln!("requested declaration not found");
        std::process::exit(2);
    }
    term::outcome::install_hook();
    let t = std::time::Instant::now();
    let next = AtomicU32::new(0);
    let fails = AtomicUsize::new(0);
    let n = indices.len() as u32;
    let exit = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..threads {
            std::thread::Builder::new()
                .stack_size(64 << 20)
                .spawn_scoped(sc, || {
                    let mut local = bumpalo::Bump::new();
                    loop {
                        let job = next.fetch_add(1, Relaxed);
                        if job >= n {
                            break;
                        }
                        let idx = indices[job as usize];
                        let r = term::outcome::run(|| checker::Tc::new(&store, &local).check(idx));
                        local.reset();
                        if let Err(f) = r {
                            exit.fetch_max(f.exit_code() as usize, Relaxed);
                            let k = fails.fetch_add(1, Relaxed);
                            if k < 30 {
                                println!(
                                    "{} {}: {}",
                                    store.declars[idx as usize].name().as_ref(),
                                    f.status(),
                                    f.reason()
                                );
                            }
                        }
                    }
                })
                .unwrap();
        }
    });
    eprintln!(
        "experimental signature/body checks {:.2?}: {} attempted, {} failures; inductive validation incomplete",
        t.elapsed(),
        n,
        fails.load(Relaxed)
    );
    if exit.load(Relaxed) != 0 {
        std::process::exit(exit.load(Relaxed) as i32);
    }
}
