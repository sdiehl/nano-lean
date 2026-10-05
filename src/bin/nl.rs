//! Check Lean exports using the interned-term checker.

use indicatif::{ProgressBar, ProgressStyle};
use nano_lean::{checker, import, term};
use std::io::IsTerminal;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering::Relaxed};
use std::sync::mpsc;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args.next().expect(
        "usage: nl FILE [THREADS] [--declaration NAME] [--limit N] [--import-only] [--trace] [--steps N] [--arena-mib N] [--native-only]",
    );
    let mut threads = 1usize;
    let mut selected = None;
    let mut limit = usize::MAX;
    let mut import_only = false;
    let mut trace = false;
    let mut native_only = false;
    let mut limits = checker::Limits::default();
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
            "--trace" => trace = true,
            "--native-only" => native_only = true,
            "--steps" => {
                limits.steps = args
                    .next()
                    .expect("missing steps")
                    .parse()
                    .expect("invalid steps")
            }
            "--arena-mib" => {
                limits.arena_bytes = args
                    .next()
                    .expect("missing arena limit")
                    .parse::<usize>()
                    .expect("invalid arena limit")
                    .checked_mul(1 << 20)
                    .expect("arena limit overflow")
            }
            _ => threads = arg.parse().expect("invalid thread count or option"),
        }
    }
    assert!(
        (1..=64).contains(&threads),
        "thread count must be between 1 and 64"
    );
    let t = std::time::Instant::now();
    let arena = term::arena::Arena::new();
    let store = match import::import(&arena, &path) {
        Ok(store) => store,
        Err(e) => {
            println!("{e}");
            let code = match e {
                import::ImportError::Invalid(_) => 1,
                import::ImportError::Unsupported(_) => 2,
            };
            std::process::exit(code);
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
    let fallbacks = AtomicUsize::new(0);
    let n = indices.len() as u32;
    let exit = AtomicUsize::new(0);
    let progress = if trace {
        ProgressBar::hidden()
    } else {
        ProgressBar::new(u64::from(n))
    };
    progress.set_style(ProgressStyle::with_template(
        "{spinner:.green} [{elapsed_precise}] {wide_bar:.cyan/blue} {pos}/{len} {per_sec} ETA {eta_precise} {msg}"
    ).expect("valid progress template"));
    let tally = || {
        format!(
            "{} fail, {} fallback",
            fails.load(Relaxed),
            fallbacks.load(Relaxed)
        )
    };
    progress.set_message(tally());
    progress.enable_steady_tick(std::time::Duration::from_millis(250));
    let (stop, stopped) = mpsc::channel::<()>();
    std::thread::scope(|sc| {
        // Stop the reporter even if joining a worker unwinds.
        let stop = stop;
        if !trace && !std::io::stderr().is_terminal() {
            let (progress, tally) = (&progress, &tally);
            sc.spawn(move || {
                while let Err(mpsc::RecvTimeoutError::Timeout) =
                    stopped.recv_timeout(std::time::Duration::from_secs(10))
                {
                    let eta = progress.eta().as_secs();
                    eprintln!(
                        "[progress] {}/{n} checked; {:.0}/s; estimated remaining {}m {}s; {}",
                        progress.position(),
                        progress.per_sec(),
                        eta / 60,
                        eta % 60,
                        tally()
                    );
                }
            });
        }
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                std::thread::Builder::new()
                    .stack_size(64 << 20)
                    .spawn_scoped(sc, || {
                        let mut local = term::arena::Arena::new();
                        let mut adapter = checker::Adapter::new(&store);
                        loop {
                            let job = next.fetch_add(1, Relaxed);
                            if job >= n {
                                break;
                            }
                            let idx = indices[job as usize];
                            let started = std::time::Instant::now();
                            if trace {
                                eprintln!("start {idx} {}", store.declars[idx as usize].name());
                            }
                            let r = checker::check_with_adapter(
                                &store,
                                &mut local,
                                idx,
                                limits,
                                Some(&mut adapter),
                                native_only,
                            );
                            if matches!(r, Ok(true)) {
                                fallbacks.fetch_add(1, Relaxed);
                                progress.set_message(tally());
                            }
                            if trace {
                                eprintln!(
                                    "end {idx} elapsed {:?} arena {} bytes",
                                    started.elapsed(),
                                    local.allocated_bytes()
                                );
                            }
                            local.reset();
                            progress.inc(1);
                            if let Err(f) = r {
                                exit.fetch_max(f.exit_code() as usize, Relaxed);
                                let k = fails.fetch_add(1, Relaxed);
                                progress.set_message(tally());
                                if k < 30 {
                                    progress.suspend(|| {
                                        println!(
                                            "{} {}: {}",
                                            store.declars[idx as usize].name().as_ref(),
                                            f.status(),
                                            f.reason()
                                        )
                                    });
                                }
                            }
                        }
                    })
                    .unwrap()
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
        drop(stop);
    });
    progress.finish_and_clear();
    eprintln!(
        "experimental checks {:.2?}: {} attempted, {} failures, {} fallbacks",
        t.elapsed(),
        n,
        fails.load(Relaxed),
        fallbacks.load(Relaxed)
    );
    if exit.load(Relaxed) != 0 {
        std::process::exit(exit.load(Relaxed) as i32);
    }
}
