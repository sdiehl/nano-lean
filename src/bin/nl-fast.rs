//! Check Lean exports using the interned-term checker.

use indicatif::{ProgressBar, ProgressStyle};
use nano_lean::{checker, import, term};
use std::io::IsTerminal;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering::Relaxed};
use std::sync::mpsc;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Arena bytes a value-core session may accumulate before it is reset.
const SESSION_BYTES: usize = 64 << 20;

unsafe extern "C" {
    fn mi_option_set(option: i32, value: std::ffi::c_long);
    fn mi_collect(force: bool);
}

fn main() {
    const USAGE: &str = "usage: nl-fast [FILE|-] [-j THREADS] [--fallback] [--term-core] [--declaration NAME] [--only FILE] [--limit N] [--steps N] [--arena-mib N] [--import-only] [--trace]\nReads stdin when FILE is omitted or `-`.";
    let mut args = std::env::args().skip(1);
    let mut path = None;
    let mut threads = 1usize;
    let mut selected = None;
    let mut only: Option<std::collections::HashSet<String>> = None;
    let mut limit = usize::MAX;
    let mut import_only = false;
    let mut trace = false;
    let mut native_only = true;
    let mut value_core = true;
    let mut limits = checker::Limits {
        steps: 200_000_000,
        arena_bytes: 2048 << 20,
    };
    let usage = || -> ! {
        eprintln!("{USAGE}");
        std::process::exit(2)
    };
    let value = |args: &mut std::iter::Skip<std::env::Args>| args.next().unwrap_or_else(|| usage());
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-h" | "--help" => {
                println!("{USAGE}");
                return;
            }
            "-j" | "--threads" => threads = value(&mut args).parse().unwrap_or_else(|_| usage()),
            "--declaration" => selected = Some(value(&mut args)),
            "--only" => {
                let file = value(&mut args);
                let text = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                    eprintln!("{file}: {e}");
                    std::process::exit(2)
                });
                only = Some(
                    text.lines()
                        .map(str::trim)
                        .filter(|l| !l.is_empty())
                        .map(String::from)
                        .collect(),
                );
            }
            "--limit" => limit = value(&mut args).parse().unwrap_or_else(|_| usage()),
            "--import-only" => import_only = true,
            "--trace" => trace = true,
            "--fallback" => native_only = false,
            "--term-core" => value_core = false,
            "--steps" => limits.steps = value(&mut args).parse().unwrap_or_else(|_| usage()),
            "--arena-mib" => {
                limits.arena_bytes = value(&mut args)
                    .parse::<usize>()
                    .ok()
                    .and_then(|m| m.checked_mul(1 << 20))
                    .unwrap_or_else(|| usage())
            }
            "-" => path = None,
            a if a.starts_with('-') => usage(),
            _ if path.is_none() => path = Some(arg),
            _ => usage(),
        }
    }
    assert!(
        (1..=64).contains(&threads),
        "thread count must be between 1 and 64"
    );
    let t = std::time::Instant::now();
    let arena = term::arena::Arena::new();
    let imported = match &path {
        Some(p) => import::import(&arena, p),
        None => {
            use std::io::{BufRead, Read};
            let mut stdin = std::io::stdin().lock();
            if stdin.fill_buf().is_ok_and(import::blean::sniff) {
                let mut bytes = Vec::new();
                match stdin.read_to_end(&mut bytes) {
                    Ok(_) => import::import_bytes(&arena, &bytes),
                    Err(e) => Err(import::ImportError::Invalid(e.to_string())),
                }
            } else {
                import::import_reader(&arena, stdin, 0)
            }
        }
    };
    let store = match imported {
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
    // Return the import's freed buffers to the system, then keep freed pages from
    // here on: they are reused by the next declaration.
    // SAFETY: option 15 is mi_option_purge_delay; -1 disables purging.
    unsafe {
        mi_collect(true);
        mi_option_set(15, -1);
    }
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
            (selected.is_none() && only.is_none()) || {
                let name = d.name().to_string();
                selected.as_ref().is_none_or(|s| name == *s)
                    && only.as_ref().is_none_or(|set| set.contains(&name))
            }
        })
        .take(limit)
        .map(|(i, _)| i as u32)
        .collect();
    if (selected.is_some() || only.is_some()) && indices.is_empty() {
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
                        let mut session = nano_lean::value_checker::Session::new(&store);
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
                            let r = if value_core {
                                session.check(idx, limits, Some(&mut adapter), native_only)
                            } else {
                                checker::check_with_adapter(
                                    &store,
                                    session.arena_mut(),
                                    idx,
                                    limits,
                                    Some(&mut adapter),
                                    native_only,
                                )
                            };
                            if matches!(r, Ok(true)) {
                                fallbacks.fetch_add(1, Relaxed);
                                progress.set_message(tally());
                            }
                            if trace {
                                eprintln!(
                                    "end {idx} elapsed {:?} arena {} bytes",
                                    started.elapsed(),
                                    session.arena().allocated_bytes()
                                );
                            }
                            if !value_core
                                || r.is_err()
                                || session.arena().allocated_bytes() > SESSION_BYTES
                            {
                                #[cfg(feature = "vstats")]
                                nano_lean::value_checker::RESETS.fetch_add(1, Relaxed);
                                session.reset();
                            }
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
                                        );
                                        let _ = std::io::Write::flush(&mut std::io::stdout());
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
    if value_core {
        let b = &nano_lean::value_checker::BRIDGED;
        eprintln!(
            "bridged quot {} ind {} ctor {} rec {}",
            b[0].load(Relaxed),
            b[1].load(Relaxed),
            b[2].load(Relaxed),
            b[3].load(Relaxed)
        );
        #[cfg(feature = "vstats")]
        nano_lean::value_checker::report();
    }
    if exit.load(Relaxed) != 0 {
        std::process::exit(exit.load(Relaxed) as i32);
    }
}
