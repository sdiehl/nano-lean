use clap::Parser;
use nano_lean::checker::Limits;
use nano_lean::mutate::{self, Expect, Operator, Rng};
use std::{
    collections::BTreeMap,
    fs,
    path::PathBuf,
    process::ExitCode,
    time::{Duration, Instant},
};

/// Apply single edits to a valid export and report mutants where the reference
/// kernel, the fast checker and the value core disagree, accept an invalid
/// export, or change verdict under a performance-only edit.
#[derive(Parser)]
#[command(name = "nl-mutate", after_help = AFTER_HELP)]
struct Options {
    #[arg(long, default_value_t = 0)]
    seed: u64,
    /// Mutants tried per operator
    #[arg(long, default_value_t = 50)]
    per_op: usize,
    /// Run a single operator
    #[arg(long, value_name = "NAME")]
    op: Option<Operator>,
    /// Shrink each finding and write it here as a standalone export
    #[arg(long, value_name = "DIR")]
    out: Option<PathBuf>,
    #[arg(value_name = "FILE.ndjson")]
    path: PathBuf,
}

const AFTER_HELP: &str =
    "The summary counts verdict signatures per operator: one letter per checker
(reference, fast, value) for Accepted, Rejected, Unsupported or Internal.";

fn main() -> ExitCode {
    let o = Options::parse();
    let ops = o.op.map_or_else(|| Operator::ALL.to_vec(), |op| vec![op]);
    let lines = match fs::read_to_string(&o.path)
        .map_err(|e| e.to_string())
        .and_then(|s| mutate::parse(&s).map_err(|e| e.to_string()))
    {
        Ok(lines) => lines,
        Err(e) => {
            eprintln!("{}: {e}", o.path.display());
            return ExitCode::FAILURE;
        }
    };
    let limits = Limits::default();
    let started = Instant::now();
    let baseline = mutate::check(&lines, limits);
    let budget = started.elapsed() * 10 + Duration::from_secs(1);
    if !baseline.agree() {
        eprint!("baseline disagrees\n{baseline}");
        return ExitCode::FAILURE;
    }
    let stem = o
        .path
        .file_stem()
        .map_or_else(|| "export".into(), |s| s.to_string_lossy().into_owned());
    let mut rng = Rng::new(o.seed);
    let (mut tried, mut findings) = (0, 0);
    let mut tally: BTreeMap<(&str, String), usize> = BTreeMap::new();
    for &op in &ops {
        let mut candidates = mutate::mutants(&lines, op);
        while candidates.len() > o.per_op {
            candidates.swap_remove(rng.below(candidates.len()));
        }
        for m in candidates {
            tried += 1;
            let mutant = m.apply(&lines);
            let started = Instant::now();
            let verdicts = mutate::check(&mutant, limits);
            *tally
                .entry((op.name(), mutate::signature(&verdicts)))
                .or_default() += 1;
            let slow = m.expect == Expect::Same && started.elapsed() > budget;
            let Some(why) = mutate::finding(m.expect, &baseline, &verdicts)
                .or(slow.then_some("performance edit exceeded time budget"))
            else {
                continue;
            };
            findings += 1;
            println!("{op}: {why} ({})\n{verdicts}", m.site());
            if let Some(dir) = &o.out {
                let wanted = mutate::signature(&verdicts);
                let small = mutate::shrink(mutant, m.pin(), |c| {
                    let v = mutate::check(c, limits);
                    mutate::finding(m.expect, &baseline, &v).is_some()
                        && mutate::signature(&v) == wanted
                });
                let file = dir.join(format!("{stem}-{op}-{findings}.ndjson"));
                if let Err(e) =
                    fs::create_dir_all(dir).and_then(|()| fs::write(&file, mutate::render(&small)))
                {
                    eprintln!("{}: {e}", file.display());
                    return ExitCode::FAILURE;
                }
                println!("shrunk to {} lines: {}\n", small.len(), file.display());
            }
        }
    }
    for ((op, signature), n) in tally {
        println!("{op:>16} {signature} {n}");
    }
    println!("{tried} mutants, {findings} findings");
    ExitCode::from(u8::from(findings > 0))
}
