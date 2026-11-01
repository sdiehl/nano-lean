use clap::Parser;
use nano_lean::checker::Limits;
use nano_lean::mutate::{self, Expect, Operator, Rng};
use nano_lean::verdict::Verdicts;
use serde_json::Value;
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode, Stdio},
    thread,
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
    /// Also compare against an external kernel that exits 0 to accept and 1 to reject
    #[arg(long, value_name = "PROGRAM")]
    oracle: Option<PathBuf>,
    #[arg(value_name = "FILE.ndjson")]
    path: PathBuf,
}

struct Oracle {
    program: PathBuf,
    file: PathBuf,
    timeout: Duration,
}

impl Oracle {
    /// Some(true) on accept, Some(false) on reject, None on anything else.
    fn run(&self, lines: &[Value]) -> Option<bool> {
        fs::write(&self.file, mutate::render(lines)).ok()?;
        let mut child = Command::new(&self.program)
            .arg(&self.file)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .ok()?;
        let started = Instant::now();
        loop {
            if let Some(status) = child.try_wait().ok()? {
                return match status.code() {
                    Some(0) => Some(true),
                    Some(1) => Some(false),
                    _ => None,
                };
            }
            if started.elapsed() > self.timeout {
                child.kill().ok();
                child.wait().ok();
                return None;
            }
            thread::sleep(Duration::from_millis(5));
        }
    }

    /// Lean accepts unsafe definitions and recomputes inductive metadata, which nl rejects
    /// by policy, so those operators only count when Lean rejects.
    fn disagrees(&self, op: Operator, lines: &[Value], v: &Verdicts) -> bool {
        let all = v.all();
        let policy = matches!(
            op,
            Operator::Unsafe | Operator::InductiveCount | Operator::InductiveFlag
        );
        match self.run(lines) {
            Some(true) => !policy && all.iter().any(|(_, v)| v.rejected()),
            Some(false) => all.iter().any(|(_, v)| v.accepted()),
            None => false,
        }
    }
}

const LEAN_DISAGREES: &str = "the oracle disagrees";

fn judge(
    oracle: Option<&Oracle>,
    op: Operator,
    expect: Expect,
    baseline: &Verdicts,
    mutant: &[Value],
    v: &Verdicts,
) -> Option<&'static str> {
    mutate::finding(expect, baseline, v).or_else(|| {
        oracle
            .is_some_and(|o| o.disagrees(op, mutant, v))
            .then_some(LEAN_DISAGREES)
    })
}

fn oracle_for(program: Option<&Path>, lines: &[Value], timeout: Duration) -> Option<Oracle> {
    let o = Oracle {
        program: program?.to_path_buf(),
        file: std::env::temp_dir().join(format!("nl-mutate-{}.ndjson", std::process::id())),
        timeout,
    };
    if o.run(lines) == Some(true) {
        Some(o)
    } else {
        println!("the oracle does not accept the baseline, so it is not consulted");
        None
    }
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
    let oracle = oracle_for(o.oracle.as_deref(), &lines, budget * 10);
    let oracle = oracle.as_ref();
    let stem = o
        .path
        .file_stem()
        .map_or_else(|| "export".into(), |s| s.to_string_lossy().into_owned());
    let mut rng = Rng::new(o.seed);
    let (mut tried, mut findings, mut declined) = (0, 0, 0);
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
            let Some(why) = judge(oracle, op, m.expect, &baseline, &mutant, &verdicts)
                .or(slow.then_some("performance edit exceeded time budget"))
            else {
                if mutate::declined(&verdicts) {
                    declined += 1;
                    println!(
                        "{op}: declined where another accepted ({})\n{verdicts}",
                        m.site()
                    );
                }
                continue;
            };
            findings += 1;
            println!("{op}: {why} ({})\n{verdicts}", m.site());
            if let Some(dir) = &o.out {
                let wanted = mutate::signature(&verdicts);
                let valid = mutate::signature(&baseline);
                let (base, pins) = mutate::shrink(lines.clone(), m.pins(), |c, pins| {
                    let b = mutate::check(c, limits);
                    mutate::signature(&b) == valid
                        && oracle.is_none_or(|o| o.run(c) == Some(true))
                        && {
                            let small = m.at(pins).apply(c);
                            let v = mutate::check(&small, limits);
                            judge(oracle, op, m.expect, &b, &small, &v) == Some(why)
                                && mutate::signature(&v) == wanted
                        }
                });
                let small = m.at(&pins).apply(&base);
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
    if let Some(o) = oracle {
        fs::remove_file(&o.file).ok();
    }
    println!("{tried} mutants, {findings} findings, {declined} declined");
    ExitCode::from(u8::from(findings > 0))
}
