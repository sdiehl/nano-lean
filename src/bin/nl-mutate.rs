use nano_lean::checker::Limits;
use nano_lean::mutate::{self, Expect, OPERATORS, Rng};
use std::{collections::BTreeMap, env, fs, path::PathBuf, process::ExitCode, time::Instant};

const USAGE: &str = "Usage: nl-mutate [--seed N] [--per-op N] [--op NAME] [--out DIR] FILE.ndjson
Apply single edits to a valid export and report mutants where the reference
kernel, the fast checker and the value core disagree, accept an invalid
export, or change verdict under a performance-only edit. With --out, each
finding is shrunk and written as a standalone export. The summary counts
verdict signatures per operator: one letter per checker (reference, fast,
value) for Accepted, Rejected, Unsupported or Internal.";

struct Options {
    seed: u64,
    per_op: usize,
    ops: Vec<&'static str>,
    out: Option<PathBuf>,
    path: PathBuf,
}

fn options() -> Result<Options, String> {
    let mut args = env::args().skip(1);
    let mut o = Options {
        seed: 0,
        per_op: 50,
        ops: OPERATORS.to_vec(),
        out: None,
        path: PathBuf::new(),
    };
    let mut path = None;
    while let Some(arg) = args.next() {
        let mut value = || args.next().ok_or(format!("{arg} needs a value"));
        match arg.as_str() {
            "--seed" => o.seed = value()?.parse().map_err(|_| "invalid seed")?,
            "--per-op" => o.per_op = value()?.parse().map_err(|_| "invalid count")?,
            "--op" => {
                let name = value()?;
                let op = OPERATORS.iter().find(|op| **op == name);
                o.ops = vec![*op.ok_or(format!("unknown operator {name}"))?];
            }
            "--out" => o.out = Some(value()?.into()),
            "-h" | "--help" => return Err(USAGE.into()),
            _ if path.is_none() => path = Some(arg.into()),
            _ => return Err(USAGE.into()),
        }
    }
    o.path = path.ok_or(USAGE)?;
    Ok(o)
}

fn main() -> ExitCode {
    let o = match options() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::FAILURE;
        }
    };
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
    let budget = started.elapsed() * 10 + std::time::Duration::from_secs(1);
    if !baseline.agree() {
        eprint!("baseline disagrees\n{baseline}");
        return ExitCode::FAILURE;
    }
    let stem = o.path.file_stem().unwrap().to_string_lossy().into_owned();
    let mut rng = Rng::new(o.seed);
    let (mut tried, mut findings) = (0, 0);
    let mut tally: BTreeMap<(&str, String), usize> = BTreeMap::new();
    for &op in &o.ops {
        let mut candidates = mutate::mutants(&lines, op, &mut rng);
        while candidates.len() > o.per_op {
            candidates.swap_remove(rng.below(candidates.len()));
        }
        for m in candidates {
            tried += 1;
            let mutant = m.apply(&lines);
            let started = Instant::now();
            let verdicts = mutate::check(&mutant, limits);
            *tally.entry((op, mutate::signature(&verdicts))).or_default() += 1;
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
