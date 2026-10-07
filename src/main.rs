mod parallel;

use nano_lean::{
    Environment, emit,
    export::{ExportError, ExportReport, check_export, check_export_file, check_export_file_shard},
    parser,
};
use serde_json::{Value, json};
use std::{
    env,
    error::Error,
    fs::{self, File},
    io::{self, BufReader, Read},
    process::ExitCode,
};

const USAGE: &str = "Usage: nl-ref [FILE|-]
       nl-ref --export FILE.ndjson
       nl-ref --export-stream FILE.ndjson
       nl-ref --export-parallel JOBS [--memory-mib MIB] FILE.ndjson
       nl-ref --emit FILE.ltc
Check a core-language script or a Lean export, or write a script's declarations as an export.
Commands: axiom, def, theorem, inductive, init_quot, infer, check, eval, equal. See examples/core.ltc.";
const DEFAULT_MEMORY_MIB: usize = 2048;
const STDIN: &str = "-";

fn main() -> ExitCode {
    let args: Vec<_> = env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match args.as_slice() {
        ["--export-parallel", jobs, path] => report(
            number(jobs, "worker count")
                .and_then(|jobs| parallel::run(path, jobs, DEFAULT_MEMORY_MIB)),
        ),
        ["--export-parallel", jobs, "--memory-mib", memory, path] => report((|| {
            let jobs = number(jobs, "worker count")?;
            parallel::run(path, jobs, number(memory, "memory budget")?)
        })()),
        ["--export-shard", path, index, jobs] => report((|| {
            let index = number(index, "shard index")?;
            check_export_file_shard(path, index, number(jobs, "worker count")?)
                .map(|r| r.json())
                .map_err(|e| e.to_string())
        })()),
        ["--export", path] => verdict(check_export_file(path)),
        ["--export-stream", path] => verdict(
            File::open(path)
                .map_err(|e| ExportError::Invalid(e.to_string()))
                .and_then(|file| check_export(BufReader::new(file))),
        ),
        ["--emit", path] => finish(
            read_source(path)
                .and_then(|source| Ok(parser::declarations(&source)?))
                .and_then(|ds| Ok(emit::ndjson(&ds)?))
                .map(|ndjson| print!("{ndjson}")),
        ),
        ["--help" | "-h"] => {
            println!("{USAGE}");
            ExitCode::SUCCESS
        }
        [] => finish(script(STDIN)),
        [path] => finish(script(path)),
        _ => finish(Err("usage: nl-ref [FILE|-]".into())),
    }
}

fn number(s: &str, what: &str) -> Result<usize, String> {
    s.parse().map_err(|_| format!("invalid {what}"))
}

fn read_source(path: &str) -> Result<String, Box<dyn Error>> {
    if path == STDIN {
        let mut source = String::new();
        io::stdin().read_to_string(&mut source)?;
        Ok(source)
    } else {
        Ok(fs::read_to_string(path)?)
    }
}

fn script(path: &str) -> Result<(), Box<dyn Error>> {
    for line in parser::run(&read_source(path)?, &mut Environment::new())? {
        println!("{line}");
    }
    Ok(())
}

fn finish(result: Result<(), Box<dyn Error>>) -> ExitCode {
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn verdict(result: Result<ExportReport, ExportError>) -> ExitCode {
    match result {
        Ok(report) => {
            println!("{}", report.json());
            ExitCode::SUCCESS
        }
        Err(e) => {
            let unsupported = matches!(e, ExportError::Unsupported(_));
            let status = if unsupported {
                "unsupported"
            } else {
                "rejected"
            };
            println!("{}", json!({"status": status, "reason": e.to_string()}));
            ExitCode::from(if unsupported { 2 } else { 1 })
        }
    }
}

fn report(result: Result<Value, String>) -> ExitCode {
    match result {
        Ok(report) => {
            println!("{report}");
            ExitCode::SUCCESS
        }
        Err(reason) => {
            println!("{}", json!({"status": "rejected", "reason": reason}));
            ExitCode::FAILURE
        }
    }
}
