mod parallel;

use clap::{ArgGroup, Parser};
use nano_lean::{
    Environment, emit,
    export::{ExportError, ExportReport, check_export, check_export_file, check_export_file_shard},
    parser,
};
use serde_json::{Value, json};
use std::{
    error::Error,
    fs::{self, File},
    io::{self, BufReader, Read},
    process::ExitCode,
};

const STDIN: &str = "-";

#[derive(Parser)]
#[command(
    name = "nl-ref",
    about = "Check a core-language script or a Lean export, or write a script's declarations as an export.",
    after_help = "Commands: axiom, def, theorem, inductive, init_quot, infer, check, eval, equal. See examples/core.ltc."
)]
#[command(group(ArgGroup::new("mode").args(["export", "export_stream", "export_parallel", "export_shard", "emit"])))]
struct Cli {
    /// Check a Lean export
    #[arg(long, value_name = "FILE.ndjson")]
    export: Option<String>,
    /// Check a Lean export read as a stream
    #[arg(long, value_name = "FILE.ndjson")]
    export_stream: Option<String>,
    /// Check FILE across JOBS worker processes
    #[arg(long, value_name = "JOBS", requires = "file")]
    export_parallel: Option<usize>,
    /// Memory budget for parallel workers
    #[arg(
        long,
        value_name = "MIB",
        default_value_t = 2048,
        requires = "export_parallel"
    )]
    memory_mib: usize,
    #[arg(long, hide = true, num_args = 3, value_names = ["FILE", "INDEX", "JOBS"])]
    export_shard: Option<Vec<String>>,
    /// Write a script's declarations as an export
    #[arg(long, value_name = "FILE.ltc")]
    emit: Option<String>,
    /// Core-language script, or `-` for stdin
    #[arg(conflicts_with_all = ["export", "export_stream", "export_shard", "emit"])]
    file: Option<String>,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    if let Some(jobs) = cli.export_parallel {
        report(parallel::run(
            cli.file.as_deref().unwrap(),
            jobs,
            cli.memory_mib,
        ))
    } else if let Some(shard) = cli.export_shard {
        report((|| {
            let index = number(&shard[1], "shard index")?;
            check_export_file_shard(&shard[0], index, number(&shard[2], "worker count")?)
                .map(|r| r.json())
                .map_err(|e| e.to_string())
        })())
    } else if let Some(path) = cli.export {
        verdict(check_export_file(&path))
    } else if let Some(path) = cli.export_stream {
        verdict(
            File::open(path)
                .map_err(|e| ExportError::Invalid(e.to_string()))
                .and_then(|file| check_export(BufReader::new(file))),
        )
    } else if let Some(path) = cli.emit {
        finish(
            read_source(&path)
                .and_then(|source| Ok(parser::declarations(&source)?))
                .and_then(|ds| Ok(emit::ndjson(&ds)?))
                .map(|ndjson| print!("{ndjson}")),
        )
    } else {
        finish(script(cli.file.as_deref().unwrap_or(STDIN)))
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
