mod parallel;

use clap::{ArgGroup, Parser};
use nano_lean::{
    Environment, emit,
    export::{ExportError, Report, check_export, check_export_file, check_export_file_shard},
    parser,
};
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
        print_report(
            parallel::run(cli.file.as_deref().unwrap(), jobs, cli.memory_mib)
                .unwrap_or_else(|reason| Report::Rejected { reason }),
        )
    } else if let Some(shard) = cli.export_shard {
        print_report(
            number(&shard[1], "shard index")
                .and_then(|index| Ok((index, number(&shard[2], "worker count")?)))
                .map_err(ExportError::Invalid)
                .and_then(|(index, jobs)| check_export_file_shard(&shard[0], index, jobs))
                .map_or_else(Report::from, Report::from),
        )
    } else if let Some(path) = cli.export {
        print_report(check_export_file(&path).map_or_else(Report::from, Report::from))
    } else if let Some(path) = cli.export_stream {
        print_report(
            File::open(path)
                .map_err(ExportError::from)
                .and_then(|file| check_export(BufReader::new(file)))
                .map_or_else(Report::from, Report::from),
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

fn print_report(report: Report) -> ExitCode {
    println!("{report}");
    ExitCode::from(match report {
        Report::Checked { .. } | Report::ShardChecked(_) => 0,
        Report::Rejected { .. } => 1,
        Report::Unsupported { .. } => 2,
    })
}
