mod parallel;

use nano_lean::{
    Environment,
    export::{ExportError, check_export, check_export_file, check_export_file_shard},
    parser,
};
use std::{
    env, fs,
    io::{self, BufReader, Read},
    process::ExitCode,
};

fn main() -> ExitCode {
    let args: Vec<_> = env::args().skip(1).collect();
    if let [flag, jobs, path] = args.as_slice()
        && flag == "--export-parallel"
    {
        let result = jobs
            .parse::<usize>()
            .map_err(|_| "invalid worker count".to_owned())
            .and_then(|jobs| parallel::run(path, jobs, 2048));
        return print_parallel_result(result);
    }
    if let [flag, jobs, memory_flag, memory, path] = args.as_slice()
        && flag == "--export-parallel"
        && memory_flag == "--memory-mib"
    {
        let result = (|| {
            let jobs = jobs
                .parse::<usize>()
                .map_err(|_| "invalid worker count".to_owned())?;
            let memory = memory
                .parse::<usize>()
                .map_err(|_| "invalid memory budget".to_owned())?;
            parallel::run(path, jobs, memory)
        })();
        return print_parallel_result(result);
    }
    if let [flag, path, index, jobs] = args.as_slice()
        && flag == "--export-shard"
    {
        let result = (|| {
            let index = index
                .parse::<usize>()
                .map_err(|_| "invalid shard index".to_owned())?;
            let jobs = jobs
                .parse::<usize>()
                .map_err(|_| "invalid worker count".to_owned())?;
            check_export_file_shard(path, index, jobs)
                .map(|r| r.json())
                .map_err(|e| e.to_string())
        })();
        return print_parallel_result(result);
    }
    if let [flag, path] = args.as_slice()
        && (flag == "--export" || flag == "--export-stream")
    {
        let result = if flag == "--export-stream" {
            match fs::File::open(path) {
                Ok(file) => check_export(BufReader::new(file)),
                Err(e) => Err(ExportError::Invalid(e.to_string())),
            }
        } else {
            check_export_file(path)
        };
        return match result {
            Ok(report) => {
                println!("{}", report.json());
                ExitCode::SUCCESS
            }
            Err(e) => {
                let unsupported = matches!(e, ExportError::Unsupported(_));
                println!(
                    "{}",
                    serde_json::json!({"status":if unsupported { "unsupported" } else { "rejected" },"reason":e.to_string()})
                );
                ExitCode::from(if unsupported { 2 } else { 1 })
            }
        };
    }
    if let [flag, path] = args.as_slice()
        && flag == "--emit"
    {
        let result = read_source(path)
            .and_then(|source| Ok(parser::declarations(&source)?))
            .and_then(|ds| Ok(nano_lean::emit::ndjson(&ds)?));
        return match result {
            Ok(ndjson) => {
                print!("{ndjson}");
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("error: {e}");
                ExitCode::FAILURE
            }
        };
    }
    if args == ["--help"] || args == ["-h"] {
        println!(
            "Usage: nl-ref [FILE|-]\n       nl-ref --export FILE.ndjson\n       nl-ref --export-stream FILE.ndjson\n       nl-ref --export-parallel JOBS [--memory-mib MIB] FILE.ndjson\n       nl-ref --emit FILE.ltc\nCheck a core-language script or a Lean export, or write a script's declarations as an export.\nCommands: axiom, def, theorem, inductive, init_quot, infer, check, eval, equal. See examples/core.ltc."
        );
        return ExitCode::SUCCESS;
    }
    let result = (|| -> Result<(), Box<dyn std::error::Error>> {
        let source = match args.as_slice() {
            [] => read_source("-")?,
            [path] => read_source(path)?,
            _ => return Err("usage: nl-ref [FILE|-]".into()),
        };
        for line in parser::run(&source, &mut Environment::new())? {
            println!("{line}");
        }
        Ok(())
    })();
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn read_source(path: &str) -> Result<String, Box<dyn std::error::Error>> {
    if path == "-" {
        let mut source = String::new();
        io::stdin().read_to_string(&mut source)?;
        Ok(source)
    } else {
        Ok(fs::read_to_string(path)?)
    }
}

fn print_parallel_result(result: Result<serde_json::Value, String>) -> ExitCode {
    match result {
        Ok(report) => {
            println!("{report}");
            ExitCode::SUCCESS
        }
        Err(reason) => {
            println!(
                "{}",
                serde_json::json!({"status":"rejected", "reason":reason})
            );
            ExitCode::FAILURE
        }
    }
}
