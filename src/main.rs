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
    if args == ["--help"] || args == ["-h"] {
        println!(
            "Usage: nano-lean [FILE|-]\n       nano-lean --export FILE.ndjson\n       nano-lean --export-stream FILE.ndjson\n       nano-lean --export-parallel JOBS [--memory-mib MIB] FILE.ndjson\nCheck a core-language script or a Lean export.\nCommands: axiom, def, infer, check, eval, equal. See examples/core.ltc."
        );
        return ExitCode::SUCCESS;
    }
    let result = (|| -> Result<(), Box<dyn std::error::Error>> {
        let mut source = String::new();
        match args.as_slice() {
            [] => {
                io::stdin().read_to_string(&mut source)?;
            }
            [path] if path == "-" => {
                io::stdin().read_to_string(&mut source)?;
            }
            [path] => source = fs::read_to_string(path)?,
            _ => return Err("usage: nano-lean [FILE|-]".into()),
        }
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
