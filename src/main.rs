use nano_lean::{
    Environment,
    export::{ExportError, check_export_file},
    parser,
};
use std::{
    env, fs,
    io::{self, Read},
    process::ExitCode,
};

fn main() -> ExitCode {
    let args: Vec<_> = env::args().skip(1).collect();
    if let [flag, path] = args.as_slice()
        && flag == "--export"
    {
        let result = check_export_file(path);
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
            "Usage: nano-lean [FILE|-]\n       nano-lean --export FILE.ndjson\nCheck a core-language script or a Lean export.\nCommands: axiom, def, infer, check, eval, equal. See examples/core.ltc."
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
