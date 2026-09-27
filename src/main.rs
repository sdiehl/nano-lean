use nano_lean::{Environment, parser};
use std::{
    env, fs,
    io::{self, Read},
    process::ExitCode,
};

fn main() -> ExitCode {
    let args: Vec<_> = env::args().skip(1).collect();
    if args == ["--help"] || args == ["-h"] {
        println!(
            "Usage: nano-lean [FILE|-]\nCheck a core-language script (stdin if omitted).\nCommands: axiom, def, infer, check, eval, equal. See examples/core.ltc."
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
