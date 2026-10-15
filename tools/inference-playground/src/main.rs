use std::{
    fs::File,
    io::{self, IsTerminal},
    process::ExitCode,
};

const HELP: &str = "Usage: yu-playground [--intrusion] [--scoped-experiment] [--run DEFINITION [--steps N]] [SOURCE.yu | -]\nWith no argument, reads piped stdin; terminal stdin shows this help.\nRuns the existing experimental solver and prints finite graph references and retained constraints.\n--intrusion also prints retained source SCC associations, extrusion pairs, settlement state and symbolic directional introductions (not event consumption or runtime hygiene).\n--run executes module computation roots, then prints the selected definition using the provisional source machine. Handler evidence and some source forms remain unavailable.\n--steps limits execution transitions (default 100000); exhaustion withholds the result.\nInput cap: 65536 bytes. Output caps: 1048576 bytes and 16384 observation work entries total; 4096 nodes/rows/bounds per graph.\nThese are tool caps, not source typing rejections or solver CPU limits.";

fn run() -> Result<(), String> {
    let mut path = None;
    let mut intrusion = false;
    let mut scoped = false;
    let mut definition = None;
    let mut steps = None;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                println!("{HELP}");
                return Ok(());
            }
            "--intrusion" if !intrusion => intrusion = true,
            "--scoped-experiment" if !scoped => scoped = true,
            "--run" if definition.is_none() => {
                definition = Some(
                    args.next()
                        .filter(|value| !value.starts_with('-'))
                        .ok_or_else(|| format!("--run requires a definition name\n{HELP}"))?,
                );
            }
            "--steps" if steps.is_none() => {
                let value = args
                    .next()
                    .ok_or_else(|| format!("--steps requires a positive integer\n{HELP}"))?;
                steps = Some(
                    value
                        .parse::<usize>()
                        .ok()
                        .filter(|value| *value > 0)
                        .ok_or_else(|| format!("--steps requires a positive integer\n{HELP}"))?,
                );
            }
            "-" => {
                if path.replace(arg).is_some() {
                    return Err(HELP.to_owned());
                }
            }
            value if value.starts_with('-') => {
                return Err(format!("unknown or repeated option: {value}\n{HELP}"));
            }
            _ => {
                if path.replace(arg).is_some() {
                    return Err(HELP.to_owned());
                }
            }
        }
    }
    if (steps.is_some() && definition.is_none()) || (intrusion && definition.is_some()) {
        return Err(format!(
            "--steps requires --run; --intrusion is an inference observation option\n{HELP}"
        ));
    }
    let stdin = io::stdin();
    if path.is_none() && stdin.is_terminal() {
        println!("{HELP}");
        return Ok(());
    }
    let source = match path.as_deref() {
        None | Some("-") => yu_playground::read_source(stdin.lock())?,
        Some(path) => yu_playground::read_source(
            File::open(path).map_err(|error| format!("cannot open {path}: {error}"))?,
        )?,
    };
    let name = path.as_deref().unwrap_or("stdin.yu");
    let output = if let Some(definition) = definition {
        yu_playground::execute(&source, name, &definition, steps.unwrap_or(100_000), scoped)?
    } else {
        yu_playground::infer_with_scoped_experiment(&source, name, intrusion, scoped)?
    };
    print!("{output}");
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
