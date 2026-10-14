use std::{
    fs::File,
    io::{self, IsTerminal},
    process::ExitCode,
};

const HELP: &str = "Usage: yu-playground [--intrusion] [--scoped-experiment] [SOURCE.yu | -]\nWith no argument, reads piped stdin; terminal stdin shows this help.\nRuns the existing experimental solver and prints finite graph references and retained constraints.\n--intrusion also prints retained source SCC associations, extrusion pairs, settlement state and symbolic directional introductions (not event consumption or runtime hygiene).\nInput cap: 65536 bytes. Output caps: 1048576 bytes and 16384 observation work entries total; 4096 nodes/rows/bounds per graph.\nThese are tool caps, not source typing rejections or solver CPU limits.";

fn run() -> Result<(), String> {
    let mut path = None;
    let mut intrusion = false;
    let mut scoped = false;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--help" | "-h" => {
                println!("{HELP}");
                return Ok(());
            }
            "--intrusion" if !intrusion => intrusion = true,
            "--scoped-experiment" if !scoped => scoped = true,
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
    print!(
        "{}",
        yu_playground::infer_with_scoped_experiment(
            &source,
            path.as_deref().unwrap_or("stdin.yu"),
            intrusion,
            scoped
        )?
    );
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
