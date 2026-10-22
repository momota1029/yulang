use std::{
    fs::File,
    io::{self, IsTerminal},
    path::{Component, Path},
    process::ExitCode,
};

const HELP: &str = "Usage: yu-playground [--intrusion] [--scoped-experiment] [--run DEFINITION | --run-module] [--steps N] [SOURCE.yu | -]\nWith no argument, reads piped stdin; terminal stdin shows this help.\nRuns the existing experimental solver and prints finite graph references and retained constraints.\n--intrusion also prints retained source SCC associations, extrusion pairs, settlement state and symbolic directional introductions (not event consumption or runtime hygiene).\n--run executes module computation roots, then prints the selected definition using the provisional source machine.\n--run-module executes the complete source-ordered module schedule without selecting a definition and prints captured host writes.\n--steps limits runtime transitions (default 100000); exhaustion withholds the result.\nInput cap: 65536 bytes. Output caps: 1048576 bytes and 16384 observation work entries total; 4096 nodes/rows/bounds per graph.\nThese are tool caps, not source typing rejections or solver CPU limits.";

fn run() -> Result<(), String> {
    let mut path = None;
    let mut intrusion = false;
    let mut scoped = false;
    let mut definition = None;
    let mut run_module = false;
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
            "--run-module" if !run_module => run_module = true,
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
    if (definition.is_some() && run_module)
        || (steps.is_some() && definition.is_none() && !run_module)
        || (intrusion && (definition.is_some() || run_module))
    {
        return Err(format!(
            "--steps requires a run mode; --intrusion is an inference observation option\n{HELP}"
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
    let name = match path.as_deref() {
        None | Some("-") => "stdin.yu".to_owned(),
        Some(path) => source_identity_name(path)?,
    };
    let output = if let Some(definition) = definition {
        yu_playground::execute(&source, &name, &definition, steps.unwrap_or(100_000), scoped)?
    } else if run_module {
        yu_playground::execute_module(&source, &name, steps.unwrap_or(100_000), scoped)?
    } else {
        yu_playground::infer_with_scoped_experiment(&source, &name, intrusion, scoped)?
    };
    print!("{output}");
    Ok(())
}

fn source_identity_name(path: &str) -> Result<String, String> {
    let absolute = Path::new(path).canonicalize()
        .map_err(|error| format!("cannot normalize source path {path}: {error}"))?;
    let mut roots = Vec::new();
    if let Ok(root) = std::env::current_dir().and_then(|root| root.canonicalize()) {
        roots.push(root);
    }
    if let Ok(root) = Path::new(env!("CARGO_MANIFEST_DIR")).canonicalize() {
        if !roots.contains(&root) { roots.push(root); }
    }
    for root in roots {
        if let Ok(relative) = absolute.strip_prefix(root) {
            return Ok(normalize_components(relative)?);
        }
    }
    let external = absolute.strip_prefix(Path::new("/")).unwrap_or(&absolute);
    Ok(format!("external/{}", normalize_components(external)?))
}

fn normalize_components(path: &Path) -> Result<String, String> {
    let mut parts = Vec::new();
    for component in path.components() {
        match component {
            Component::Normal(part) => parts.push(part.to_string_lossy().into_owned()),
            Component::CurDir => {}
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => {
                return Err(format!("source identity path is not normalized: {}", path.display()));
            }
        }
    }
    if parts.is_empty() {
        return Err("source identity path is empty".to_owned());
    }
    Ok(parts.join("/"))
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
