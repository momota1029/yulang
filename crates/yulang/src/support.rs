use super::*;

pub(super) fn parse_build_args(
    program: &str,
    mut args: VecDeque<OsString>,
) -> (PathBuf, Option<PathBuf>) {
    let mut path = None;
    let mut out = None;
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--out") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "build --out requires a path");
                };
                set_single_output_path(program, &mut out, value);
            }
            Some(value) if value.starts_with("--out=") => {
                let value = value.strip_prefix("--out=").unwrap_or_default();
                if value.is_empty() {
                    print_usage_error_and_exit(program, "build --out requires a path");
                }
                set_single_output_path(program, &mut out, OsString::from(value));
            }
            Some(flag) if flag.starts_with("--") => {
                print_usage_error_and_exit(program, &format!("unsupported build option {flag}"));
            }
            _ => set_single_path(program, &mut path, arg),
        }
    }
    let Some(path) = path else {
        print_usage_and_exit(program);
    };
    (path, out)
}

pub(super) fn parse_run_args(
    program: &str,
    mut args: VecDeque<OsString>,
) -> (PathBuf, RunSelection) {
    let mut path = None;
    let mut selection = RunSelection::default();
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--print-roots") => {
                selection.print_roots = true;
            }
            Some("--interpreter") => {
                selection.interpreter = true;
            }
            Some(flag) if flag.starts_with("--") => {
                print_usage_error_and_exit(program, &format!("unsupported run option {flag}"));
            }
            _ => set_single_path(program, &mut path, arg),
        }
    }
    let Some(path) = path else {
        print_usage_and_exit(program);
    };
    (path, selection)
}

pub(super) fn parse_parse_args(
    program: &str,
    mut args: VecDeque<OsString>,
) -> (Option<PathBuf>, parse_view::ParserMode) {
    let mut path = None;
    let mut mode = None;
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--as") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "parse --as requires a mode");
                };
                let Some(value) = value.to_str() else {
                    print_usage_error_and_exit(program, "parse mode must be UTF-8");
                };
                mode = parse_parser_mode_or_exit(program, value);
            }
            Some(value) if value.starts_with("--as=") => {
                let value = value.strip_prefix("--as=").unwrap_or_default();
                mode = parse_parser_mode_or_exit(program, value);
            }
            Some(flag) if flag.starts_with("--") => {
                print_usage_error_and_exit(program, &format!("unsupported parse option {flag}"));
            }
            _ => set_single_path(program, &mut path, arg),
        }
    }
    let Some(mode) = mode else {
        print_usage_error_and_exit(program, "parse requires --as <expr|pat|stmt|type|mark>");
    };
    (path, mode)
}

pub(super) fn parse_parser_mode_or_exit(
    program: &str,
    value: &str,
) -> Option<parse_view::ParserMode> {
    let Some(mode) = parse_view::parse_mode(value) else {
        print_usage_error_and_exit(
            program,
            &format!("unknown parse mode {value:?}; expected expr, pat, stmt, type, or mark"),
        );
    };
    Some(mode)
}

pub(super) fn parse_dump_args(
    program: &str,
    mut args: VecDeque<OsString>,
) -> (PathBuf, DumpSelection) {
    let mut path = None;
    let mut selection = DumpSelection::default();
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--core-ir") | Some("--poly") => {
                selection.poly = true;
            }
            Some("--poly-raw") => {
                selection.poly_raw = true;
            }
            Some("--runtime-finalize-ir")
            | Some("--finalized-ir")
            | Some("--runtime-ir")
            | Some("--mono") => {
                selection.mono = true;
            }
            Some("--hygiene-ir") => {
                print_usage_error_and_exit(
                    program,
                    "dump --hygiene-ir is not supported by yulang yet",
                );
            }
            Some("--verbose-ir") => {}
            Some(flag) if flag.starts_with("--") => {
                print_usage_error_and_exit(program, &format!("unsupported dump option {flag}"));
            }
            _ => set_single_path(program, &mut path, arg),
        }
    }
    if !selection.poly && !selection.poly_raw && !selection.mono {
        print_usage_error_and_exit(
            program,
            "dump requires at least one of --core-ir, --runtime-ir, --poly, --poly-raw, --mono",
        );
    }
    let Some(path) = path else {
        print_usage_and_exit(program);
    };
    (path, selection)
}

pub(super) fn print_selected_dump_without_std(path: PathBuf, selection: DumpSelection) {
    if selection.poly {
        run_route(
            yulang::dump_poly_from_entry(path.clone()),
            print_dump_poly_output,
        );
    }
    if selection.poly_raw {
        run_route(
            yulang::dump_poly_raw_from_entry(path.clone()),
            print_dump_poly_output,
        );
    }
    if selection.mono {
        run_route(yulang::dump_mono_from_entry(path), print_dump_mono_output);
    }
}

pub(super) fn print_selected_dump_with_std(
    path: PathBuf,
    selection: DumpSelection,
    options: &yulang::StdSourceOptions,
    use_cache: bool,
) {
    let files = run_route_to_value(yulang::collect_local_sources_with_std_options(
        path, options,
    ));
    if selection.poly {
        let output = dump_poly_with_optional_cache(files.clone(), false, use_cache);
        print_dump_poly_output(&output);
    }
    if selection.poly_raw {
        let output = dump_poly_with_optional_cache(files.clone(), true, use_cache);
        print_dump_poly_output(&output);
    }
    if selection.mono {
        let output = dump_mono_with_optional_cache(files, use_cache);
        print_dump_mono_output(&output);
    }
}

pub(super) fn require_one_path(program: &str, mut args: VecDeque<OsString>) -> PathBuf {
    let Some(path) = args.pop_front() else {
        print_usage_and_exit(program);
    };
    if args.pop_front().is_some() {
        print_usage_and_exit(program);
    }
    PathBuf::from(path)
}

pub(super) fn require_path_and_module(
    program: &str,
    mut args: VecDeque<OsString>,
) -> (PathBuf, String) {
    let Some(path) = args.pop_front() else {
        print_usage_and_exit(program);
    };
    let Some(module) = args.pop_front() else {
        print_usage_and_exit(program);
    };
    if args.pop_front().is_some() {
        print_usage_and_exit(program);
    }
    let Some(module) = module.to_str() else {
        print_usage_error_and_exit(program, "module path must be UTF-8");
    };
    (PathBuf::from(path), module.to_string())
}

pub(super) fn set_single_path(program: &str, path: &mut Option<PathBuf>, value: OsString) {
    if path.is_some() {
        print_usage_and_exit(program);
    }
    *path = Some(PathBuf::from(value));
}

pub(super) fn set_single_output_path(program: &str, out: &mut Option<PathBuf>, value: OsString) {
    if out.is_some() {
        print_usage_and_exit(program);
    }
    *out = Some(PathBuf::from(value));
}

pub(super) fn read_source_or_exit(path: Option<&PathBuf>) -> String {
    match path {
        Some(path) => fs::read_to_string(path).unwrap_or_else(|error| {
            eprintln!("failed to read {}: {error}", path.display());
            process::exit(1);
        }),
        None => {
            let mut source = String::new();
            if let Err(error) = io::stdin().read_to_string(&mut source) {
                eprintln!("failed to read stdin: {error}");
                process::exit(1);
            }
            source
        }
    }
}

pub(super) fn print_cst_if_requested(options: &GlobalOptions, path: &PathBuf) {
    if !options.show_cst {
        return;
    }
    let source = read_source_or_exit(Some(path));
    print!("{}", cst_view::format_module_cst(&source));
}

pub(super) fn read_control_artifact_or_exit(path: &PathBuf) -> Option<control_vm::Program> {
    let source = match fs::read_to_string(path) {
        Ok(source) => source,
        Err(_) => return None,
    };
    match yulang::artifact::decode_control_program(&source) {
        Ok(program) => program,
        Err(error) => {
            eprintln!(
                "failed to read control-vm artifact {}: {error}",
                path.display()
            );
            process::exit(1);
        }
    }
}

pub(super) fn run_control_artifact(program: control_vm::Program, print_roots: bool) {
    let values = match control_vm::run_program(&program) {
        Ok(values) => values,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    if print_roots {
        println!("run roots {}", control_vm::format_values(&values));
    }
}

pub(super) fn default_artifact_path(entry: &PathBuf) -> PathBuf {
    let stem = entry
        .file_stem()
        .and_then(|stem| stem.to_str())
        .filter(|stem| !stem.is_empty())
        .unwrap_or("main");
    PathBuf::from("target")
        .join("yulang")
        .join("yuir")
        .join(format!("{stem}.yuir"))
}

pub(super) fn ensure_parent_dir_or_exit(path: &PathBuf, label: &str) {
    let Some(parent) = path.parent() else {
        return;
    };
    if parent.as_os_str().is_empty() {
        return;
    }
    if let Err(error) = fs::create_dir_all(parent) {
        eprintln!(
            "failed to create {label} parent {}: {error}",
            parent.display()
        );
        process::exit(1);
    }
}

pub(super) fn run_route<T>(result: Result<T, yulang::RouteError>, print: impl FnOnce(&T)) {
    match result {
        Ok(output) => print(&output),
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    }
}

pub(super) fn run_route_to_value<T>(result: Result<T, yulang::RouteError>) -> T {
    match result {
        Ok(output) => output,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    }
}

pub(super) fn print_dump_poly_output(output: &yulang::DumpPolyOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

pub(super) fn print_dump_mono_output(output: &yulang::DumpMonoOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

pub(super) fn print_run_mono_output(output: &yulang::RunMonoOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

pub(super) fn print_run_control_output(output: &yulang::RunControlOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

pub(super) fn run_mono_printer(print_roots: bool) -> impl FnOnce(&yulang::RunMonoOutput) {
    move |output| {
        if print_roots {
            print!("{}", output.text);
        }
        for error in &output.errors {
            eprintln!("error: {error}");
        }
    }
}

pub(super) fn run_control_printer(print_roots: bool) -> impl FnOnce(&yulang::RunControlOutput) {
    move |output| {
        if print_roots {
            print!("{}", output.text);
        }
        for error in &output.errors {
            eprintln!("error: {error}");
        }
    }
}

pub(super) fn print_check_poly_output(output: &yulang::CheckPolyOutput) {
    print!("{}", output.text);
}

pub(super) fn print_usage_error_and_exit(program: &str, error: &str) -> ! {
    eprintln!("{error}");
    print_usage_and_exit(program);
}

pub(super) fn print_usage_and_exit(program: &str) -> ! {
    eprintln!(
        "usage: {program} [--std-root <path>] [--no-prelude] [--cst] [--no-cache] check <path>"
    );
    eprintln!(
        "       {program} [--std-root <path>] [--no-prelude] [--no-cache] build [--out <path>] <path>"
    );
    eprintln!(
        "       {program} [--std-root <path>] [--no-prelude] [--no-cache] run [--interpreter] [--print-roots] <path>"
    );
    eprintln!(
        "       {program} [--std-root <path>] [--no-prelude] dump <path> (--core-ir | --runtime-ir | --poly | --poly-raw | --mono)"
    );
    eprintln!("       {program} parse [path] --as <expr|pat|stmt|type|mark>");
    eprintln!("       {program} [--std-root <path>] install std");
    eprintln!("       {program} cache <clear|path>");
    eprintln!("       {program} realm freeze [path] --version <version>");
    eprintln!("       {program} [--std-root <path>] server");
    eprintln!("       {program} debug <control-vm|control-vm-emit|control-vm-load> ...");
    eprintln!("       {program} dump-poly <path>");
    eprintln!("       {program} dump-poly-raw <path>");
    eprintln!("       {program} dump-mono <path>");
    eprintln!("       {program} run-mono <path>");
    eprintln!("       {program} run-control <path>");
    eprintln!("       {program} [--std-root <path>] dump-poly-std <path>");
    eprintln!("       {program} [--std-root <path>] dump-mono-std <path>");
    eprintln!("       {program} [--std-root <path>] run-mono-std <path>");
    eprintln!("       {program} [--std-root <path>] run-control-std <path>");
    eprintln!("       {program} [--std-root <path>] check-poly-std <path>");
    eprintln!("       {program} [--std-root <path>] check-poly-std-in <path> <module>");
    eprintln!("       {program} [--std-root <path>] dump-poly-std-in <path> <module>");
    eprintln!("       {program} [--std-root <path>] dump-poly-std-raw <path>");
    eprintln!("       {program} [--std-root <path>] dump-poly-std-in-raw <path> <module>");
    process::exit(2);
}
