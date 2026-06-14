use std::collections::VecDeque;
use std::env;
use std::ffi::OsString;
use std::path::PathBuf;
use std::process;

fn main() {
    let mut raw_args = env::args_os();
    let program = raw_args
        .next()
        .map(PathBuf::from)
        .and_then(|path| path.file_name().map(|name| name.to_owned()))
        .and_then(|name| name.into_string().ok())
        .unwrap_or_else(|| "yulang2".to_string());

    let args = VecDeque::from(raw_args.collect::<Vec<_>>());
    let (options, mut args) = match parse_global_options(args) {
        Ok(parsed) => parsed,
        Err(error) => print_usage_error_and_exit(&program, &error),
    };
    let Some(command) = args.pop_front() else {
        print_usage_and_exit(&program);
    };

    match command.to_str() {
        Some("check") => run_compatible_check(&program, &options, args),
        Some("run") | Some("interpret") => run_compatible_run(&program, &options, args),
        Some("dump") => run_compatible_dump(&program, &options, args),
        Some("dump-poly") => {
            let path = require_one_path(&program, args);
            run_route(yulang2::dump_poly_from_entry(path), print_dump_poly_output);
        }
        Some("dump-poly-raw") => {
            let path = require_one_path(&program, args);
            run_route(
                yulang2::dump_poly_raw_from_entry(path),
                print_dump_poly_output,
            );
        }
        Some("dump-mono") => {
            let path = require_one_path(&program, args);
            run_route(yulang2::dump_mono_from_entry(path), print_dump_mono_output);
        }
        Some("run-mono") => {
            let path = require_one_path(&program, args);
            run_route(yulang2::run_mono_from_entry(path), print_run_mono_output);
        }
        Some("run-control") => {
            let path = require_one_path(&program, args);
            run_route(
                yulang2::run_control_from_entry(path),
                print_run_control_output,
            );
        }
        Some("dump-poly-std") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang2::dump_poly_from_entry_with_std_options(path, &source_options),
                print_dump_poly_output,
            );
        }
        Some("dump-mono-std") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang2::dump_mono_from_entry_with_std_options(path, &source_options),
                print_dump_mono_output,
            );
        }
        Some("run-mono-std") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang2::run_mono_from_entry_with_std_options(path, &source_options),
                print_run_mono_output,
            );
        }
        Some("run-control-std") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang2::run_control_from_entry_with_std_options(path, &source_options),
                print_run_control_output,
            );
        }
        Some("check-poly-std") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang2::check_poly_from_entry_with_std_options(path, &source_options),
                print_check_poly_output,
            );
        }
        Some("check-poly-std-in") => {
            let (path, module) = require_path_and_module(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang2::check_poly_from_entry_with_std_in_module_options(
                    path,
                    &module,
                    &source_options,
                ),
                print_check_poly_output,
            );
        }
        Some("dump-poly-std-in") => {
            let (path, module) = require_path_and_module(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang2::dump_poly_from_entry_with_std_in_module_options(
                    path,
                    &module,
                    &source_options,
                ),
                print_dump_poly_output,
            );
        }
        Some("dump-poly-std-raw") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang2::dump_poly_raw_from_entry_with_std_options(path, &source_options),
                print_dump_poly_output,
            );
        }
        Some("dump-poly-std-in-raw") => {
            let (path, module) = require_path_and_module(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang2::dump_poly_raw_from_entry_with_std_in_module_options(
                    path,
                    &module,
                    &source_options,
                ),
                print_dump_poly_output,
            );
        }
        _ => print_usage_and_exit(&program),
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct GlobalOptions {
    std_root: Option<PathBuf>,
    no_prelude: bool,
}

impl GlobalOptions {
    fn std_source_options(&self) -> yulang2::StdSourceOptions {
        yulang2::StdSourceOptions {
            std_root: self.std_root.clone(),
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct DumpSelection {
    poly: bool,
    poly_raw: bool,
    mono: bool,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct RunSelection {
    interpreter: bool,
    print_roots: bool,
}

fn parse_global_options(
    mut args: VecDeque<OsString>,
) -> Result<(GlobalOptions, VecDeque<OsString>), String> {
    let mut options = GlobalOptions::default();
    let mut command_args = VecDeque::new();
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--std-root") => {
                let Some(value) = args.pop_front() else {
                    return Err("--std-root requires a path".to_string());
                };
                options.std_root = Some(PathBuf::from(value));
            }
            Some(value) if value.starts_with("--std-root=") => {
                let value = value.strip_prefix("--std-root=").unwrap_or_default();
                if value.is_empty() {
                    return Err("--std-root requires a path".to_string());
                }
                options.std_root = Some(PathBuf::from(value));
            }
            Some("--no-prelude") => {
                options.no_prelude = true;
            }
            Some("--no-cache") => {}
            _ => command_args.push_back(arg),
        }
    }
    Ok((options, command_args))
}

fn run_compatible_check(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let path = require_one_path(program, args);
    if options.no_prelude {
        run_route(
            yulang2::check_poly_from_entry(path),
            print_check_poly_output,
        );
        return;
    }

    let source_options = options.std_source_options();
    run_route(
        yulang2::check_poly_from_entry_with_std_options(path, &source_options),
        print_check_poly_output,
    );
}

fn run_compatible_run(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let (path, selection) = parse_run_args(program, args);
    if options.no_prelude {
        if selection.interpreter {
            run_route(
                yulang2::run_mono_from_entry(path),
                run_mono_printer(selection.print_roots),
            );
        } else {
            run_route(
                yulang2::run_control_from_entry(path),
                run_control_printer(selection.print_roots),
            );
        }
        return;
    }

    let source_options = options.std_source_options();
    if selection.interpreter {
        run_route(
            yulang2::run_mono_from_entry_with_std_options(path, &source_options),
            run_mono_printer(selection.print_roots),
        );
    } else {
        run_route(
            yulang2::run_control_from_entry_with_std_options(path, &source_options),
            run_control_printer(selection.print_roots),
        );
    }
}

fn run_compatible_dump(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let (path, selection) = parse_dump_args(program, args);
    if options.no_prelude {
        print_selected_dump_without_std(path, selection);
        return;
    }

    let source_options = options.std_source_options();
    print_selected_dump_with_std(path, selection, &source_options);
}

fn parse_run_args(program: &str, mut args: VecDeque<OsString>) -> (PathBuf, RunSelection) {
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

fn parse_dump_args(program: &str, mut args: VecDeque<OsString>) -> (PathBuf, DumpSelection) {
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
                    "dump --hygiene-ir is not supported by yulang2 yet",
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

fn print_selected_dump_without_std(path: PathBuf, selection: DumpSelection) {
    if selection.poly {
        run_route(
            yulang2::dump_poly_from_entry(path.clone()),
            print_dump_poly_output,
        );
    }
    if selection.poly_raw {
        run_route(
            yulang2::dump_poly_raw_from_entry(path.clone()),
            print_dump_poly_output,
        );
    }
    if selection.mono {
        run_route(yulang2::dump_mono_from_entry(path), print_dump_mono_output);
    }
}

fn print_selected_dump_with_std(
    path: PathBuf,
    selection: DumpSelection,
    options: &yulang2::StdSourceOptions,
) {
    if selection.poly {
        run_route(
            yulang2::dump_poly_from_entry_with_std_options(path.clone(), options),
            print_dump_poly_output,
        );
    }
    if selection.poly_raw {
        run_route(
            yulang2::dump_poly_raw_from_entry_with_std_options(path.clone(), options),
            print_dump_poly_output,
        );
    }
    if selection.mono {
        run_route(
            yulang2::dump_mono_from_entry_with_std_options(path, options),
            print_dump_mono_output,
        );
    }
}

fn require_one_path(program: &str, mut args: VecDeque<OsString>) -> PathBuf {
    let Some(path) = args.pop_front() else {
        print_usage_and_exit(program);
    };
    if args.pop_front().is_some() {
        print_usage_and_exit(program);
    }
    PathBuf::from(path)
}

fn require_path_and_module(program: &str, mut args: VecDeque<OsString>) -> (PathBuf, String) {
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

fn set_single_path(program: &str, path: &mut Option<PathBuf>, value: OsString) {
    if path.is_some() {
        print_usage_and_exit(program);
    }
    *path = Some(PathBuf::from(value));
}

fn run_route<T>(result: Result<T, yulang2::RouteError>, print: impl FnOnce(&T)) {
    match result {
        Ok(output) => print(&output),
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    }
}

fn print_dump_poly_output(output: &yulang2::DumpPolyOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn print_dump_mono_output(output: &yulang2::DumpMonoOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn print_run_mono_output(output: &yulang2::RunMonoOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn print_run_control_output(output: &yulang2::RunControlOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn run_mono_printer(print_roots: bool) -> impl FnOnce(&yulang2::RunMonoOutput) {
    move |output| {
        if print_roots {
            print!("{}", output.text);
        }
        for error in &output.errors {
            eprintln!("error: {error}");
        }
    }
}

fn run_control_printer(print_roots: bool) -> impl FnOnce(&yulang2::RunControlOutput) {
    move |output| {
        if print_roots {
            print!("{}", output.text);
        }
        for error in &output.errors {
            eprintln!("error: {error}");
        }
    }
}

fn print_check_poly_output(output: &yulang2::CheckPolyOutput) {
    print!("{}", output.text);
}

fn print_usage_error_and_exit(program: &str, error: &str) -> ! {
    eprintln!("{error}");
    print_usage_and_exit(program);
}

fn print_usage_and_exit(program: &str) -> ! {
    eprintln!("usage: {program} [--std-root <path>] [--no-prelude] check <path>");
    eprintln!(
        "       {program} [--std-root <path>] [--no-prelude] run [--interpreter] [--print-roots] <path>"
    );
    eprintln!(
        "       {program} [--std-root <path>] [--no-prelude] dump <path> (--core-ir | --runtime-ir | --poly | --poly-raw | --mono)"
    );
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
