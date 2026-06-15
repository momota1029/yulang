use std::collections::VecDeque;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;
use std::process;

mod cst_view;
mod parse_view;

fn main() {
    let mut raw_args = env::args_os();
    let program = raw_args
        .next()
        .map(PathBuf::from)
        .and_then(|path| path.file_name().map(|name| name.to_owned()))
        .and_then(|name| name.into_string().ok())
        .unwrap_or_else(|| "yulang".to_string());

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
        Some("build") => run_compatible_build(&program, &options, args),
        Some("run") | Some("interpret") => run_compatible_run(&program, &options, args),
        Some("dump") => run_compatible_dump(&program, &options, args),
        Some("parse") => run_compatible_parse(&program, args),
        Some("install") => run_install(&program, &options, args),
        Some("install-std") => run_install_std(&program, &options, args),
        Some("cache") => run_cache(&program, args),
        Some("realm") => run_realm(&program, args),
        Some("server") => run_server(&program, &options, args),
        Some("debug") => run_debug(&program, &options, args),
        Some("dump-poly") => {
            let path = require_one_path(&program, args);
            run_route(yulang::dump_poly_from_entry(path), print_dump_poly_output);
        }
        Some("dump-poly-raw") => {
            let path = require_one_path(&program, args);
            run_route(
                yulang::dump_poly_raw_from_entry(path),
                print_dump_poly_output,
            );
        }
        Some("dump-mono") => {
            let path = require_one_path(&program, args);
            run_route(yulang::dump_mono_from_entry(path), print_dump_mono_output);
        }
        Some("run-mono") => {
            let path = require_one_path(&program, args);
            run_route(yulang::run_mono_from_entry(path), print_run_mono_output);
        }
        Some("run-control") => {
            let path = require_one_path(&program, args);
            run_route(
                yulang::run_control_from_entry(path),
                print_run_control_output,
            );
        }
        Some("dump-poly-std") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            let files = run_route_to_value(yulang::collect_local_sources_with_std_options(
                path,
                &source_options,
            ));
            let output = dump_poly_with_optional_cache(files, false, options.use_cache);
            print_dump_poly_output(&output);
        }
        Some("dump-mono-std") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            let files = run_route_to_value(yulang::collect_local_sources_with_std_options(
                path,
                &source_options,
            ));
            let output = dump_mono_with_optional_cache(files, options.use_cache);
            print_dump_mono_output(&output);
        }
        Some("run-mono-std") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            let files = run_route_to_value(yulang::collect_local_sources_with_std_options(
                path,
                &source_options,
            ));
            let output = run_mono_with_optional_cache(files, options.use_cache);
            print_run_mono_output(&output);
        }
        Some("run-control-std") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            let files = run_route_to_value(yulang::collect_local_sources_with_std_options(
                path,
                &source_options,
            ));
            let build = build_control_with_optional_cache(files, options.use_cache);
            run_route(
                yulang::run_built_control_program(&build.program, build.file_count, build.errors),
                print_run_control_output,
            );
        }
        Some("check-poly-std") => {
            let path = require_one_path(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang::check_poly_from_entry_with_std_options(path, &source_options),
                print_check_poly_output,
            );
        }
        Some("check-poly-std-in") => {
            let (path, module) = require_path_and_module(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang::check_poly_from_entry_with_std_in_module_options(
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
                yulang::dump_poly_from_entry_with_std_in_module_options(
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
            let files = run_route_to_value(yulang::collect_local_sources_with_std_options(
                path,
                &source_options,
            ));
            let output = dump_poly_with_optional_cache(files, true, options.use_cache);
            print_dump_poly_output(&output);
        }
        Some("dump-poly-std-in-raw") => {
            let (path, module) = require_path_and_module(&program, args);
            let source_options = options.std_source_options();
            run_route(
                yulang::dump_poly_raw_from_entry_with_std_in_module_options(
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct GlobalOptions {
    std_root: Option<PathBuf>,
    no_prelude: bool,
    show_cst: bool,
    use_cache: bool,
}

impl Default for GlobalOptions {
    fn default() -> Self {
        Self {
            std_root: None,
            no_prelude: false,
            show_cst: false,
            use_cache: true,
        }
    }
}

impl GlobalOptions {
    fn std_source_options(&self) -> yulang::StdSourceOptions {
        yulang::StdSourceOptions {
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
            Some("--cst") => {
                options.show_cst = true;
            }
            Some("--no-cache") => {
                options.use_cache = false;
            }
            Some("--verbose-ir")
            | Some("--infer-phase-timings")
            | Some("--runtime-phase-timings")
            | Some("--startup-profile") => {}
            Some("--profile-repeat") | Some("--profile-flamegraph") => {
                if args.pop_front().is_none() {
                    return Err(format!("{arg:?} requires a value"));
                }
            }
            Some(value) if value.starts_with("--profile-repeat=") => {}
            Some(value) if value.starts_with("--profile-flamegraph=") => {}
            _ => command_args.push_back(arg),
        }
    }
    Ok((options, command_args))
}

fn run_compatible_check(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let path = require_one_path(program, args);
    print_cst_if_requested(options, &path);
    if options.no_prelude {
        run_route(yulang::check_poly_from_entry(path), print_check_poly_output);
        return;
    }

    let source_options = options.std_source_options();
    run_route(
        yulang::check_poly_from_entry_with_std_options(path, &source_options),
        print_check_poly_output,
    );
}

fn run_compatible_build(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let (path, out) = parse_build_args(program, args);
    print_cst_if_requested(options, &path);
    let files = collect_control_sources_or_exit(&path, options);
    let output = build_control_with_optional_cache(files, options.use_cache);
    let artifact = match yulang::artifact::encode_control_program(&output.program) {
        Ok(artifact) => artifact,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    let out = out.unwrap_or_else(|| default_artifact_path(&path));
    ensure_parent_dir_or_exit(&out, "control-vm artifact");
    if let Err(error) = fs::write(&out, artifact) {
        eprintln!(
            "failed to write control-vm artifact {}: {error}",
            out.display()
        );
        process::exit(1);
    }
    for error in &output.errors {
        eprintln!("error: {error}");
    }
    println!("build: {}", out.display());
}

fn run_compatible_run(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let (path, selection) = parse_run_args(program, args);
    if let Some(artifact) = read_control_artifact_or_exit(&path) {
        if selection.interpreter {
            eprintln!("control-vm artifact cannot be run with --interpreter");
            process::exit(2);
        }
        run_control_artifact(artifact, selection.print_roots);
        return;
    }

    print_cst_if_requested(options, &path);
    if selection.interpreter {
        if options.no_prelude {
            run_route(
                yulang::run_mono_from_entry(path),
                run_mono_printer(selection.print_roots),
            );
        } else {
            let source_options = options.std_source_options();
            let files = run_route_to_value(yulang::collect_local_sources_with_std_options(
                path,
                &source_options,
            ));
            let output = run_mono_with_optional_cache(files, options.use_cache);
            run_mono_printer(selection.print_roots)(&output);
        }
        return;
    }

    let files = collect_control_sources_or_exit(&path, options);
    let build = build_control_with_optional_cache(files, options.use_cache);
    let output = run_route_to_value(yulang::run_built_control_program(
        &build.program,
        build.file_count,
        build.errors,
    ));
    run_control_printer(selection.print_roots)(&output);
}

fn collect_control_sources_or_exit(
    path: &PathBuf,
    options: &GlobalOptions,
) -> Vec<yulang::CollectedSource> {
    if options.no_prelude {
        return run_route_to_value(yulang::collect_local_sources(path));
    }

    let source_options = options.std_source_options();
    run_route_to_value(yulang::collect_local_sources_with_std_options(
        path,
        &source_options,
    ))
}

fn build_control_with_optional_cache(
    files: Vec<yulang::CollectedSource>,
    use_cache: bool,
) -> yulang::BuildControlOutput {
    if !use_cache {
        return run_route_to_value(yulang::build_control_from_collected_sources(files));
    }

    let key = yulang::cache::source_cache_key(&files);
    let cache = yulang::cache::ArtifactCache::new(yulang::stdlib::default_user_cache_root());
    match cache.read_control_artifact(key) {
        Ok(Some(cached)) => {
            return yulang::BuildControlOutput {
                program: cached.program,
                file_count: cached.file_count,
                errors: cached.errors,
            };
        }
        Ok(None) => {}
        Err(error) => eprintln!("warning: {error}"),
    }

    let poly = build_poly_with_cache(files, key, &cache);
    let output = run_route_to_value(yulang::build_control_from_poly_output(&poly));
    let artifact = yulang::cache::CachedControlArtifact {
        program: output.program.clone(),
        file_count: output.file_count,
        errors: output.errors.clone(),
    };
    if let Err(error) = cache.write_control_artifact(key, &artifact) {
        eprintln!("warning: {error}");
    }
    output
}

fn build_poly_with_optional_cache(
    files: Vec<yulang::CollectedSource>,
    use_cache: bool,
) -> yulang::BuildPolyOutput {
    if !use_cache {
        return run_route_to_value(yulang::build_poly_from_collected_sources(files));
    }

    let key = yulang::cache::source_cache_key(&files);
    let cache = yulang::cache::ArtifactCache::new(yulang::stdlib::default_user_cache_root());
    build_poly_with_cache(files, key, &cache)
}

fn build_poly_with_cache(
    files: Vec<yulang::CollectedSource>,
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
) -> yulang::BuildPolyOutput {
    match cache.read_poly_artifact(key) {
        Ok(Some(cached)) => yulang::BuildPolyOutput {
            arena: cached.arena,
            labels: cached.labels,
            file_count: cached.file_count,
            errors: cached.errors,
        },
        Ok(None) => {
            let output = run_route_to_value(yulang::build_poly_from_collected_sources(files));
            let artifact = yulang::cache::CachedPolyArtifact {
                arena: output.arena,
                labels: output.labels,
                file_count: output.file_count,
                errors: output.errors,
            };
            if let Err(error) = cache.write_poly_artifact(key, &artifact) {
                eprintln!("warning: {error}");
            }
            yulang::BuildPolyOutput {
                arena: artifact.arena,
                labels: artifact.labels,
                file_count: artifact.file_count,
                errors: artifact.errors,
            }
        }
        Err(error) => {
            eprintln!("warning: {error}");
            run_route_to_value(yulang::build_poly_from_collected_sources(files))
        }
    }
}

fn dump_poly_with_optional_cache(
    files: Vec<yulang::CollectedSource>,
    raw: bool,
    use_cache: bool,
) -> yulang::DumpPolyOutput {
    let output = build_poly_with_optional_cache(files, use_cache);
    let text = if raw {
        poly::dump::dump_arena_raw_with_labels(&output.arena, &output.labels)
    } else {
        poly::dump::dump_arena_with_labels(&output.arena, &output.labels)
    };
    yulang::DumpPolyOutput {
        text,
        file_count: output.file_count,
        errors: output.errors,
    }
}

fn dump_mono_with_optional_cache(
    files: Vec<yulang::CollectedSource>,
    use_cache: bool,
) -> yulang::DumpMonoOutput {
    let output = build_poly_with_optional_cache(files, use_cache);
    let program = match specialize::specialize(&output.arena) {
        Ok(program) => program,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    yulang::DumpMonoOutput {
        text: specialize::mono::dump::dump_program(&program),
        file_count: output.file_count,
        errors: output.errors,
    }
}

fn run_mono_with_optional_cache(
    files: Vec<yulang::CollectedSource>,
    use_cache: bool,
) -> yulang::RunMonoOutput {
    let output = build_poly_with_optional_cache(files, use_cache);
    let program = match specialize::specialize(&output.arena) {
        Ok(program) => program,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    let values = match mono_runtime::run_program(&program) {
        Ok(values) => values,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    yulang::RunMonoOutput {
        text: yulang::format_run_mono_values(&values),
        file_count: output.file_count,
        errors: output.errors,
        values,
    }
}

fn run_compatible_dump(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let (path, selection) = parse_dump_args(program, args);
    print_cst_if_requested(options, &path);
    if options.no_prelude {
        print_selected_dump_without_std(path, selection);
        return;
    }

    let source_options = options.std_source_options();
    print_selected_dump_with_std(path, selection, &source_options, options.use_cache);
}

fn run_compatible_parse(program: &str, args: VecDeque<OsString>) {
    let (path, mode) = parse_parse_args(program, args);
    let source = read_source_or_exit(path.as_ref());
    let output = parse_view::run_parser_view(mode, &source);
    print!("{}", output.text);
    if !output.ok {
        eprintln!("parse failed");
        process::exit(1);
    }
}

fn run_install(program: &str, options: &GlobalOptions, mut args: VecDeque<OsString>) {
    let Some(target) = args.pop_front() else {
        print_usage_and_exit(program);
    };
    if args.pop_front().is_some() {
        print_usage_and_exit(program);
    }
    match target.to_str() {
        Some("std") => run_install_std(program, options, VecDeque::new()),
        _ => print_usage_and_exit(program),
    }
}

fn run_install_std(program: &str, options: &GlobalOptions, mut args: VecDeque<OsString>) {
    if args.pop_front().is_some() {
        print_usage_and_exit(program);
    }
    let root = options
        .std_root
        .clone()
        .unwrap_or_else(yulang::stdlib::default_versioned_std_root);
    if let Err(error) = yulang::stdlib::install_embedded_std(&root) {
        eprintln!("failed to install std to {}: {error}", root.display());
        process::exit(1);
    }
    eprintln!("{}", root.display());
}

fn run_cache(program: &str, mut args: VecDeque<OsString>) {
    let Some(op) = args.pop_front() else {
        print_usage_and_exit(program);
    };
    if args.pop_front().is_some() {
        print_usage_and_exit(program);
    }
    let root = yulang::stdlib::default_user_cache_root();
    match op.to_str() {
        Some("path") => println!("{}", root.display()),
        Some("clear") => match fs::remove_dir_all(&root) {
            Ok(()) => println!("cleared {}", root.display()),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                println!("cache already empty {}", root.display());
            }
            Err(error) => {
                eprintln!("failed to clear cache {}: {error}", root.display());
                process::exit(1);
            }
        },
        _ => print_usage_and_exit(program),
    }
}

fn run_realm(program: &str, mut args: VecDeque<OsString>) {
    let Some(op) = args.pop_front() else {
        print_usage_and_exit(program);
    };
    match op.to_str() {
        Some("freeze") => {
            let (path, version) = parse_realm_freeze_args(program, args);
            let root = path.unwrap_or_else(|| PathBuf::from("."));
            match sources::freeze_realm_version(&root, version) {
                Ok(output) => {
                    let status = if output.already_exists {
                        "already frozen"
                    } else {
                        "frozen"
                    };
                    println!(
                        "realm freeze: {status} {} hash={:016x} files={}",
                        output.root.display(),
                        output.snapshot.source_hash,
                        output.snapshot.files.len()
                    );
                }
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        _ => print_usage_and_exit(program),
    }
}

fn run_server(program: &str, options: &GlobalOptions, mut args: VecDeque<OsString>) {
    if args.pop_front().is_some() {
        print_usage_and_exit(program);
    }
    yulang::server::run_blocking(options.std_root.clone());
}

fn run_debug(program: &str, options: &GlobalOptions, mut args: VecDeque<OsString>) {
    let Some(op) = args.pop_front() else {
        print_usage_and_exit(program);
    };
    match op.to_str() {
        Some("control-vm") => run_compatible_run(program, options, args),
        Some("control-vm-emit") => run_compatible_build(program, options, args),
        Some("control-vm-load") => {
            let (path, selection) = parse_run_args(program, args);
            if selection.interpreter {
                print_usage_error_and_exit(
                    program,
                    "debug control-vm-load does not take --interpreter",
                );
            }
            let Some(artifact) = read_control_artifact_or_exit(&path) else {
                eprintln!("{} is not a yulang control-vm artifact", path.display());
                process::exit(1);
            };
            run_control_artifact(artifact, selection.print_roots);
        }
        _ => print_usage_and_exit(program),
    }
}

fn parse_realm_freeze_args(
    program: &str,
    mut args: VecDeque<OsString>,
) -> (Option<PathBuf>, String) {
    let mut path = None;
    let mut version = None;
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--version") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "realm freeze --version requires a value");
                };
                set_realm_version(program, &mut version, value);
            }
            Some(value) if value.starts_with("--version=") => {
                let value = value.strip_prefix("--version=").unwrap_or_default();
                if value.is_empty() {
                    print_usage_error_and_exit(program, "realm freeze --version requires a value");
                }
                set_realm_version(program, &mut version, OsString::from(value));
            }
            Some(flag) if flag.starts_with("--") => {
                print_usage_error_and_exit(
                    program,
                    &format!("unsupported realm freeze option {flag}"),
                );
            }
            _ => set_single_path(program, &mut path, arg),
        }
    }
    let Some(version) = version else {
        print_usage_error_and_exit(program, "realm freeze requires --version <version>");
    };
    (path, version)
}

fn set_realm_version(program: &str, version: &mut Option<String>, value: OsString) {
    if version.is_some() {
        print_usage_and_exit(program);
    }
    let Some(value) = value.to_str() else {
        print_usage_error_and_exit(program, "realm version must be UTF-8");
    };
    *version = Some(value.to_string());
}

fn parse_build_args(program: &str, mut args: VecDeque<OsString>) -> (PathBuf, Option<PathBuf>) {
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

fn parse_parse_args(
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

fn parse_parser_mode_or_exit(program: &str, value: &str) -> Option<parse_view::ParserMode> {
    let Some(mode) = parse_view::parse_mode(value) else {
        print_usage_error_and_exit(
            program,
            &format!("unknown parse mode {value:?}; expected expr, pat, stmt, type, or mark"),
        );
    };
    Some(mode)
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

fn print_selected_dump_without_std(path: PathBuf, selection: DumpSelection) {
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

fn print_selected_dump_with_std(
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

fn set_single_output_path(program: &str, out: &mut Option<PathBuf>, value: OsString) {
    if out.is_some() {
        print_usage_and_exit(program);
    }
    *out = Some(PathBuf::from(value));
}

fn read_source_or_exit(path: Option<&PathBuf>) -> String {
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

fn print_cst_if_requested(options: &GlobalOptions, path: &PathBuf) {
    if !options.show_cst {
        return;
    }
    let source = read_source_or_exit(Some(path));
    print!("{}", cst_view::format_module_cst(&source));
}

fn read_control_artifact_or_exit(path: &PathBuf) -> Option<control_vm::Program> {
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

fn run_control_artifact(program: control_vm::Program, print_roots: bool) {
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

fn default_artifact_path(entry: &PathBuf) -> PathBuf {
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

fn ensure_parent_dir_or_exit(path: &PathBuf, label: &str) {
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

fn run_route<T>(result: Result<T, yulang::RouteError>, print: impl FnOnce(&T)) {
    match result {
        Ok(output) => print(&output),
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    }
}

fn run_route_to_value<T>(result: Result<T, yulang::RouteError>) -> T {
    match result {
        Ok(output) => output,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    }
}

fn print_dump_poly_output(output: &yulang::DumpPolyOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn print_dump_mono_output(output: &yulang::DumpMonoOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn print_run_mono_output(output: &yulang::RunMonoOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn print_run_control_output(output: &yulang::RunControlOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn run_mono_printer(print_roots: bool) -> impl FnOnce(&yulang::RunMonoOutput) {
    move |output| {
        if print_roots {
            print!("{}", output.text);
        }
        for error in &output.errors {
            eprintln!("error: {error}");
        }
    }
}

fn run_control_printer(print_roots: bool) -> impl FnOnce(&yulang::RunControlOutput) {
    move |output| {
        if print_roots {
            print!("{}", output.text);
        }
        for error in &output.errors {
            eprintln!("error: {error}");
        }
    }
}

fn print_check_poly_output(output: &yulang::CheckPolyOutput) {
    print!("{}", output.text);
}

fn print_usage_error_and_exit(program: &str, error: &str) -> ! {
    eprintln!("{error}");
    print_usage_and_exit(program);
}

fn print_usage_and_exit(program: &str) -> ! {
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
