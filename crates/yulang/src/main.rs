use std::collections::VecDeque;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;
use std::process;
use std::time::{Duration, Instant};

mod cst_view;
mod parse_view;
mod support;
use support::*;

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
            let files = collect_bare_sources_or_exit(&path, &options);
            let output = dump_mono_with_optional_cache(files, options.use_cache);
            print_dump_mono_output(&output);
        }
        Some("run-mono") => {
            let path = require_one_path(&program, args);
            let files = collect_bare_sources_or_exit(&path, &options);
            let output = run_mono_with_optional_cache(files, options.use_cache);
            print_run_mono_output(&output);
        }
        Some("run-control") => {
            let path = require_one_path(&program, args);
            let build = run_route_to_value(yulang::build_control_from_entry(path));
            let output = run_built_control_for_cli(build);
            print_cli_control_run_output(&output);
        }
        Some("dump-poly-std") => {
            let path = require_one_path(&program, args);
            let files = collect_std_sources_or_exit(&path, &options);
            let output = dump_poly_with_optional_cache(files, false, options.use_cache);
            print_dump_poly_output(&output);
        }
        Some("dump-mono-std") => {
            let path = require_one_path(&program, args);
            let files = collect_std_sources_or_exit(&path, &options);
            let output = dump_mono_with_optional_cache(files, options.use_cache);
            print_dump_mono_output(&output);
        }
        Some("run-mono-std") => {
            let path = require_one_path(&program, args);
            let files = collect_std_sources_or_exit(&path, &options);
            let output = run_mono_with_optional_cache(files, options.use_cache);
            print_run_mono_output(&output);
        }
        Some("run-control-std") => {
            let path = require_one_path(&program, args);
            let files = collect_std_sources_or_exit(&path, &options);
            let build = build_control_with_optional_cache(files, options.use_cache);
            let output = run_built_control_for_cli(build);
            print_cli_control_run_output(&output);
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
            let files = collect_std_sources_or_exit(&path, &options);
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
    runtime_phase_timings: bool,
}

impl Default for GlobalOptions {
    fn default() -> Self {
        Self {
            std_root: None,
            no_prelude: false,
            show_cst: false,
            use_cache: true,
            runtime_phase_timings: false,
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
    control_evidence: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum RunInput {
    Path(PathBuf),
    Source { path: PathBuf, source: String },
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct RunSelection {
    interpreter: bool,
    print_roots: bool,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct RuntimePhaseTimings {
    build_cache: RuntimeBuildCacheKind,
    collect: Duration,
    build_poly: Duration,
    specialize: Duration,
    control_lower: Duration,
    vm_eval: Duration,
    control_validate: Duration,
    runtime_init: Duration,
    runtime_execute: Duration,
    root_format: Duration,
    total: Duration,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct RuntimeEvidenceBenchSummary {
    tasks: usize,
    graph_slots: u64,
    graph_weighted_constraints: u64,
    graph_weighted_edges: u64,
    graph_effect_subtractions: u64,
    graph_row_residuals: usize,
    nodes: usize,
    node_slots: usize,
    node_weighted_slots: usize,
    node_effect_subtraction_slots: usize,
    node_evidence_refs: usize,
    sites: usize,
    expr_types: usize,
    expr_stack_weights: usize,
    ref_signatures: usize,
    select_signatures: usize,
    pat_ref_signatures: usize,
    typeclass_resolutions: usize,
    type_stack_weights: usize,
    raw_thunk_computations: usize,
}

impl RuntimeEvidenceBenchSummary {
    fn from_surface(surface: &specialize::RuntimeEvidenceSurface) -> Self {
        let mut summary = Self {
            tasks: surface.tasks.len(),
            ..Self::default()
        };

        for task in &surface.tasks {
            summary.graph_slots += u64::from(task.graph.slot_count);
            summary.graph_weighted_constraints += u64::from(task.graph.weighted_constraint_count);
            summary.graph_weighted_edges += u64::from(task.graph.weighted_edge_count);
            summary.graph_effect_subtractions += u64::from(task.graph.effect_subtraction_count);
            summary.graph_row_residuals += task.graph.row_residuals.len();
            summary.nodes += task.nodes.len();
            summary.node_slots += task
                .nodes
                .iter()
                .map(|node| node.slots.len())
                .sum::<usize>();
            summary.node_weighted_slots += task
                .nodes
                .iter()
                .map(|node| node.weighted_slots.len())
                .sum::<usize>();
            summary.node_effect_subtraction_slots += task
                .nodes
                .iter()
                .map(|node| node.effect_subtraction_slots.len())
                .sum::<usize>();
            summary.node_evidence_refs += task
                .nodes
                .iter()
                .map(|node| node.evidence_refs.len())
                .sum::<usize>();
            summary.sites += task.sites.len();
            summary.expr_types += task.expr_types.len();
            summary.expr_stack_weights += task
                .expr_types
                .iter()
                .map(|expr| expr.stack_weights.len())
                .sum::<usize>();
            summary.ref_signatures += task.ref_signatures.len();
            summary.select_signatures += task.select_signatures.len();
            summary.pat_ref_signatures += task.pat_ref_signatures.len();
            summary.typeclass_resolutions += task.typeclass_resolutions.len();
            summary.type_stack_weights += task
                .expr_types
                .iter()
                .map(|expr| expr.stack_weights.len())
                .sum::<usize>();
            summary.type_stack_weights += task
                .ref_signatures
                .iter()
                .map(|signature| signature.stack_weights.len())
                .sum::<usize>();
            summary.type_stack_weights += task
                .select_signatures
                .iter()
                .map(|signature| signature.stack_weights.len())
                .sum::<usize>();
            summary.type_stack_weights += task
                .pat_ref_signatures
                .iter()
                .map(|signature| signature.stack_weights.len())
                .sum::<usize>();
            summary.type_stack_weights += task
                .typeclass_resolutions
                .iter()
                .map(|resolution| resolution.stack_weights.len())
                .sum::<usize>();
            summary.raw_thunk_computations += task.raw_thunk_computations.len();
        }

        summary
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeEvidenceRunArgs {
    path: PathBuf,
    compare_control: bool,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum RuntimeBuildCacheKind {
    #[default]
    NotMeasured,
    Disabled,
    ControlHit,
    PolyHit,
    CompiledUnitHit,
    StdPrefixHit,
    StdPrefixBuild,
    SourceUnitPrefixHit,
    MergedSourceUnitPrefixHit,
    FullMiss,
    ErrorFallback,
}

impl RuntimeBuildCacheKind {
    fn as_str(self) -> &'static str {
        match self {
            Self::NotMeasured => "not-measured",
            Self::Disabled => "disabled",
            Self::ControlHit => "control-hit",
            Self::PolyHit => "poly-hit",
            Self::CompiledUnitHit => "compiled-unit-hit",
            Self::StdPrefixHit => "std-prefix-hit",
            Self::StdPrefixBuild => "std-prefix-build",
            Self::SourceUnitPrefixHit => "source-unit-prefix-hit",
            Self::MergedSourceUnitPrefixHit => "merged-source-unit-prefix-hit",
            Self::FullMiss => "full-miss",
            Self::ErrorFallback => "error-fallback",
        }
    }
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
            Some("--runtime-phase-timings") => {
                options.runtime_phase_timings = true;
            }
            Some("--verbose-ir") | Some("--infer-phase-timings") | Some("--startup-profile") => {}
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
    abort_on_runtime_lowering_errors(&output.errors);
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
    let (input, selection) = parse_run_args(program, args);
    if let RunInput::Path(path) = &input {
        if let Some(artifact) = read_control_artifact_or_exit(path) {
            if selection.interpreter {
                eprintln!("control-vm artifact cannot be run with --interpreter");
                process::exit(2);
            }
            run_control_artifact(artifact, selection.print_roots);
            return;
        }
    }

    print_run_input_cst_if_requested(options, &input);
    if selection.interpreter {
        if options.no_prelude {
            let output = match input {
                RunInput::Path(path) => run_route_to_value(yulang::run_mono_from_entry(path)),
                RunInput::Source { path, source } => {
                    let files = run_route_to_value(yulang::collect_local_source_text(path, source));
                    run_mono_with_optional_cache(files, options.use_cache)
                }
            };
            run_mono_printer(selection.print_roots)(&output);
        } else {
            let source_options = options.std_source_options();
            let files = collect_std_run_input_sources_or_exit(input, &source_options);
            let output = run_mono_with_optional_cache(files, options.use_cache);
            run_mono_printer(selection.print_roots)(&output);
        }
        return;
    }

    let mut timings = RuntimePhaseTimings::default();
    let total_start = Instant::now();
    let collect_start = Instant::now();
    let files = collect_control_run_input_sources_or_exit(input, options);
    timings.collect = collect_start.elapsed();
    let build = build_control_with_optional_cache_timed(
        files,
        options.use_cache,
        options.runtime_phase_timings.then_some(&mut timings),
    );
    let eval_start = Instant::now();
    let output = run_built_control_for_cli(build);
    timings.vm_eval = eval_start.elapsed();
    timings.control_validate = output.timings.validate;
    timings.runtime_init = output.timings.init;
    timings.runtime_execute = output.timings.execute;
    timings.root_format = output.timings.root_format;
    timings.total = total_start.elapsed();
    print_cli_control_run_output_with_roots(&output, selection.print_roots);
    if options.runtime_phase_timings {
        print_runtime_phase_timings(&timings, &output.stats);
    }
}

fn print_run_input_cst_if_requested(options: &GlobalOptions, input: &RunInput) {
    match input {
        RunInput::Path(path) => print_cst_if_requested(options, path),
        RunInput::Source { source, .. } => {
            if options.show_cst {
                print!("{}", cst_view::format_module_cst(source));
            }
        }
    }
}

fn collect_control_run_input_sources_or_exit(
    input: RunInput,
    options: &GlobalOptions,
) -> Vec<yulang::CollectedSource> {
    if options.no_prelude {
        return collect_bare_run_input_sources_or_exit(input, options);
    }

    let source_options = options.std_source_options();
    match input {
        RunInput::Path(path) => collect_std_sources_or_exit(&path, options),
        RunInput::Source { path, source } => run_route_to_value(
            yulang::collect_local_source_text_with_std_options(path, source, &source_options),
        ),
    }
}

fn collect_bare_run_input_sources_or_exit(
    input: RunInput,
    options: &GlobalOptions,
) -> Vec<yulang::CollectedSource> {
    match input {
        RunInput::Path(path) => collect_bare_sources_or_exit(&path, options),
        RunInput::Source { path, source } => {
            run_route_to_value(yulang::collect_local_source_text(path, source))
        }
    }
}

fn collect_std_run_input_sources_or_exit(
    input: RunInput,
    source_options: &yulang::StdSourceOptions,
) -> Vec<yulang::CollectedSource> {
    match input {
        RunInput::Path(path) => run_route_to_value(yulang::collect_local_sources_with_std_options(
            path,
            source_options,
        )),
        RunInput::Source { path, source } => run_route_to_value(
            yulang::collect_local_source_text_with_std_options(path, source, source_options),
        ),
    }
}

fn collect_control_sources_or_exit(
    path: &PathBuf,
    options: &GlobalOptions,
) -> Vec<yulang::CollectedSource> {
    if options.no_prelude {
        return collect_bare_sources_or_exit(path, options);
    }

    collect_std_sources_or_exit(path, options)
}

fn collect_bare_sources_or_exit(
    path: &PathBuf,
    options: &GlobalOptions,
) -> Vec<yulang::CollectedSource> {
    match source_collection_cache(options) {
        Some(cache) => run_route_to_value(yulang::collect_local_sources_with_cache(path, cache)),
        None => run_route_to_value(yulang::collect_local_sources(path)),
    }
}

fn collect_std_sources_or_exit(
    path: &PathBuf,
    options: &GlobalOptions,
) -> Vec<yulang::CollectedSource> {
    let source_options = options.std_source_options();
    run_route_to_value(yulang::collect_local_sources_with_std_options_and_cache(
        path,
        &source_options,
        source_collection_cache(options),
    ))
}

fn source_collection_cache(options: &GlobalOptions) -> Option<yulang::SourceCollectionCache> {
    options.use_cache.then(|| {
        yulang::SourceCollectionCache::new(yulang::cache::ArtifactCache::new(
            yulang::stdlib::default_user_cache_root(),
        ))
    })
}

fn build_control_with_optional_cache(
    files: Vec<yulang::CollectedSource>,
    use_cache: bool,
) -> yulang::BuildControlOutput {
    build_control_with_optional_cache_timed(files, use_cache, None)
}

fn build_control_with_optional_cache_timed(
    files: Vec<yulang::CollectedSource>,
    use_cache: bool,
    mut timings: Option<&mut RuntimePhaseTimings>,
) -> yulang::BuildControlOutput {
    if !use_cache {
        record_runtime_build_cache(&mut timings, RuntimeBuildCacheKind::Disabled);
        if let Some(timings) = timings.as_deref_mut() {
            return build_control_without_cache_timed(files, timings);
        }
        return run_route_to_value(yulang::build_control_from_collected_sources(files));
    }

    let key = yulang::cache::source_cache_key(&files);
    let cache = yulang::cache::ArtifactCache::new(yulang::stdlib::default_user_cache_root());
    match cache.read_control_artifact(key) {
        Ok(Some(cached)) => {
            record_runtime_build_cache(&mut timings, RuntimeBuildCacheKind::ControlHit);
            return yulang::BuildControlOutput {
                program: cached.program,
                runtime_evidence: cached.runtime_evidence,
                labels: cached.labels,
                file_count: cached.file_count,
                errors: cached.errors,
            };
        }
        Ok(None) => {}
        Err(error) => eprintln!("warning: {error}"),
    }

    let poly_start = Instant::now();
    let poly = build_poly_with_cache_timed(files, key, &cache, timings.as_deref_mut());
    if let Some(timings) = timings.as_deref_mut() {
        timings.build_poly = poly_start.elapsed();
    }
    let output = build_control_from_poly_output_with_optional_mono_cache(
        poly,
        Some((&cache, key)),
        timings.as_deref_mut(),
    );
    let artifact = yulang::cache::CachedControlArtifact {
        program: output.program.clone(),
        runtime_evidence: output.runtime_evidence.clone(),
        labels: output.labels.clone(),
        file_count: output.file_count,
        errors: output.errors.clone(),
    };
    if let Err(error) = cache.write_control_artifact(key, &artifact) {
        eprintln!("warning: {error}");
    }
    output
}

fn build_control_without_cache_timed(
    files: Vec<yulang::CollectedSource>,
    timings: &mut RuntimePhaseTimings,
) -> yulang::BuildControlOutput {
    let poly_start = Instant::now();
    let poly = run_route_to_value(yulang::build_poly_from_collected_sources(files));
    timings.build_poly = poly_start.elapsed();

    build_control_from_poly_output_timed(poly, timings)
}

fn build_control_from_poly_output_timed(
    poly: yulang::BuildPolyOutput,
    timings: &mut RuntimePhaseTimings,
) -> yulang::BuildControlOutput {
    build_control_from_poly_output_with_optional_mono_cache(poly, None, Some(timings))
}

fn build_control_from_poly_output_with_optional_mono_cache(
    poly: yulang::BuildPolyOutput,
    mono_cache: Option<(&yulang::cache::ArtifactCache, yulang::cache::SourceCacheKey)>,
    mut timings: Option<&mut RuntimePhaseTimings>,
) -> yulang::BuildControlOutput {
    let specialize_start = Instant::now();
    let specialized = specialize_control_program(&poly, mono_cache);
    if let Some(timings) = timings.as_deref_mut() {
        timings.specialize = specialize_start.elapsed();
    }

    let control_lower_start = Instant::now();
    let program = match control_vm::lower(&specialized.program) {
        Ok(program) => program,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    if let Some(timings) = timings.as_deref_mut() {
        timings.control_lower = control_lower_start.elapsed();
    }

    yulang::BuildControlOutput {
        program,
        runtime_evidence: specialized.runtime_evidence,
        labels: poly.labels,
        file_count: poly.file_count,
        errors: poly.errors,
    }
}

fn specialize_mono_program(
    poly: &yulang::BuildPolyOutput,
    mono_cache: Option<(&yulang::cache::ArtifactCache, yulang::cache::SourceCacheKey)>,
) -> specialize::mono::Program {
    abort_on_runtime_lowering_errors(&poly.errors);
    if let Some((cache, key)) = mono_cache {
        match cache.read_mono_artifact(key) {
            Ok(Some(cached)) => return cached.program,
            Ok(None) => {}
            Err(error) => eprintln!("warning: {error}"),
        }
    }

    let program = match specialize::specialize(&poly.arena) {
        Ok(program) => program,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };

    if let Some((cache, key)) = mono_cache {
        let artifact = yulang::cache::CachedMonoArtifact {
            program: program.clone(),
            file_count: poly.file_count,
            errors: poly.errors.clone(),
        };
        if let Err(error) = cache.write_mono_artifact(key, &artifact) {
            eprintln!("warning: {error}");
        }
    }

    program
}

fn specialize_control_program(
    poly: &yulang::BuildPolyOutput,
    mono_cache: Option<(&yulang::cache::ArtifactCache, yulang::cache::SourceCacheKey)>,
) -> specialize::SpecializeOutput {
    abort_on_runtime_lowering_errors(&poly.errors);
    let output = match specialize::specialize_with_runtime_evidence(&poly.arena) {
        Ok(output) => output,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };

    if let Some((cache, key)) = mono_cache {
        let artifact = yulang::cache::CachedMonoArtifact {
            program: output.program.clone(),
            file_count: poly.file_count,
            errors: poly.errors.clone(),
        };
        if let Err(error) = cache.write_mono_artifact(key, &artifact) {
            eprintln!("warning: {error}");
        }
    }

    output
}

fn abort_on_runtime_lowering_errors(errors: &[String]) {
    if errors.is_empty() {
        return;
    }
    eprintln!("cannot build executable program with lowering errors");
    for error in errors {
        eprintln!("error: {error}");
    }
    process::exit(1);
}

fn record_runtime_build_cache(
    timings: &mut Option<&mut RuntimePhaseTimings>,
    kind: RuntimeBuildCacheKind,
) {
    if let Some(timings) = timings.as_deref_mut() {
        timings.build_cache = kind;
    }
}

fn print_runtime_phase_timings(timing: &RuntimePhaseTimings, stats: &control_vm::RuntimeStats) {
    eprintln!("runtime timing:");
    eprintln!("  run.cache: {}", timing.build_cache.as_str());
    eprintln!("  run.collect: {}", format_duration(timing.collect));
    eprintln!("  run.build_poly: {}", format_duration(timing.build_poly));
    eprintln!("  run.specialize: {}", format_duration(timing.specialize));
    eprintln!(
        "  run.control_lower: {}",
        format_duration(timing.control_lower)
    );
    eprintln!("  run.vm_eval: {}", format_duration(timing.vm_eval));
    eprintln!(
        "  run.control_validate: {}",
        format_duration(timing.control_validate)
    );
    eprintln!(
        "  run.runtime_init: {}",
        format_duration(timing.runtime_init)
    );
    eprintln!(
        "  run.runtime_execute: {}",
        format_duration(timing.runtime_execute)
    );
    eprintln!("  run.root_format: {}", format_duration(timing.root_format));
    eprintln!("  run.total: {}", format_duration(timing.total));
    eprintln!("runtime stats:");
    eprintln!("  run.control_effect_ops: {}", stats.control_effect_ops);
    eprintln!(
        "  run.control_effect_op_families: {}",
        stats.control_effect_op_families
    );
    eprintln!(
        "  run.control_effect_ops_with_handler_arm: {}",
        stats.control_effect_ops_with_handler_arm
    );
    eprintln!(
        "  run.control_effect_ops_without_handler_arm: {}",
        stats.control_effect_ops_without_handler_arm
    );
    eprintln!(
        "  run.control_marker_frames: {}",
        stats.control_marker_frames
    );
    eprintln!(
        "  run.control_marker_frame_families: {}",
        stats.control_marker_frame_families
    );
    eprintln!("  run.control_catches: {}", stats.control_catches);
    eprintln!("  run.control_handler_arms: {}", stats.control_handler_arms);
    eprintln!(
        "  run.control_handler_arm_families: {}",
        stats.control_handler_arm_families
    );
    eprintln!("  run.control_value_arms: {}", stats.control_value_arms);
    eprintln!(
        "  run.control_continuation_arms: {}",
        stats.control_continuation_arms
    );
    eprintln!(
        "  run.control_function_adapters: {}",
        stats.control_function_adapters
    );
    eprintln!("  run.control_ref_sets: {}", stats.control_ref_sets);
    eprintln!(
        "  run.control_scoped_effect_op_visits: {}",
        stats.control_scoped_effect_op_visits
    );
    eprintln!(
        "  run.control_scoped_unique_effect_ops: {}",
        stats.control_scoped_unique_effect_ops
    );
    eprintln!(
        "  run.control_scoped_unvisited_effect_ops: {}",
        stats.control_scoped_unvisited_effect_ops
    );
    eprintln!(
        "  run.control_scoped_effect_ops_with_nearest_handler: {}",
        stats.control_scoped_effect_ops_with_nearest_handler
    );
    eprintln!(
        "  run.control_scoped_effect_ops_without_nearest_handler: {}",
        stats.control_scoped_effect_ops_without_nearest_handler
    );
    eprintln!(
        "  run.control_scoped_effect_ops_with_direct_handler_candidate: {}",
        stats.control_scoped_effect_ops_with_direct_handler_candidate
    );
    eprintln!(
        "  run.control_scoped_effect_ops_blocked_by_callback_boundary: {}",
        stats.control_scoped_effect_ops_blocked_by_callback_boundary
    );
    eprintln!(
        "  run.control_scoped_effect_ops_blocked_by_delayed_boundary: {}",
        stats.control_scoped_effect_ops_blocked_by_delayed_boundary
    );
    eprintln!(
        "  run.control_scoped_effect_ops_with_resumptive_handler: {}",
        stats.control_scoped_effect_ops_with_resumptive_handler
    );
    eprintln!(
        "  run.control_scoped_effect_ops_with_abortive_handler: {}",
        stats.control_scoped_effect_ops_with_abortive_handler
    );
    eprintln!(
        "  run.control_scoped_effect_call_sites: {}",
        stats.control_scoped_effect_call_sites
    );
    eprintln!(
        "  run.control_scoped_effect_call_sites_with_nearest_handler: {}",
        stats.control_scoped_effect_call_sites_with_nearest_handler
    );
    eprintln!(
        "  run.control_scoped_effect_call_sites_without_nearest_handler: {}",
        stats.control_scoped_effect_call_sites_without_nearest_handler
    );
    eprintln!(
        "  run.control_scoped_effect_call_sites_with_direct_handler_candidate: {}",
        stats.control_scoped_effect_call_sites_with_direct_handler_candidate
    );
    eprintln!(
        "  run.control_scoped_effect_call_sites_blocked_by_callback_boundary: {}",
        stats.control_scoped_effect_call_sites_blocked_by_callback_boundary
    );
    eprintln!(
        "  run.control_scoped_effect_call_sites_blocked_by_delayed_boundary: {}",
        stats.control_scoped_effect_call_sites_blocked_by_delayed_boundary
    );
    eprintln!(
        "  run.control_scoped_effect_call_sites_with_resumptive_handler: {}",
        stats.control_scoped_effect_call_sites_with_resumptive_handler
    );
    eprintln!(
        "  run.control_scoped_effect_call_sites_with_abortive_handler: {}",
        stats.control_scoped_effect_call_sites_with_abortive_handler
    );
    eprintln!(
        "  run.control_scoped_known_function_call_sites: {}",
        stats.control_scoped_known_function_call_sites
    );
    eprintln!(
        "  run.control_scoped_known_instance_call_sites: {}",
        stats.control_scoped_known_instance_call_sites
    );
    eprintln!(
        "  run.control_scoped_dynamic_call_sites: {}",
        stats.control_scoped_dynamic_call_sites
    );
    eprintln!(
        "  run.control_scoped_dynamic_call_sites_under_handler: {}",
        stats.control_scoped_dynamic_call_sites_under_handler
    );
    eprintln!(
        "  run.control_scoped_known_thunk_force_sites: {}",
        stats.control_scoped_known_thunk_force_sites
    );
    eprintln!(
        "  run.control_scoped_dynamic_force_sites: {}",
        stats.control_scoped_dynamic_force_sites
    );
    eprintln!(
        "  run.control_scoped_dynamic_force_sites_under_handler: {}",
        stats.control_scoped_dynamic_force_sites_under_handler
    );
    eprintln!(
        "  run.control_scoped_callback_boundaries: {}",
        stats.control_scoped_callback_boundaries
    );
    eprintln!(
        "  run.control_scoped_delayed_boundaries: {}",
        stats.control_scoped_delayed_boundaries
    );
    eprintln!(
        "  run.control_scoped_max_handler_depth: {}",
        stats.control_scoped_max_handler_depth
    );
    eprintln!(
        "  run.control_scoped_missing_instance_refs: {}",
        stats.control_scoped_missing_instance_refs
    );
    eprintln!(
        "  run.control_scoped_cycle_instance_refs: {}",
        stats.control_scoped_cycle_instance_refs
    );
    eprintln!(
        "  run.control_scoped_missing_expr_refs: {}",
        stats.control_scoped_missing_expr_refs
    );
    eprintln!(
        "  run.control_scoped_cycle_expr_refs: {}",
        stats.control_scoped_cycle_expr_refs
    );
    eprintln!("  run.expr_evals: {}", stats.expr_evals);
    eprintln!("  run.expr_clones: {}", stats.expr_clones);
    eprintln!("  run.env_lookups: {}", stats.env_lookups);
    eprintln!("  run.env_lookup_hits: {}", stats.env_lookup_hits);
    eprintln!("  run.env_lookup_misses: {}", stats.env_lookup_misses);
    eprintln!("  run.env_lookup_steps: {}", stats.env_lookup_steps);
    eprintln!("  run.env_inserts: {}", stats.env_inserts);
    eprintln!("  run.env_cow_clones: {}", stats.env_cow_clones);
    eprintln!(
        "  run.env_cow_entries_copied: {}",
        stats.env_cow_entries_copied
    );
    eprintln!("  run.env_max_size: {}", stats.env_max_size);
    eprintln!("  run.apply_value: {}", stats.apply_value_calls);
    eprintln!("  run.apply_marked: {}", stats.apply_marked_calls);
    eprintln!("  run.apply_primitive: {}", stats.apply_primitive_calls);
    eprintln!("  run.apply_constructor: {}", stats.apply_constructor_calls);
    eprintln!("  run.apply_closure: {}", stats.apply_closure_calls);
    eprintln!(
        "  run.apply_recursive_closure: {}",
        stats.apply_recursive_closure_calls
    );
    eprintln!("  run.apply_adapter: {}", stats.apply_adapter_calls);
    eprintln!(
        "  run.apply_forced_thunk: {}",
        stats.apply_forced_thunk_calls
    );
    eprintln!("  run.apply_effect_op: {}", stats.apply_effect_op_calls);
    eprintln!(
        "  run.apply_continuation: {}",
        stats.apply_continuation_calls
    );
    eprintln!(
        "  run.primitive_zero_arity: {}",
        stats.primitive_zero_arity_calls
    );
    eprintln!("  run.primitive_apply: {}", stats.primitive_apply_calls);
    eprintln!("  run.primitive_partial: {}", stats.primitive_apply_partial);
    eprintln!(
        "  run.primitive_complete: {}",
        stats.primitive_apply_complete
    );
    eprintln!("  run.force_thunk: {}", stats.force_thunk_calls);
    eprintln!("  run.force_marked: {}", stats.force_marked_calls);
    eprintln!("  run.force_expr: {}", stats.force_expr_calls);
    eprintln!("  run.force_value: {}", stats.force_value_calls);
    eprintln!("  run.force_effect: {}", stats.force_effect_calls);
    eprintln!(
        "  run.force_continuation: {}",
        stats.force_continuation_calls
    );
    eprintln!("  run.force_adapter: {}", stats.force_adapter_calls);
    eprintln!("  run.effect_requests: {}", stats.effect_requests);
    eprintln!("  run.host_requests: {}", stats.host_requests);
    eprintln!("  run.catch_matches: {}", stats.catch_request_matches);
    eprintln!("  run.marked_value_calls: {}", stats.marked_value_calls);
    eprintln!(
        "  run.marked_values_created: {}",
        stats.marked_values_created
    );
    eprintln!("  run.marked_values_reused: {}", stats.marked_values_reused);
    eprintln!(
        "  run.marked_values_skipped_empty: {}",
        stats.marked_values_skipped_empty
    );
    eprintln!(
        "  run.marked_values_skipped_pure: {}",
        stats.marked_values_skipped_pure
    );
    eprintln!("  run.continuations: {}", stats.continuations_stored);
    eprintln!(
        "  run.continuation_invocations: {}",
        stats.continuation_invocations
    );
    eprintln!(
        "  run.continuation_capture_clones: {}",
        stats.continuation_capture_clones
    );
    eprintln!(
        "  run.continuation_invoke_clones: {}",
        stats.continuation_invoke_clones
    );
    eprintln!(
        "  run.continuation_frames_observed: {}",
        stats.continuation_frames_observed
    );
    eprintln!(
        "  run.continuation_marker_scopes_observed: {}",
        stats.continuation_marker_scopes_observed
    );
    eprintln!(
        "  run.continuation_frames_cloned: {}",
        stats.continuation_frames_cloned
    );
    eprintln!(
        "  run.continuation_marker_scopes_cloned: {}",
        stats.continuation_marker_scopes_cloned
    );
    eprintln!(
        "  run.shared_frame_unwrap_clones: {}",
        stats.shared_frame_unwrap_clones
    );
    eprintln!(
        "  run.shared_frame_unwrap_apply_clones: {}",
        stats.shared_frame_unwrap_apply_clones
    );
    eprintln!(
        "  run.shared_frame_unwrap_direct_clones: {}",
        stats.shared_frame_unwrap_direct_clones
    );
    eprintln!(
        "  run.shared_frame_unwrap_data_clones: {}",
        stats.shared_frame_unwrap_data_clones
    );
    eprintln!(
        "  run.shared_frame_unwrap_case_clones: {}",
        stats.shared_frame_unwrap_case_clones
    );
    eprintln!(
        "  run.shared_frame_unwrap_catch_clones: {}",
        stats.shared_frame_unwrap_catch_clones
    );
    eprintln!(
        "  run.shared_frame_unwrap_block_clones: {}",
        stats.shared_frame_unwrap_block_clones
    );
    eprintln!(
        "  run.shared_frame_unwrap_bind_clones: {}",
        stats.shared_frame_unwrap_bind_clones
    );
    eprintln!(
        "  run.shared_frame_unwrap_refset_clones: {}",
        stats.shared_frame_unwrap_refset_clones
    );
    eprintln!("  run.frame_allocs: {}", stats.frame_allocs);
    eprintln!(
        "  run.max_continuation_frames: {}",
        stats.max_continuation_frames
    );
    eprintln!("  run.request_resume_steps: {}", stats.request_resume_steps);
    eprintln!("  run.continue_value: {}", stats.continue_with_values);
    eprintln!("  run.continue_request: {}", stats.continue_with_requests);
    eprintln!("  run.continue_bind_value: {}", stats.continue_bind_values);
    eprintln!(
        "  run.continue_bind_request: {}",
        stats.continue_bind_requests
    );
    eprintln!(
        "  run.continue_bind_result_value: {}",
        stats.continue_bind_result_values
    );
    eprintln!(
        "  run.continue_bind_result_request: {}",
        stats.continue_bind_result_requests
    );
    eprintln!(
        "  run.continue_value_bind_value: {}",
        stats.continue_value_bind_values
    );
    eprintln!(
        "  run.continue_value_bind_request: {}",
        stats.continue_value_bind_requests
    );
    eprintln!("  run.marker_frame_calls: {}", stats.marker_frame_calls);
    eprintln!("  run.marker_frame_empty: {}", stats.marker_frame_empty);
    eprintln!("  run.marker_frame_pushes: {}", stats.marker_frame_pushes);
    eprintln!(
        "  run.marker_frame_marker_entries: {}",
        stats.marker_frame_marker_entries
    );
    eprintln!(
        "  run.marker_frame_frame_entries: {}",
        stats.marker_frame_frame_entries
    );
    eprintln!(
        "  run.marker_frame_add_id_entries: {}",
        stats.marker_frame_add_id_entries
    );
    eprintln!(
        "  run.marker_frame_active_add_id_entries: {}",
        stats.marker_frame_active_add_id_entries
    );
    eprintln!("  run.marker_plan_pushes: {}", stats.marker_plan_pushes);
    eprintln!(
        "  run.marker_plan_reused_parent: {}",
        stats.marker_plan_reused_parent
    );
    eprintln!(
        "  run.marker_frame_value_closes: {}",
        stats.marker_frame_value_closes
    );
    eprintln!(
        "  run.marker_frame_request_closes: {}",
        stats.marker_frame_request_closes
    );
    eprintln!(
        "  run.marker_frame_resume_steps: {}",
        stats.marker_frame_resume_steps
    );
    eprintln!(
        "  run.marker_scope_frame_touches: {}",
        stats.marker_scope_frame_touches
    );
    eprintln!(
        "  run.marker_scope_consume_calls: {}",
        stats.marker_scope_consume_calls
    );
    eprintln!(
        "  run.marker_scope_consume_nonempty_calls: {}",
        stats.marker_scope_consume_nonempty_calls
    );
    eprintln!(
        "  run.marker_scope_consume_touches: {}",
        stats.marker_scope_consume_touches
    );
    eprintln!(
        "  run.marker_scope_close_calls: {}",
        stats.marker_scope_close_calls
    );
    eprintln!(
        "  run.marker_scope_close_pops: {}",
        stats.marker_scope_close_pops
    );
    eprintln!(
        "  run.marker_scope_request_closes: {}",
        stats.marker_scope_request_closes
    );
    eprintln!(
        "  run.marker_scope_extend_touches: {}",
        stats.marker_scope_extend_touches
    );
    eprintln!(
        "  run.marker_scope_request_close_touches: {}",
        stats.marker_scope_request_close_touches
    );
    eprintln!(
        "  run.marker_scope_max_depth: {}",
        stats.marker_scope_max_depth
    );
    eprintln!("  run.instance_eval: {}", stats.instance_eval_calls);
    eprintln!("  run.instance_hits: {}", stats.instance_cache_hits);
    eprintln!("  run.instance_misses: {}", stats.instance_cache_misses);
    eprintln!("  run.path_prefix_checks: {}", stats.path_prefix_checks);
    eprintln!("  run.path_prefix_segments: {}", stats.path_prefix_segments);
    eprintln!("  run.path_eq_checks: {}", stats.path_eq_checks);
    eprintln!("  run.path_eq_segments: {}", stats.path_eq_segments);
    eprintln!("  run.active_add_scans: {}", stats.active_add_id_scans);
    eprintln!(
        "  run.active_add_path_candidates: {}",
        stats.active_add_id_path_candidates
    );
    eprintln!(
        "  run.active_add_skipped_own_path: {}",
        stats.active_add_id_skipped_own_path
    );
    eprintln!(
        "  run.active_add_skipped_foreign_path: {}",
        stats.active_add_id_skipped_foreign_path
    );
    eprintln!(
        "  run.active_add_skipped_disabled_path: {}",
        stats.active_add_id_skipped_disabled_path
    );
    eprintln!(
        "  run.active_add_skipped_entry_except: {}",
        stats.active_add_id_skipped_entry_except
    );
    eprintln!(
        "  run.active_add_skipped_carried_duplicate: {}",
        stats.active_add_id_skipped_carried_duplicate
    );
    eprintln!(
        "  run.active_add_applied_direct: {}",
        stats.active_add_id_applied_direct
    );
    eprintln!(
        "  run.active_add_applied_carried: {}",
        stats.active_add_id_applied_carried
    );
    eprintln!("  run.active_frame_scans: {}", stats.active_frame_scans);
    eprintln!(
        "  run.scope_state_shadow_checks: {}",
        stats.scope_state_shadow_checks
    );
    eprintln!(
        "  run.scope_state_shadow_active_add_markers: {}",
        stats.scope_state_shadow_active_add_markers
    );
    eprintln!(
        "  run.scope_state_shadow_path_candidates: {}",
        stats.scope_state_shadow_path_candidates
    );
    eprintln!(
        "  run.scope_state_shadow_all_path_candidates: {}",
        stats.scope_state_shadow_all_path_candidates
    );
    eprintln!(
        "  run.scope_state_shadow_own_path_candidates: {}",
        stats.scope_state_shadow_own_path_candidates
    );
    eprintln!(
        "  run.scope_state_shadow_foreign_path_candidates: {}",
        stats.scope_state_shadow_foreign_path_candidates
    );
}

fn format_duration(duration: Duration) -> String {
    if duration.as_secs() > 0 {
        format!("{:.3}s", duration.as_secs_f64())
    } else if duration.as_millis() > 0 {
        format!("{:.1}ms", duration.as_secs_f64() * 1000.0)
    } else {
        format!("{}us", duration.as_micros())
    }
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
    build_poly_with_cache_timed(files, key, cache, None)
}

fn build_poly_with_cache_timed(
    files: Vec<yulang::CollectedSource>,
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
    mut timings: Option<&mut RuntimePhaseTimings>,
) -> yulang::BuildPolyOutput {
    if let Err(error) = yulang::cache::write_realm_resolution_artifacts(cache, &files) {
        eprintln!("warning: {error}");
    }
    match cache.read_poly_artifact(key) {
        Ok(Some(cached)) => {
            record_runtime_build_cache(&mut timings, RuntimeBuildCacheKind::PolyHit);
            yulang::BuildPolyOutput {
                arena: cached.arena,
                labels: cached.labels,
                file_count: cached.file_count,
                errors: cached.errors,
            }
        }
        Ok(None) => {
            match cache.read_compiled_unit_artifact(key) {
                Ok(Some(cached)) => {
                    record_runtime_build_cache(
                        &mut timings,
                        RuntimeBuildCacheKind::CompiledUnitHit,
                    );
                    return build_poly_from_compiled_unit_cache(cached, key, cache);
                }
                Ok(None) => {}
                Err(error) => eprintln!("warning: {error}"),
            }
            if let Some((output, cache_kind)) =
                build_poly_from_source_unit_prefix_cache(&files, key, cache)
            {
                record_runtime_build_cache(&mut timings, cache_kind);
                return output;
            }
            record_runtime_build_cache(&mut timings, RuntimeBuildCacheKind::FullMiss);
            let output = run_route_to_value(
                yulang::build_poly_and_compiled_unit_from_collected_sources(files.clone()),
            );
            if let Err(error) = cache.write_compiled_unit_artifact(key, &output.compiled_unit) {
                eprintln!("warning: {error}");
            }
            write_source_unit_closure_artifacts(&files, cache);
            let poly = output.poly;
            let artifact = yulang::cache::CachedPolyArtifact {
                arena: poly.arena,
                labels: poly.labels,
                file_count: poly.file_count,
                errors: poly.errors,
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
            record_runtime_build_cache(&mut timings, RuntimeBuildCacheKind::ErrorFallback);
            run_route_to_value(yulang::build_poly_from_collected_sources(files))
        }
    }
}

fn build_poly_from_source_unit_prefix_cache(
    files: &[yulang::CollectedSource],
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
) -> Option<(yulang::BuildPolyOutput, RuntimeBuildCacheKind)> {
    if source_set_contains_std(files) {
        return build_poly_from_std_prefix_cache(files, key, cache);
    }
    let units = yulang::source_compilation_units(files);
    let cached = match cache.read_source_unit_compiled_artifacts(files, &units) {
        Ok(cached) => cached,
        Err(error) => {
            eprintln!("warning: {error}");
            return None;
        }
    };
    let candidates = select_source_unit_prefix_candidates(files, &units, &cached);
    if let Some(output) =
        build_poly_from_merged_source_unit_prefix_cache(files, key, cache, &candidates)
    {
        return Some((output, RuntimeBuildCacheKind::MergedSourceUnitPrefixHit));
    }
    let prefix = candidates
        .iter()
        .max_by_key(|candidate| (candidate.covered_files.len(), candidate.unit))?;
    build_poly_from_compiled_source_unit_prefix(
        files,
        key,
        cache,
        &prefix.covered_files,
        prefix.artifact.clone(),
    )
    .map(|output| (output, RuntimeBuildCacheKind::SourceUnitPrefixHit))
}

fn build_poly_from_std_prefix_cache(
    files: &[yulang::CollectedSource],
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
) -> Option<(yulang::BuildPolyOutput, RuntimeBuildCacheKind)> {
    let plan = std_prefix_cache_plan(files)?;
    let (prefix, kind) = match cache.read_compiled_unit_artifact(plan.key) {
        Ok(Some(prefix)) if prefix.errors.is_empty() => {
            (prefix, RuntimeBuildCacheKind::StdPrefixHit)
        }
        Ok(Some(_)) | Ok(None) => (
            build_std_prefix_artifact(files, cache, &plan)?,
            RuntimeBuildCacheKind::StdPrefixBuild,
        ),
        Err(error) => {
            eprintln!("warning: {error}");
            (
                build_std_prefix_artifact(files, cache, &plan)?,
                RuntimeBuildCacheKind::StdPrefixBuild,
            )
        }
    };
    build_poly_from_compiled_source_unit_prefix(files, key, cache, &plan.file_indices, prefix)
        .map(|output| (output, kind))
}

#[derive(Clone)]
struct SourceUnitPrefixCandidate {
    unit: usize,
    artifact: yulang::cache::CachedCompiledUnitArtifact,
    covered_files: Vec<usize>,
}

fn select_source_unit_prefix_candidates(
    files: &[yulang::CollectedSource],
    units: &yulang::SourceCompilationUnits,
    cached: &yulang::cache::CachedSourceUnitCompiledArtifacts,
) -> Vec<SourceUnitPrefixCandidate> {
    let root_unit = units.unit_for_file(0);
    let mut candidates = cached
        .selection
        .cached_units
        .iter()
        .copied()
        .filter(|unit| Some(*unit) != root_unit)
        .filter_map(|unit| {
            let artifact = cached.artifacts.get(unit)?.as_ref()?.clone();
            let covered_files =
                yulang::source::source_unit_closure_file_indices(units, unit).ok()?;
            if covered_files.is_empty() || covered_files.iter().any(|file| *file >= files.len()) {
                return None;
            }
            Some(SourceUnitPrefixCandidate {
                unit,
                artifact,
                covered_files,
            })
        })
        .collect::<Vec<_>>();

    candidates.sort_by(|left, right| {
        right
            .covered_files
            .len()
            .cmp(&left.covered_files.len())
            .then_with(|| right.unit.cmp(&left.unit))
    });

    let mut covered = vec![false; files.len()];
    let mut selected = Vec::new();
    for candidate in candidates {
        if candidate.covered_files.iter().any(|file| covered[*file]) {
            continue;
        }
        for file in &candidate.covered_files {
            covered[*file] = true;
        }
        selected.push(candidate);
    }
    selected.sort_by_key(|candidate| {
        candidate
            .covered_files
            .first()
            .copied()
            .unwrap_or(usize::MAX)
    });
    selected
}

fn build_poly_from_merged_source_unit_prefix_cache(
    files: &[yulang::CollectedSource],
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
    candidates: &[SourceUnitPrefixCandidate],
) -> Option<yulang::BuildPolyOutput> {
    if candidates.len() < 2 {
        return None;
    }
    let mut artifacts = Vec::with_capacity(candidates.len());
    let mut covered_files = Vec::new();
    for candidate in candidates {
        artifacts.push(candidate.artifact.clone());
        covered_files.extend(candidate.covered_files.iter().copied());
    }
    covered_files.sort_unstable();
    covered_files.dedup();
    let prefix_key = yulang::cache::merged_compiled_unit_artifact_key(&artifacts).ok();
    let prefix = prefix_key
        .and_then(|key| match cache.read_compiled_unit_artifact(key) {
            Ok(cached) => cached,
            Err(error) => {
                eprintln!("warning: {error}");
                None
            }
        })
        .or_else(|| {
            let prefix = match yulang::cache::merge_compiled_unit_artifacts(artifacts) {
                Ok(prefix) => prefix,
                Err(_) => return None,
            };
            if let Err(error) = cache.write_compiled_unit_artifact(prefix.cache_key(), &prefix) {
                eprintln!("warning: {error}");
            }
            Some(prefix)
        })?;
    build_poly_from_compiled_source_unit_prefix(files, key, cache, &covered_files, prefix)
}

fn build_poly_from_compiled_source_unit_prefix(
    files: &[yulang::CollectedSource],
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
    prefix_file_indices: &[usize],
    prefix: yulang::cache::CachedCompiledUnitArtifact,
) -> Option<yulang::BuildPolyOutput> {
    let mut prefix_files = vec![false; files.len()];
    for file in prefix_file_indices {
        prefix_files[*file] = true;
    }
    let suffix = files
        .iter()
        .enumerate()
        .filter_map(|(file, source)| (!prefix_files[file]).then_some(source.clone()))
        .collect::<Vec<_>>();
    let output =
        match yulang::build_poly_and_compiled_unit_from_compiled_unit_prefix_and_collected_sources(
            prefix,
            files.to_vec(),
            suffix,
        ) {
            Ok(output) => output,
            Err(error) => {
                eprintln!("warning: {error}");
                return None;
            }
        };
    if let Err(error) = cache.write_compiled_unit_artifact(key, &output.compiled_unit) {
        eprintln!("warning: {error}");
    }
    Some(write_poly_artifact_from_output(output.poly, key, cache))
}

fn write_source_unit_closure_artifacts(
    files: &[yulang::CollectedSource],
    cache: &yulang::cache::ArtifactCache,
) {
    if source_set_contains_std(files) {
        return;
    }

    let units = yulang::source_compilation_units(files);
    let keys = yulang::cache::source_compilation_unit_cache_keys(files, &units);
    for unit in 0..units.units.len() {
        if units.unit_for_file(0) == Some(unit) {
            continue;
        }
        match yulang::cache::compiled_unit_artifact_from_source_unit_closure(files, &units, unit) {
            Ok(artifact) => {
                if let Err(error) = cache.write_compiled_unit_artifact(keys[unit], &artifact) {
                    eprintln!("warning: {error}");
                }
            }
            Err(error) => eprintln!("warning: {error:?}"),
        }
    }
}

struct StdPrefixCachePlan {
    file_indices: Vec<usize>,
    key: yulang::cache::SourceCacheKey,
}

fn build_std_prefix_artifact(
    files: &[yulang::CollectedSource],
    cache: &yulang::cache::ArtifactCache,
    plan: &StdPrefixCachePlan,
) -> Option<yulang::cache::CachedCompiledUnitArtifact> {
    let prefix_files = plan
        .file_indices
        .iter()
        .map(|file| files[*file].clone())
        .collect::<Vec<_>>();
    let loaded = sources::load(std_prefix_lowering_source_files(files, &plan.file_indices));
    let artifact = match yulang::cache::compiled_unit_artifact_from_loaded_files_with_key(
        &prefix_files,
        &loaded,
        plan.key,
    ) {
        Ok(artifact) => artifact,
        Err(error) => {
            eprintln!("warning: {error}");
            return None;
        }
    };
    if !artifact.errors.is_empty() {
        return None;
    }
    if let Err(error) = cache.write_compiled_unit_artifact(plan.key, &artifact) {
        eprintln!("warning: {error}");
    }
    Some(artifact)
}

fn std_prefix_cache_plan(files: &[yulang::CollectedSource]) -> Option<StdPrefixCachePlan> {
    let units = yulang::source_compilation_units(files);
    let std_root_file = files
        .iter()
        .position(|file| is_std_root_module_path(&file.module_path))?;
    let unit = units.unit_for_file(std_root_file)?;
    let file_indices = yulang::source::source_unit_closure_file_indices(&units, unit).ok()?;
    if file_indices.is_empty()
        || file_indices
            .iter()
            .any(|file| !is_std_module_path(&files[*file].module_path))
    {
        return None;
    }
    let key = yulang::cache::source_cache_key(&std_prefix_cache_key_sources(files, &file_indices));
    Some(StdPrefixCachePlan { file_indices, key })
}

fn std_prefix_cache_key_sources(
    files: &[yulang::CollectedSource],
    file_indices: &[usize],
) -> Vec<yulang::CollectedSource> {
    let mut cache_sources = Vec::with_capacity(file_indices.len() + 1);
    cache_sources.push(std_prefix_root_collected_source());
    cache_sources.extend(file_indices.iter().map(|file| files[*file].clone()));
    cache_sources
}

fn std_prefix_lowering_source_files(
    files: &[yulang::CollectedSource],
    file_indices: &[usize],
) -> Vec<sources::SourceFile> {
    let mut source_files = Vec::with_capacity(file_indices.len() + 1);
    source_files.push(sources::SourceFile {
        module_path: sources::Path::default(),
        source: std_prefix_root_source(),
    });
    source_files.extend(file_indices.iter().map(|file| sources::SourceFile {
        module_path: files[*file].module_path.clone(),
        source: files[*file].source.clone(),
    }));
    source_files
}

fn std_prefix_root_collected_source() -> yulang::CollectedSource {
    yulang::CollectedSource::new(
        PathBuf::from("<std-prefix-root>"),
        sources::Path::default(),
        std_prefix_root_source(),
    )
}

fn std_prefix_root_source() -> String {
    format!("{}mod std;\n", yulang::IMPLICIT_PRELUDE_IMPORT)
}

fn is_std_root_module_path(path: &sources::Path) -> bool {
    path.segments.len() == 1 && path.segments[0].0 == "std"
}

fn build_poly_from_compiled_unit_cache(
    cached: yulang::cache::CachedCompiledUnitArtifact,
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
) -> yulang::BuildPolyOutput {
    let poly = yulang::build_poly_from_compiled_unit_artifact(cached);
    write_poly_artifact_from_output(poly, key, cache)
}

fn write_poly_artifact_from_output(
    poly: yulang::BuildPolyOutput,
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
) -> yulang::BuildPolyOutput {
    let artifact = yulang::cache::CachedPolyArtifact {
        arena: poly.arena,
        labels: poly.labels,
        file_count: poly.file_count,
        errors: poly.errors,
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

fn source_set_contains_std(files: &[yulang::CollectedSource]) -> bool {
    files
        .iter()
        .any(|file| is_std_module_path(&file.module_path))
}

fn is_std_module_path(path: &sources::Path) -> bool {
    path.segments.first().is_some_and(|name| name.0 == "std")
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
    let mono_cache = mono_cache_for_files(&files, use_cache);
    let output = build_poly_with_optional_cache(files, use_cache);
    let program = specialize_mono_program(
        &output,
        mono_cache.as_ref().map(|(cache, key)| (cache, *key)),
    );
    yulang::DumpMonoOutput {
        text: specialize::mono::dump::dump_program(&program),
        file_count: output.file_count,
        errors: output.errors,
    }
}

fn dump_control_evidence_with_optional_cache(
    files: Vec<yulang::CollectedSource>,
    use_cache: bool,
) -> yulang::DumpMonoOutput {
    let output = build_control_with_optional_cache(files, use_cache);
    let evidence = control_vm::ControlEvidenceProgram::from_program(&output.program);
    let mut text = control_vm::format_control_evidence_program(&evidence);
    text.push('\n');
    text.push_str(&specialize::format_runtime_evidence_surface(
        &output.runtime_evidence,
    ));
    yulang::DumpMonoOutput {
        text,
        file_count: output.file_count,
        errors: output.errors,
    }
}

fn dump_evidence_vm_plan_with_optional_cache(
    files: Vec<yulang::CollectedSource>,
    use_cache: bool,
) -> yulang::DumpMonoOutput {
    let output = build_control_with_optional_cache(files, use_cache);
    let plan = evidence_vm::build_plan(&output.program, &output.runtime_evidence);
    yulang::DumpMonoOutput {
        text: evidence_vm::format_plan(&plan),
        file_count: output.file_count,
        errors: output.errors,
    }
}

fn run_mono_with_optional_cache(
    files: Vec<yulang::CollectedSource>,
    use_cache: bool,
) -> yulang::RunMonoOutput {
    let mono_cache = mono_cache_for_files(&files, use_cache);
    let output = build_poly_with_optional_cache(files, use_cache);
    let program = specialize_mono_program(
        &output,
        mono_cache.as_ref().map(|(cache, key)| (cache, *key)),
    );
    let values = match mono_runtime::run_program(&program) {
        Ok(values) => values,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    yulang::RunMonoOutput {
        text: yulang::format_run_mono_values_with_labels(&values, Some(&output.labels)),
        file_count: output.file_count,
        errors: output.errors,
        values,
    }
}

fn mono_cache_for_files(
    files: &[yulang::CollectedSource],
    use_cache: bool,
) -> Option<(yulang::cache::ArtifactCache, yulang::cache::SourceCacheKey)> {
    use_cache.then(|| {
        (
            yulang::cache::ArtifactCache::new(yulang::stdlib::default_user_cache_root()),
            yulang::cache::source_cache_key(files),
        )
    })
}

fn run_compatible_dump(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let (path, selection) = parse_dump_args(program, args);
    print_cst_if_requested(options, &path);
    if options.no_prelude {
        print_selected_dump_without_std(path, selection, options.use_cache);
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
        Some("stats") => {
            if let Err(error) = print_cache_stats(&root) {
                eprintln!("failed to inspect cache {}: {error}", root.display());
                process::exit(1);
            }
        }
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

fn print_cache_stats(root: &PathBuf) -> io::Result<()> {
    println!("cache: {}", root.display());
    for stage in ["control-vm", "mono", "poly", "compiled-unit"] {
        println!("{stage}: {}", cache_stage_file_count(root, stage)?);
    }
    println!("realm-resolution: {}", realm_resolution_file_count(root)?);
    Ok(())
}

fn cache_stage_file_count(root: &PathBuf, stage: &str) -> io::Result<usize> {
    let dir = root.join("artifacts").join(stage);
    match fs::read_dir(dir) {
        Ok(entries) => {
            let mut count = 0;
            for entry in entries {
                if entry?.path().is_file() {
                    count += 1;
                }
            }
            Ok(count)
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(0),
        Err(error) => Err(error),
    }
}

fn realm_resolution_file_count(root: &PathBuf) -> io::Result<usize> {
    let realms = root.join("realms");
    let entries = match fs::read_dir(realms) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(0),
        Err(error) => return Err(error),
    };
    let mut count = 0;
    for entry in entries {
        let resolution_dir = entry?.path().join("resolution");
        match fs::read_dir(resolution_dir) {
            Ok(files) => {
                for file in files {
                    if file?.path().is_file() {
                        count += 1;
                    }
                }
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    Ok(count)
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
        Some("install") => {
            let (path, version) = parse_realm_install_args(program, args);
            let root = path.unwrap_or_else(|| PathBuf::from("."));
            match yulang::install_local_realm(&root, version) {
                Ok(output) => {
                    let status = if output.already_installed {
                        "already installed"
                    } else {
                        "installed"
                    };
                    println!(
                        "realm install: {status} {} hash={:016x} files={}",
                        output.installed_root.display(),
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

fn run_runtime_evidence_bench(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let (path, repeat) = parse_runtime_evidence_bench_args(program, args);
    println!("runtime evidence bench:");
    println!("  case: {}", path.display());
    println!("  repeat: {repeat}");

    for iteration in 1..=repeat {
        let total_start = Instant::now();
        let mut timings = RuntimePhaseTimings::default();
        let collect_start = Instant::now();
        let files = collect_control_sources_or_exit(&path, options);
        timings.collect = collect_start.elapsed();
        let output =
            build_control_with_optional_cache_timed(files, options.use_cache, Some(&mut timings));
        timings.total = total_start.elapsed();
        print_runtime_evidence_bench_iteration(iteration, &timings, &output);
    }
}

fn parse_runtime_evidence_bench_args(
    program: &str,
    mut args: VecDeque<OsString>,
) -> (PathBuf, usize) {
    let mut path = None;
    let mut repeat = 1usize;

    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--repeat") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(
                        program,
                        "debug runtime-evidence-bench --repeat requires a value",
                    );
                };
                repeat = parse_runtime_evidence_bench_repeat(program, &value);
            }
            Some(value) if value.starts_with("--repeat=") => {
                repeat =
                    parse_runtime_evidence_bench_repeat_str(program, &value["--repeat=".len()..]);
            }
            Some(value) if value.starts_with("--") => {
                print_usage_error_and_exit(
                    program,
                    &format!("unknown debug runtime-evidence-bench option: {value}"),
                );
            }
            _ => {
                if path.is_some() {
                    print_usage_error_and_exit(
                        program,
                        "debug runtime-evidence-bench takes exactly one path",
                    );
                }
                path = Some(PathBuf::from(arg));
            }
        }
    }

    let Some(path) = path else {
        print_usage_error_and_exit(program, "debug runtime-evidence-bench requires a path");
    };
    if repeat == 0 {
        print_usage_error_and_exit(
            program,
            "debug runtime-evidence-bench --repeat must be >= 1",
        );
    }
    (path, repeat)
}

fn parse_runtime_evidence_bench_repeat(program: &str, value: &OsString) -> usize {
    let Some(value) = value.to_str() else {
        print_usage_error_and_exit(
            program,
            "debug runtime-evidence-bench --repeat must be valid UTF-8",
        );
    };
    parse_runtime_evidence_bench_repeat_str(program, value)
}

fn parse_runtime_evidence_bench_repeat_str(program: &str, value: &str) -> usize {
    match value.parse::<usize>() {
        Ok(repeat) => repeat,
        Err(_) => print_usage_error_and_exit(
            program,
            "debug runtime-evidence-bench --repeat must be an integer",
        ),
    }
}

fn print_runtime_evidence_bench_iteration(
    iteration: usize,
    timings: &RuntimePhaseTimings,
    output: &yulang::BuildControlOutput,
) {
    let summary = RuntimeEvidenceBenchSummary::from_surface(&output.runtime_evidence);
    println!("iteration {iteration}:");
    println!("  bench.cache: {}", timings.build_cache.as_str());
    println!("  bench.collect: {}", format_duration(timings.collect));
    println!(
        "  bench.build_poly: {}",
        format_duration(timings.build_poly)
    );
    println!(
        "  bench.specialize: {}",
        format_duration(timings.specialize)
    );
    println!(
        "  bench.control_lower: {}",
        format_duration(timings.control_lower)
    );
    println!("  bench.total: {}", format_duration(timings.total));
    println!("  evidence.tasks: {}", summary.tasks);
    println!("  evidence.graph_slots: {}", summary.graph_slots);
    println!(
        "  evidence.graph_weighted_constraints: {}",
        summary.graph_weighted_constraints
    );
    println!(
        "  evidence.graph_weighted_edges: {}",
        summary.graph_weighted_edges
    );
    println!(
        "  evidence.graph_effect_subtractions: {}",
        summary.graph_effect_subtractions
    );
    println!(
        "  evidence.graph_row_residuals: {}",
        summary.graph_row_residuals
    );
    println!("  evidence.nodes: {}", summary.nodes);
    println!("  evidence.node_slots: {}", summary.node_slots);
    println!(
        "  evidence.node_weighted_slots: {}",
        summary.node_weighted_slots
    );
    println!(
        "  evidence.node_effect_subtraction_slots: {}",
        summary.node_effect_subtraction_slots
    );
    println!(
        "  evidence.node_evidence_refs: {}",
        summary.node_evidence_refs
    );
    println!("  evidence.sites: {}", summary.sites);
    println!("  evidence.expr_types: {}", summary.expr_types);
    println!(
        "  evidence.expr_stack_weights: {}",
        summary.expr_stack_weights
    );
    println!("  evidence.ref_signatures: {}", summary.ref_signatures);
    println!(
        "  evidence.select_signatures: {}",
        summary.select_signatures
    );
    println!(
        "  evidence.pat_ref_signatures: {}",
        summary.pat_ref_signatures
    );
    println!(
        "  evidence.typeclass_resolutions: {}",
        summary.typeclass_resolutions
    );
    println!(
        "  evidence.type_stack_weights: {}",
        summary.type_stack_weights
    );
    println!(
        "  evidence.raw_thunk_computations: {}",
        summary.raw_thunk_computations
    );
}

fn run_runtime_evidence_run(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let total_start = Instant::now();
    let args = parse_runtime_evidence_run_args(program, args);
    let files = collect_control_sources_or_exit(&args.path, options);
    let build = build_control_with_optional_cache(files, options.use_cache);
    let summary = RuntimeEvidenceBenchSummary::from_surface(&build.runtime_evidence);
    let run_start = Instant::now();
    let output = match evidence_vm::run_program(&build.program) {
        Ok(output) => output,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    let runtime_evidence_execute = run_start.elapsed();
    let format_start = Instant::now();
    let roots_text = output.roots_text_with_labels(Some(&build.labels));
    let root_format = format_start.elapsed();
    let total = total_start.elapsed();

    println!("runtime evidence run:");
    println!("  evidence.tasks: {}", summary.tasks);
    println!("  evidence.nodes: {}", summary.nodes);
    println!(
        "  evidence.node_evidence_refs: {}",
        summary.node_evidence_refs
    );
    println!(
        "  control_evidence.effect_calls: {}",
        output.evidence_stats.effect_calls
    );
    println!(
        "  control_evidence.direct_effect_calls: {}",
        output.evidence_stats.direct_effect_calls
    );
    println!(
        "  runtime_evidence.expr_evals: {}",
        output.evidence_stats.expr_evals
    );
    println!(
        "  runtime_evidence.env_clones: {}",
        output.evidence_stats.env_clones
    );
    println!(
        "  runtime_evidence.env_entries_cloned: {}",
        output.evidence_stats.env_entries_cloned
    );
    println!(
        "  runtime_evidence.apply_value_calls: {}",
        output.evidence_stats.apply_value_calls
    );
    println!(
        "  runtime_evidence.apply_adapter_calls: {}",
        output.evidence_stats.apply_adapter_calls
    );
    println!(
        "  runtime_evidence.adapt_value_calls: {}",
        output.evidence_stats.adapt_value_calls
    );
    println!(
        "  runtime_evidence.primitive_apply_calls: {}",
        output.evidence_stats.primitive_apply_calls
    );
    println!(
        "  runtime_evidence.thunk_forces: {}",
        output.evidence_stats.thunk_forces
    );
    println!(
        "  runtime_evidence.thunk_force_expr: {}",
        output.evidence_stats.thunk_force_expr
    );
    println!(
        "  runtime_evidence.thunk_force_effect: {}",
        output.evidence_stats.thunk_force_effect
    );
    println!(
        "  runtime_evidence.thunk_force_continuation: {}",
        output.evidence_stats.thunk_force_continuation
    );
    println!(
        "  runtime_evidence.thunk_force_value: {}",
        output.evidence_stats.thunk_force_value
    );
    println!(
        "  runtime_evidence.thunk_force_adapter: {}",
        output.evidence_stats.thunk_force_adapter
    );
    println!(
        "  runtime_evidence.continuation_appends: {}",
        output.evidence_stats.continuation_appends
    );
    println!(
        "  runtime_evidence.continuation_append_steps: {}",
        output.evidence_stats.continuation_append_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_steps: {}",
        output.evidence_stats.continuation_resume_steps
    );
    println!(
        "  runtime_evidence.request_continuation_steps: {}",
        output.evidence_stats.request_continuation_steps
    );
    println!(
        "  runtime_evidence.catch_body_checks: {}",
        output.evidence_stats.catch_body_checks
    );
    println!(
        "  runtime_evidence.marker_frame_entries: {}",
        output.evidence_stats.marker_frame_entries
    );
    println!(
        "  runtime_evidence.marker_frame_markers: {}",
        output.evidence_stats.marker_frame_markers
    );
    println!(
        "  runtime_evidence.active_marker_plan_pushes: {}",
        output.evidence_stats.active_marker_plan_pushes
    );
    println!(
        "  runtime_evidence.active_marker_plan_dedupes: {}",
        output.evidence_stats.active_marker_plan_dedupes
    );
    println!(
        "  runtime_evidence.active_add_id_scans: {}",
        output.evidence_stats.active_add_id_scans
    );
    println!(
        "  runtime_evidence.active_add_id_path_candidates: {}",
        output.evidence_stats.active_add_id_path_candidates
    );
    println!(
        "  runtime_evidence.active_add_id_path_rejects: {}",
        output.evidence_stats.active_add_id_path_rejects
    );
    println!(
        "  runtime_evidence.active_add_id_entry_except_rejects: {}",
        output.evidence_stats.active_add_id_entry_except_rejects
    );
    println!(
        "  runtime_evidence.active_add_id_already_carried_rejects: {}",
        output.evidence_stats.active_add_id_already_carried_rejects
    );
    println!(
        "  runtime_evidence.active_add_id_hits: {}",
        output.evidence_stats.active_add_id_hits
    );
    println!(
        "  runtime_evidence.function_call_marker_plans: {}",
        output.evidence_stats.function_call_marker_plans
    );
    println!(
        "  runtime_evidence.function_call_marker_inputs: {}",
        output.evidence_stats.function_call_marker_inputs
    );
    println!(
        "  runtime_evidence.function_call_marker_outputs: {}",
        output.evidence_stats.function_call_marker_outputs
    );
    println!(
        "  runtime_evidence.list_merge_calls: {}",
        output.evidence_stats.list_merge_calls
    );
    println!(
        "  runtime_evidence.list_view_raw_calls: {}",
        output.evidence_stats.list_view_raw_calls
    );
    println!(
        "  runtime_evidence.list_values_copied: {}",
        output.evidence_stats.list_values_copied
    );
    println!(
        "  timing.runtime_evidence_execute: {}",
        format_duration(runtime_evidence_execute)
    );
    println!("  timing.root_format: {}", format_duration(root_format));
    println!("  timing.total_before_compare: {}", format_duration(total));

    if args.compare_control {
        let control = run_built_control_for_cli(build);
        if !control.errors.is_empty() {
            for error in &control.errors {
                eprintln!("error: {error}");
            }
            process::exit(1);
        }
        if output.stdout != control.stdout {
            eprintln!("runtime-evidence-run compare-control stdout mismatch");
            eprintln!("expected stdout:\n{}", control.stdout);
            eprintln!("actual stdout:\n{}", output.stdout);
            process::exit(1);
        }
        if roots_text != control.text {
            eprintln!("runtime-evidence-run compare-control mismatch");
            eprintln!("expected:\n{}", control.text);
            eprintln!("actual:\n{roots_text}");
            process::exit(1);
        }
        println!("  compare.control: match");
    }

    print!("{}", output.stdout);
    print!("{roots_text}");
}

fn parse_runtime_evidence_run_args(
    program: &str,
    mut args: VecDeque<OsString>,
) -> RuntimeEvidenceRunArgs {
    let mut path = None;
    let mut compare_control = false;

    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--compare-control") => compare_control = true,
            Some(value) if value.starts_with("--") => {
                print_usage_error_and_exit(
                    program,
                    &format!("unknown debug runtime-evidence-run option: {value}"),
                );
            }
            _ => {
                if path.is_some() {
                    print_usage_error_and_exit(
                        program,
                        "debug runtime-evidence-run takes exactly one path",
                    );
                }
                path = Some(PathBuf::from(arg));
            }
        }
    }

    let Some(path) = path else {
        print_usage_error_and_exit(program, "debug runtime-evidence-run requires a path");
    };
    RuntimeEvidenceRunArgs {
        path,
        compare_control,
    }
}

fn run_debug(program: &str, options: &GlobalOptions, mut args: VecDeque<OsString>) {
    let Some(op) = args.pop_front() else {
        print_usage_and_exit(program);
    };
    match op.to_str() {
        Some("control-vm") => run_compatible_run(program, options, args),
        Some("control-vm-emit") => run_compatible_build(program, options, args),
        Some("runtime-evidence-bench") => run_runtime_evidence_bench(program, options, args),
        Some("runtime-evidence-run") => run_runtime_evidence_run(program, options, args),
        Some("evidence-vm-plan") => {
            let path = require_one_path(program, args);
            let files = collect_control_sources_or_exit(&path, options);
            let output = dump_evidence_vm_plan_with_optional_cache(files, options.use_cache);
            print_dump_mono_output(&output);
        }
        Some("control-vm-load") => {
            let (path, selection) = parse_run_path_args(program, args);
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

fn parse_realm_install_args(
    program: &str,
    mut args: VecDeque<OsString>,
) -> (Option<PathBuf>, Option<String>) {
    let mut path = None;
    let mut version = None;
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--version") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "realm install --version requires a value");
                };
                set_realm_version(program, &mut version, value);
            }
            Some(value) if value.starts_with("--version=") => {
                let value = value.strip_prefix("--version=").unwrap_or_default();
                if value.is_empty() {
                    print_usage_error_and_exit(program, "realm install --version requires a value");
                }
                set_realm_version(program, &mut version, OsString::from(value));
            }
            Some(flag) if flag.starts_with("--") => {
                print_usage_error_and_exit(
                    program,
                    &format!("unsupported realm install option {flag}"),
                );
            }
            _ => set_single_path(program, &mut path, arg),
        }
    }
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
