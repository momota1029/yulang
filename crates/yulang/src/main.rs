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
            run_route(yulang::dump_mono_from_entry(path), print_dump_mono_output);
        }
        Some("run-mono") => {
            let path = require_one_path(&program, args);
            run_route(yulang::run_mono_from_entry(path), print_run_mono_output);
        }
        Some("run-control") => {
            let path = require_one_path(&program, args);
            let build = run_route_to_value(yulang::build_control_from_entry(path));
            let output = run_built_control_for_cli(build);
            print_cli_control_run_output(&output);
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
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct RunSelection {
    interpreter: bool,
    print_roots: bool,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct RuntimePhaseTimings {
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

    let mut timings = RuntimePhaseTimings::default();
    let total_start = Instant::now();
    let collect_start = Instant::now();
    let files = collect_control_sources_or_exit(&path, options);
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
    build_control_with_optional_cache_timed(files, use_cache, None)
}

fn build_control_with_optional_cache_timed(
    files: Vec<yulang::CollectedSource>,
    use_cache: bool,
    timings: Option<&mut RuntimePhaseTimings>,
) -> yulang::BuildControlOutput {
    if !use_cache {
        if let Some(timings) = timings {
            return build_control_without_cache_timed(files, timings);
        }
        return run_route_to_value(yulang::build_control_from_collected_sources(files));
    }

    let key = yulang::cache::source_cache_key(&files);
    let cache = yulang::cache::ArtifactCache::new(yulang::stdlib::default_user_cache_root());
    match cache.read_control_artifact(key) {
        Ok(Some(cached)) => {
            return yulang::BuildControlOutput {
                program: cached.program,
                labels: cached.labels,
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

    let specialize_start = Instant::now();
    let mono = match specialize::specialize(&poly.arena) {
        Ok(program) => program,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    timings.specialize = specialize_start.elapsed();

    let control_lower_start = Instant::now();
    let program = match control_vm::lower(&mono) {
        Ok(program) => program,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    timings.control_lower = control_lower_start.elapsed();

    yulang::BuildControlOutput {
        program,
        labels: poly.labels,
        file_count: poly.file_count,
        errors: poly.errors,
    }
}

fn print_runtime_phase_timings(timing: &RuntimePhaseTimings, stats: &control_vm::RuntimeStats) {
    eprintln!("runtime timing:");
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
        "  run.marker_scope_consume_touches: {}",
        stats.marker_scope_consume_touches
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
    eprintln!("  run.active_frame_scans: {}", stats.active_frame_scans);
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
    match cache.read_poly_artifact(key) {
        Ok(Some(cached)) => yulang::BuildPolyOutput {
            arena: cached.arena,
            labels: cached.labels,
            file_count: cached.file_count,
            errors: cached.errors,
        },
        Ok(None) => {
            match cache.read_compiled_unit_artifact(key) {
                Ok(Some(cached)) => {
                    return build_poly_from_compiled_unit_cache(cached, key, cache);
                }
                Ok(None) => {}
                Err(error) => eprintln!("warning: {error}"),
            }
            let output = run_route_to_value(
                yulang::build_poly_and_compiled_unit_from_collected_sources(files),
            );
            if let Err(error) = cache.write_compiled_unit_artifact(key, &output.compiled_unit) {
                eprintln!("warning: {error}");
            }
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
            run_route_to_value(yulang::build_poly_from_collected_sources(files))
        }
    }
}

fn build_poly_from_compiled_unit_cache(
    cached: yulang::cache::CachedCompiledUnitArtifact,
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
) -> yulang::BuildPolyOutput {
    let artifact = yulang::cache::CachedPolyArtifact {
        arena: cached.runtime.arena,
        labels: cached.runtime.labels,
        file_count: cached.manifest.files.len(),
        errors: cached.errors,
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
        text: yulang::format_run_mono_values_with_labels(&values, Some(&output.labels)),
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
