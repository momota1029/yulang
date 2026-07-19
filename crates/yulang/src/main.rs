use std::collections::VecDeque;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;
use std::process;
use std::time::{Duration, Instant};

mod contract;
mod cst_view;
mod parse_view;
mod runtime_evidence_debug;
mod std_prefix_cache_safety;
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

    let run_command = || match command.to_str() {
        Some("check") => run_compatible_check(&program, &options, args),
        Some("contract") => contract::run(&program, options.std_root.clone(), args),
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
    };
    let run_with_generalize_role_snapshot_mode = || {
        // Keep the existing always-solve spelling as the default-confirming control. If both
        // controls are present, always-solve wins rather than weakening its established meaning.
        if options.generalize_role_snapshot_always_solve {
            infer::analysis::with_generalize_role_snapshot_always_solve_for_new_sessions(
                run_command,
            );
        } else if options.generalize_role_snapshot_enable_reuse {
            infer::analysis::with_generalize_role_snapshot_reuse_enabled_for_new_sessions(
                run_command,
            );
        } else {
            run_command();
        }
    };
    // Stage 7's explicitly named rollback/debug route selects always-solve mode. The retained
    // Stage 5 benchmark spelling is parsed below as a compatibility no-op.
    if options.owner_dirty_scheduler_always_solve {
        infer::analysis::with_owner_dirty_scheduler_disabled_for_new_sessions(
            run_with_generalize_role_snapshot_mode,
        );
    } else {
        run_with_generalize_role_snapshot_mode();
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GlobalOptions {
    std_root: Option<PathBuf>,
    no_prelude: bool,
    show_cst: bool,
    use_cache: bool,
    runtime_phase_timings: bool,
    owner_dirty_scheduler_always_solve: bool,
    generalize_role_snapshot_always_solve: bool,
    generalize_role_snapshot_enable_reuse: bool,
}

impl Default for GlobalOptions {
    fn default() -> Self {
        Self {
            std_root: None,
            no_prelude: false,
            show_cst: false,
            use_cache: true,
            runtime_phase_timings: false,
            owner_dirty_scheduler_always_solve: false,
            generalize_role_snapshot_always_solve: false,
            generalize_role_snapshot_enable_reuse: false,
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
    backend: RunBackend,
    backend_explicit: bool,
    host: RunHostMode,
    print_roots: bool,
    print_nth: bool,
    runtime_evidence_profile_deep: bool,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum RunBackend {
    #[default]
    EvidenceVm,
    Mono,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum RunHostMode {
    #[default]
    Native,
    Unsupported,
    MockServer,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct RuntimePhaseTimings {
    build_cache: RuntimeBuildCacheKind,
    std_prefix_boundary_entries: Option<usize>,
    std_prefix_cache_interface: Option<yulang::cache::CompiledUnitCacheInterfaceTelemetry>,
    role_resolution: Option<RuntimeRoleResolutionTelemetry>,
    collect: Duration,
    build_poly: Duration,
    specialize: Duration,
    control_lower: Duration,
    vm_eval: Duration,
    runtime_execute: Duration,
    root_format: Duration,
    total: Duration,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct RuntimeRoleResolutionTelemetry {
    total: Duration,
    generalize: Duration,
    methods: Duration,
    method_pass: Duration,
    method_taint: Duration,
    owner_dirty_skip: Duration,
    owner_dirty_owner_solve: Duration,
    owner_dirty_journal_drain: Duration,
    owner_dirty_method_taint_diff: Duration,
    whole_pass_skips: usize,
    clean_owner_skips: usize,
    dirty_solves: usize,
    full_fallbacks: usize,
    journal_bursts: usize,
    journal_mutations: usize,
    peak_journal_burst: usize,
    peak_owners: usize,
    peak_dependency_keys: usize,
    peak_dependencies_per_owner: usize,
    peak_reverse_edges: usize,
    peak_retained_bytes: usize,
    live_owners: usize,
    live_dependency_keys: usize,
    live_reverse_edges: usize,
    live_retained_bytes: usize,
    per_owner_cap_rejections: usize,
    global_cap_fallbacks: usize,
    demands: usize,
    candidate_scans: usize,
    candidate_matches: usize,
    prerequisite_demands: usize,
    prerequisite_candidate_scans: usize,
    prerequisite_candidate_matches: usize,
    candidate_cache_hits: usize,
    candidate_cache_misses: usize,
    exact_snapshot_hits: usize,
    exact_snapshot_full_solves: usize,
    exact_snapshot_misses: usize,
    exact_snapshot_cap_fallbacks: usize,
    exact_snapshot_peak_entries: usize,
    exact_snapshot_peak_retained_debug_bytes: usize,
}

impl RuntimeRoleResolutionTelemetry {
    fn from_lowering_timing(timing: infer::lowering::BodyLoweringTiming) -> Self {
        let analysis = timing.analysis;
        Self {
            total: analysis.generalize_resolve_roles + analysis.method_role_solve,
            generalize: analysis.generalize_resolve_roles,
            methods: analysis.method_role_solve,
            method_pass: analysis.role_pass,
            method_taint: analysis.method_taint,
            owner_dirty_skip: analysis.owner_dirty_skip,
            owner_dirty_owner_solve: analysis.owner_dirty_owner_solve,
            owner_dirty_journal_drain: analysis.owner_dirty_journal_drain,
            owner_dirty_method_taint_diff: analysis.owner_dirty_method_taint_diff,
            whole_pass_skips: analysis.method_role_whole_pass_skips,
            clean_owner_skips: analysis.owner_dirty_clean_owner_skips,
            dirty_solves: analysis.owner_dirty_dirty_solves,
            full_fallbacks: analysis.owner_dirty_full_fallbacks,
            journal_bursts: analysis.owner_dirty_journal_bursts,
            journal_mutations: analysis.owner_dirty_journal_mutations,
            peak_journal_burst: analysis.owner_dirty_peak_journal_burst,
            peak_owners: analysis.owner_dirty_peak_owners,
            peak_dependency_keys: analysis.owner_dirty_peak_dependency_keys,
            peak_dependencies_per_owner: analysis.owner_dirty_peak_dependencies_per_owner,
            peak_reverse_edges: analysis.owner_dirty_peak_reverse_edges,
            peak_retained_bytes: analysis.owner_dirty_peak_retained_bytes,
            live_owners: analysis.owner_dirty_live_owners,
            live_dependency_keys: analysis.owner_dirty_live_dependency_keys,
            live_reverse_edges: analysis.owner_dirty_live_reverse_edges,
            live_retained_bytes: analysis.owner_dirty_live_retained_bytes,
            per_owner_cap_rejections: analysis.owner_dirty_per_owner_cap_rejections,
            global_cap_fallbacks: analysis.owner_dirty_global_cap_fallbacks,
            demands: analysis.role_resolve_demands,
            candidate_scans: analysis.role_resolve_candidate_scans,
            candidate_matches: analysis.role_resolve_candidate_matches,
            prerequisite_demands: analysis.role_resolve_prerequisite_demands,
            prerequisite_candidate_scans: analysis.role_resolve_prerequisite_candidate_scans,
            prerequisite_candidate_matches: analysis.role_resolve_prerequisite_candidate_matches,
            candidate_cache_hits: analysis.role_resolve_candidate_cache_hits,
            candidate_cache_misses: analysis.role_resolve_candidate_cache_misses,
            exact_snapshot_hits: analysis.generalize_role_snapshot_hits,
            exact_snapshot_full_solves: analysis.generalize_role_snapshot_full_solves,
            exact_snapshot_misses: analysis.generalize_role_snapshot_misses,
            exact_snapshot_cap_fallbacks: analysis.generalize_role_snapshot_cap_fallbacks,
            exact_snapshot_peak_entries: analysis.generalize_role_snapshot_peak_entries,
            exact_snapshot_peak_retained_debug_bytes: analysis
                .generalize_role_snapshot_peak_retained_debug_bytes,
        }
    }
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
    compare_mono: bool,
    runtime_evidence_profile_deep: bool,
}

#[derive(Debug, Clone, PartialEq)]
struct CliMonoRunOutput {
    text: String,
    stdout: String,
    errors: Vec<String>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct RuntimeEvidenceRunTimings {
    args_parse: Duration,
    control_build_total: Duration,
    evidence_summary: Duration,
    evidence_plan_build: Duration,
    evidence_plan_profile: evidence_vm::EvidenceVmPlanBuildProfile,
    runtime_evidence_execute: Duration,
    root_format: Duration,
    total_before_compare: Duration,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum RuntimeBuildCacheKind {
    #[default]
    NotMeasured,
    Disabled,
    SourceKeyControlHit,
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
            Self::SourceKeyControlHit => "source-key-control-hit",
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
            // Stage 6 made this Stage 5 opt-in spelling a no-op. Keep accepting it without
            // changing behavior so older benchmark commands retain their original meaning.
            Some("--owner-dirty-scheduler-benchmark") => {}
            Some("--owner-dirty-scheduler-always-solve") => {
                options.owner_dirty_scheduler_always_solve = true;
            }
            Some("--generalize-role-snapshot-always-solve") => {
                options.generalize_role_snapshot_always_solve = true;
            }
            Some("--generalize-role-snapshot-enable-reuse") => {
                options.generalize_role_snapshot_enable_reuse = true;
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
        run_route(yulang::check_poly_from_entry(path), finish_compatible_check);
        return;
    }

    let source_options = options.std_source_options();
    run_route(
        yulang::check_poly_from_entry_with_std_options(path, &source_options),
        finish_compatible_check,
    );
}

fn finish_compatible_check(output: &yulang::CheckPolyOutput) {
    print_check_poly_output(output);
    if output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == yulang::SourceDiagnosticSeverity::Error)
    {
        process::exit(1);
    }
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
    ensure_parent_dir_or_exit(&out, "control-ir artifact");
    if let Err(error) = fs::write(&out, artifact) {
        eprintln!(
            "failed to write control-ir artifact {}: {error}",
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
    print_run_input_cst_if_requested(options, &input);
    if selection.backend == RunBackend::Mono {
        reject_non_native_run_host(program, selection);
        let files = if options.no_prelude {
            collect_bare_run_input_sources_or_exit(input, options)
        } else {
            let source_options = options.std_source_options();
            collect_std_run_input_sources_or_exit(input, &source_options)
        };
        abort_run_on_parse_diagnostics(&files);
        let output = run_mono_with_optional_cache(files, options.use_cache);
        run_mono_printer(selection.print_roots)(&output);
        return;
    }

    let mut timings = RuntimePhaseTimings::default();
    let total_start = Instant::now();
    let build = match input {
        RunInput::Path(path) => build_control_path_with_optional_source_key_cache(
            &path,
            options,
            options.runtime_phase_timings.then_some(&mut timings),
        ),
        RunInput::Source { path, source } => {
            let collect_start = Instant::now();
            let files = collect_control_run_input_sources_or_exit(
                RunInput::Source { path, source },
                options,
            );
            abort_run_on_parse_diagnostics(&files);
            timings.collect = collect_start.elapsed();
            build_control_with_optional_cache_timed(
                files,
                options.use_cache,
                options.runtime_phase_timings.then_some(&mut timings),
            )
        }
    };
    let eval_start = Instant::now();
    match selection.backend {
        RunBackend::EvidenceVm => {
            let output = if options.runtime_phase_timings || selection.runtime_evidence_profile_deep
            {
                run_built_evidence_for_cli_with_host_profile_and_plan_profile(
                    build,
                    selection.host,
                    selection.runtime_evidence_profile_deep,
                    options.runtime_phase_timings,
                    selection.print_nth,
                )
            } else {
                match selection.host {
                    RunHostMode::Native if !selection.print_nth => {
                        run_built_evidence_for_cli(build)
                    }
                    RunHostMode::Native => {
                        run_built_evidence_for_cli_with_host_print_nth(build, selection.host)
                    }
                    RunHostMode::Unsupported | RunHostMode::MockServer => {
                        if selection.print_nth {
                            run_built_evidence_for_cli_with_host_print_nth(build, selection.host)
                        } else {
                            run_built_evidence_for_cli_with_host(build, selection.host)
                        }
                    }
                }
            };
            timings.vm_eval = eval_start.elapsed();
            timings.runtime_execute = output.timings.execute;
            timings.root_format = output.timings.root_format;
            timings.total = total_start.elapsed();
            print_cli_evidence_run_output_with_roots(&output, selection.print_roots);
            if options.runtime_phase_timings {
                print_runtime_evidence_phase_timings(&timings, &output.timings, &output.stats);
            }
        }
        RunBackend::Mono => unreachable!("mono backend returned before control build"),
    }
}

fn reject_non_native_run_host(program: &str, selection: RunSelection) {
    if selection.host != RunHostMode::Native {
        print_usage_error_and_exit(program, "run --host unsupported requires the evidence VM");
    }
}

fn abort_run_on_parse_diagnostics(files: &[yulang::CollectedSource]) {
    let output = yulang::parse_diagnostics_from_collected_sources(files);
    if output.diagnostics.is_empty() {
        return;
    }
    print_check_diagnostics_summary(&output.diagnostics, output.diagnostic_source.as_ref());
    process::exit(1);
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

fn build_control_path_with_optional_source_key_cache(
    path: &PathBuf,
    options: &GlobalOptions,
    mut timings: Option<&mut RuntimePhaseTimings>,
) -> yulang::BuildControlOutput {
    let collect_start = Instant::now();
    let cached = options
        .use_cache
        .then(|| read_control_from_source_key_index(path, options, timings.as_deref_mut()))
        .flatten();

    let files = collect_control_sources_or_exit(path, options);
    if let Some(timings) = timings.as_deref_mut() {
        timings.collect = collect_start.elapsed();
    }
    abort_run_on_parse_diagnostics(&files);

    if let Some(mut output) = cached {
        output.diagnostic_sources =
            yulang::RuntimeDiagnosticSources::from_collected_sources(&files);
        return output;
    }

    if !options.use_cache {
        return build_control_with_optional_cache_timed(files, false, timings);
    }

    let key = yulang::cache::source_cache_key(&files);
    write_source_key_index_if_supported(path, options, key, &files);
    build_control_with_source_key_timed(files, key, timings)
}

fn read_control_from_source_key_index(
    path: &PathBuf,
    options: &GlobalOptions,
    mut timings: Option<&mut RuntimePhaseTimings>,
) -> Option<yulang::BuildControlOutput> {
    let cache = yulang::cache::ArtifactCache::new(yulang::stdlib::default_user_cache_root());
    let index_key = source_key_index_cache_key_for_path(path, options).ok()?;
    let artifact = match cache.read_source_key_index_artifact(index_key) {
        Ok(Some(artifact)) => artifact,
        Ok(None) => return None,
        Err(error) => {
            eprintln!("warning: {error}");
            return None;
        }
    };
    if !artifact.current_files_match() {
        return None;
    }
    let cached = match cache.read_control_artifact(artifact.source_key) {
        Ok(Some(cached)) => cached,
        Ok(None) => return None,
        Err(error) => {
            eprintln!("warning: {error}");
            return None;
        }
    };
    record_runtime_build_cache(&mut timings, RuntimeBuildCacheKind::SourceKeyControlHit);
    Some(yulang::BuildControlOutput {
        program: cached.program,
        runtime_evidence: cached.runtime_evidence,
        application_provenance: cached.application_provenance,
        selection_provenance: cached.selection_provenance,
        diagnostic_sources: yulang::RuntimeDiagnosticSources::default(),
        labels: cached.labels,
        file_count: cached.file_count,
        errors: cached.errors,
    })
}

fn write_source_key_index_if_supported(
    path: &PathBuf,
    options: &GlobalOptions,
    key: yulang::cache::SourceCacheKey,
    files: &[yulang::CollectedSource],
) {
    let Some(artifact) = yulang::cache::CachedSourceKeyIndexArtifact::from_files(files, key) else {
        return;
    };
    let Ok(index_key) = source_key_index_cache_key_for_path(path, options) else {
        return;
    };
    let cache = yulang::cache::ArtifactCache::new(yulang::stdlib::default_user_cache_root());
    if let Err(error) = cache.write_source_key_index_artifact(index_key, &artifact) {
        eprintln!("warning: {error}");
    }
}

fn source_key_index_cache_key_for_path(
    path: &PathBuf,
    options: &GlobalOptions,
) -> Result<yulang::cache::SourceKeyIndexCacheKey, yulang::RouteError> {
    if options.no_prelude {
        return Ok(yulang::cache::source_key_index_cache_key(path, None, false));
    }

    let source_options = options.std_source_options();
    let std_root = yulang::resolve_std_root_for_entry(path, &source_options)?;
    Ok(yulang::cache::source_key_index_cache_key(
        path,
        Some(&std_root),
        true,
    ))
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
    build_control_with_source_key_timed(files, key, timings)
}

fn build_control_with_source_key_timed(
    files: Vec<yulang::CollectedSource>,
    key: yulang::cache::SourceCacheKey,
    mut timings: Option<&mut RuntimePhaseTimings>,
) -> yulang::BuildControlOutput {
    let cache = yulang::cache::ArtifactCache::new(yulang::stdlib::default_user_cache_root());
    match cache.read_control_artifact(key) {
        Ok(Some(cached)) => {
            record_runtime_build_cache(&mut timings, RuntimeBuildCacheKind::ControlHit);
            return yulang::BuildControlOutput {
                program: cached.program,
                runtime_evidence: cached.runtime_evidence,
                application_provenance: cached.application_provenance,
                selection_provenance: cached.selection_provenance,
                diagnostic_sources: yulang::RuntimeDiagnosticSources::from_collected_sources(
                    &files,
                ),
                labels: cached.labels,
                file_count: cached.file_count,
                errors: cached.errors,
            };
        }
        Ok(None) => {}
        Err(error) => eprintln!("warning: {error}"),
    }

    let poly_start = Instant::now();
    let poly = build_poly_with_cache_timed(files.clone(), key, &cache, timings.as_deref_mut());
    if let Some(timings) = timings.as_deref_mut() {
        timings.build_poly = poly_start.elapsed();
    }
    let output = match try_build_control_from_poly_output_with_optional_mono_cache(
        poly,
        Some((&cache, key)),
        timings.as_deref_mut(),
    ) {
        Ok(output) => output,
        Err(()) => {
            let poly_start = Instant::now();
            let poly =
                build_poly_full_miss_with_cache_timed(files, key, &cache, timings.as_deref_mut());
            if let Some(timings) = timings.as_deref_mut() {
                timings.build_poly = poly_start.elapsed();
            }
            build_control_from_poly_output_with_optional_mono_cache(
                poly,
                Some((&cache, key)),
                timings.as_deref_mut(),
            )
        }
    };
    let artifact = yulang::cache::CachedControlArtifact {
        program: output.program.clone(),
        runtime_evidence: output.runtime_evidence.clone(),
        application_provenance: output.application_provenance.clone(),
        selection_provenance: output.selection_provenance.clone(),
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
    let (poly, lowering_timing) = run_route_to_value(
        yulang::source::build_poly_from_collected_sources_with_lowering_timing(files),
    );
    timings.role_resolution = Some(RuntimeRoleResolutionTelemetry::from_lowering_timing(
        lowering_timing,
    ));
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
    let lowered = match control_ir::lower_with_application_provenance(&specialized.program) {
        Ok(lowered) => lowered,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    if let Some(timings) = timings.as_deref_mut() {
        timings.control_lower = control_lower_start.elapsed();
    }

    yulang::BuildControlOutput {
        program: lowered.program,
        runtime_evidence: specialized.runtime_evidence,
        application_provenance: yulang::RuntimeApplicationProvenance::new(
            poly.application_provenance,
            lowered.application_provenance,
        ),
        selection_provenance: yulang::RuntimeSelectionProvenance::new(
            poly.selection_provenance,
            lowered.selection_provenance,
        ),
        diagnostic_sources: poly.diagnostic_sources,
        labels: poly.labels,
        file_count: poly.file_count,
        errors: poly.errors,
    }
}

fn try_build_control_from_poly_output_with_optional_mono_cache(
    poly: yulang::BuildPolyOutput,
    mono_cache: Option<(&yulang::cache::ArtifactCache, yulang::cache::SourceCacheKey)>,
    mut timings: Option<&mut RuntimePhaseTimings>,
) -> Result<yulang::BuildControlOutput, ()> {
    if !poly.errors.is_empty() {
        return Err(());
    }

    let specialize_start = Instant::now();
    let mut specialized = specialize::specialize_with_runtime_evidence_and_source_provenance(
        &poly.arena,
        poly.application_provenance.expr_ids(),
        poly.selection_provenance
            .selection_spans()
            .map(|(select, _)| select),
    )
    .map_err(|_| ())?;
    specialized.runtime_evidence.host_manifest = poly.host_manifest.clone();
    specialized
        .runtime_evidence
        .attach_static_route_profile(&poly.arena, &specialized.program);
    if let Some(timings) = timings.as_deref_mut() {
        timings.specialize = specialize_start.elapsed();
    }

    let control_lower_start = Instant::now();
    let lowered =
        control_ir::lower_with_application_provenance(&specialized.program).map_err(|_| ())?;
    if let Some(timings) = timings.as_deref_mut() {
        timings.control_lower = control_lower_start.elapsed();
    }

    if let Some((cache, key)) = mono_cache {
        let artifact = yulang::cache::CachedMonoArtifact {
            program: specialized.program.clone(),
            file_count: poly.file_count,
            errors: poly.errors.clone(),
        };
        if let Err(error) = cache.write_mono_artifact(key, &artifact) {
            eprintln!("warning: {error}");
        }
    }

    Ok(yulang::BuildControlOutput {
        program: lowered.program,
        runtime_evidence: specialized.runtime_evidence,
        application_provenance: yulang::RuntimeApplicationProvenance::new(
            poly.application_provenance,
            lowered.application_provenance,
        ),
        selection_provenance: yulang::RuntimeSelectionProvenance::new(
            poly.selection_provenance,
            lowered.selection_provenance,
        ),
        diagnostic_sources: poly.diagnostic_sources,
        labels: poly.labels,
        file_count: poly.file_count,
        errors: poly.errors,
    })
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
        Err(error) => exit_on_specialize_error(error, poly),
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
    let mut output = match specialize::specialize_with_runtime_evidence_and_source_provenance(
        &poly.arena,
        poly.application_provenance.expr_ids(),
        poly.selection_provenance
            .selection_spans()
            .map(|(select, _)| select),
    ) {
        Ok(output) => output,
        Err(error) => exit_on_specialize_error(error, poly),
    };
    output.runtime_evidence.host_manifest = poly.host_manifest.clone();
    output
        .runtime_evidence
        .attach_static_route_profile(&poly.arena, &output.program);

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

fn exit_on_specialize_error(
    error: specialize::SpecializeError,
    poly: &yulang::BuildPolyOutput,
) -> ! {
    let error = yulang::source::specialize_route_error(error, poly);
    eprintln!("{}", format_route_error(&error));
    process::exit(1);
}

fn abort_on_runtime_lowering_errors(errors: &[String]) {
    if errors.is_empty() {
        return;
    }
    eprintln!("{}", format_runtime_lowering_errors(errors));
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

fn record_runtime_role_resolution(
    timings: &mut Option<&mut RuntimePhaseTimings>,
    lowering_timing: infer::lowering::BodyLoweringTiming,
) {
    if let Some(timings) = timings.as_deref_mut() {
        timings.role_resolution = Some(RuntimeRoleResolutionTelemetry::from_lowering_timing(
            lowering_timing,
        ));
    }
}

fn print_runtime_evidence_phase_timings(
    timing: &RuntimePhaseTimings,
    evidence_timing: &CliEvidenceRunTimings,
    stats: &evidence_vm::RuntimeEvidenceRunStats,
) {
    eprintln!("runtime timing:");
    eprintln!("  run.backend: evidence-vm");
    eprintln!("  run.cache: {}", timing.build_cache.as_str());
    if let Some(entries) = timing.std_prefix_boundary_entries {
        eprintln!("  run.cache_interface.std_prefix_boundary_entries: {entries}");
    }
    if let Some(telemetry) = &timing.std_prefix_cache_interface {
        eprintln!(
            "  run.cache_interface.canonical_handoff_cost: {}",
            format_duration(telemetry.elapsed)
        );
        match &telemetry.outcome {
            yulang::cache::CompiledUnitCacheInterfaceOutcome::Canonical { boundary_entries } => {
                let outcome = if *boundary_entries == 0 {
                    "success-empty"
                } else {
                    "success-non-empty"
                };
                eprintln!("  run.cache_interface.canonical_handoff: {outcome}");
            }
            yulang::cache::CompiledUnitCacheInterfaceOutcome::LegacyEmptyFallback { error } => {
                eprintln!("  run.cache_interface.canonical_handoff: failure");
                eprintln!(
                    "  run.cache_interface.canonical_handoff_failure_kind: {}",
                    error.kind.as_str()
                );
                if let Some(def) = error.def {
                    eprintln!("  run.cache_interface.canonical_handoff_failure_def: {def:?}");
                }
                if let Some(label) = &error.definition_label {
                    eprintln!(
                        "  run.cache_interface.canonical_handoff_failure_definition: {label}"
                    );
                }
                eprintln!(
                    "  run.cache_interface.canonical_handoff_failure_detail: {}",
                    error.detail
                );
            }
        }
    }
    if let Some(role) = timing.role_resolution {
        eprintln!(
            "  run.analysis.role_resolution: {}",
            format_duration(role.total)
        );
        eprintln!(
            "  run.analysis.role_resolution.generalize: {}",
            format_duration(role.generalize)
        );
        eprintln!(
            "  run.analysis.role_resolution.methods: {}",
            format_duration(role.methods)
        );
        eprintln!(
            "  run.analysis.role_resolve.method_pass: {}",
            format_duration(role.method_pass)
        );
        eprintln!(
            "  run.analysis.role_resolve.method_taint: {}",
            format_duration(role.method_taint)
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.skip: {}",
            format_duration(role.owner_dirty_skip)
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.owner_solve: {}",
            format_duration(role.owner_dirty_owner_solve)
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.journal_drain: {}",
            format_duration(role.owner_dirty_journal_drain)
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.method_taint_diff: {}",
            format_duration(role.owner_dirty_method_taint_diff)
        );
        eprintln!(
            "  run.analysis.role_resolve.whole_pass_skips: {}",
            role.whole_pass_skips
        );
        eprintln!(
            "  run.analysis.role_resolve.clean_owner_skips: {}",
            role.clean_owner_skips
        );
        eprintln!(
            "  run.analysis.role_resolve.dirty_solves: {}",
            role.dirty_solves
        );
        eprintln!(
            "  run.analysis.role_resolve.full_fallbacks: {}",
            role.full_fallbacks
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.journal_bursts: {}",
            role.journal_bursts
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.journal_mutations: {}",
            role.journal_mutations
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.peak_journal_burst: {}",
            role.peak_journal_burst
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.peak_owners: {}",
            role.peak_owners
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.peak_dependency_keys: {}",
            role.peak_dependency_keys
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.peak_dependencies_per_owner: {}",
            role.peak_dependencies_per_owner
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.peak_reverse_edges: {}",
            role.peak_reverse_edges
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.peak_retained_bytes: {}",
            role.peak_retained_bytes
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.live_owners: {}",
            role.live_owners
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.live_dependency_keys: {}",
            role.live_dependency_keys
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.live_reverse_edges: {}",
            role.live_reverse_edges
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.live_retained_bytes: {}",
            role.live_retained_bytes
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.per_owner_cap_rejections: {}",
            role.per_owner_cap_rejections
        );
        eprintln!(
            "  run.analysis.role_resolve.owner_dirty.global_cap_fallbacks: {}",
            role.global_cap_fallbacks
        );
        eprintln!(
            "  run.analysis.role_resolve.exact_snapshot.hits: {}",
            role.exact_snapshot_hits
        );
        eprintln!(
            "  run.analysis.role_resolve.exact_snapshot.full_solves: {}",
            role.exact_snapshot_full_solves
        );
        eprintln!(
            "  run.analysis.role_resolve.exact_snapshot.misses: {}",
            role.exact_snapshot_misses
        );
        eprintln!(
            "  run.analysis.role_resolve.exact_snapshot.cap_fallbacks: {}",
            role.exact_snapshot_cap_fallbacks
        );
        eprintln!(
            "  run.analysis.role_resolve.exact_snapshot.peak_entries: {}",
            role.exact_snapshot_peak_entries
        );
        eprintln!(
            "  run.analysis.role_resolve.exact_snapshot.peak_retained_debug_bytes: {}",
            role.exact_snapshot_peak_retained_debug_bytes
        );
        eprintln!("  run.analysis.role_resolve.demands: {}", role.demands);
        eprintln!(
            "  run.analysis.role_resolve.candidate_scans: {}",
            role.candidate_scans
        );
        eprintln!(
            "  run.analysis.role_resolve.candidate_matches: {}",
            role.candidate_matches
        );
        eprintln!(
            "  run.analysis.role_resolve.prerequisite_demands: {}",
            role.prerequisite_demands
        );
        eprintln!(
            "  run.analysis.role_resolve.prerequisite_candidate_scans: {}",
            role.prerequisite_candidate_scans
        );
        eprintln!(
            "  run.analysis.role_resolve.prerequisite_candidate_matches: {}",
            role.prerequisite_candidate_matches
        );
        eprintln!(
            "  run.analysis.role_resolve.candidate_cache_hits: {}",
            role.candidate_cache_hits
        );
        eprintln!(
            "  run.analysis.role_resolve.candidate_cache_misses: {}",
            role.candidate_cache_misses
        );
    }
    eprintln!("  run.collect: {}", format_duration(timing.collect));
    eprintln!("  run.build_poly: {}", format_duration(timing.build_poly));
    eprintln!("  run.specialize: {}", format_duration(timing.specialize));
    eprintln!(
        "  run.control_lower: {}",
        format_duration(timing.control_lower)
    );
    eprintln!(
        "  run.evidence_plan_build: {}",
        format_duration(evidence_timing.plan_build)
    );
    print_evidence_plan_build_profile_stderr(&evidence_timing.plan_profile);
    eprintln!("  run.vm_eval: {}", format_duration(timing.vm_eval));
    eprintln!(
        "  run.runtime_execute: {}",
        format_duration(timing.runtime_execute)
    );
    eprintln!("  run.root_format: {}", format_duration(timing.root_format));
    eprintln!("  run.total: {}", format_duration(timing.total));

    eprintln!("runtime stats:");
    eprintln!(
        "  run.runtime_evidence.effect_calls: {}",
        stats.effect_calls
    );
    eprintln!(
        "  run.runtime_evidence.direct_effect_calls: {}",
        stats.direct_effect_calls
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_state_handlers: {}",
        stats.plan_known_state_handlers
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_state_handler_compiler_certificates: {}",
        stats.plan_known_state_handler_compiler_certificates
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_operation_calls: {}",
        stats.plan_known_operation_calls
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_operation_state_get_candidates: {}",
        stats.plan_known_operation_state_get_candidates
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_operation_state_set_candidates: {}",
        stats.plan_known_operation_state_set_candidates
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_operation_state_direct_gets: {}",
        stats.plan_known_operation_state_direct_gets
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_operation_state_direct_sets: {}",
        stats.plan_known_operation_state_direct_sets
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_state_operation_route_proofs: {}",
        stats.plan_known_state_operation_route_proofs
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_operation_reject_no_candidate_handler: {}",
        stats.plan_known_operation_reject_no_candidate_handler
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_operation_reject_no_known_state_access_proof: {}",
        stats.plan_known_operation_reject_no_known_state_access_proof
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_operation_reject_known_state_access_handler_mismatch: {}",
        stats.plan_known_operation_reject_known_state_access_handler_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_operation_reject_known_state_access_boundary_unsafe: {}",
        stats.plan_known_operation_reject_known_state_access_boundary_unsafe
    );
    eprintln!(
        "  run.runtime_evidence.plan_known_operation_reject_direct_execution_disabled: {}",
        stats.plan_known_operation_reject_direct_execution_disabled
    );
    eprintln!(
        "  run.runtime_evidence.static_route_sites_total: {}",
        stats.static_route_sites_total
    );
    eprintln!(
        "  run.runtime_evidence.static_route_static_handler: {}",
        stats.static_route_static_handler
    );
    eprintln!(
        "  run.runtime_evidence.static_route_static_tail_resumptive: {}",
        stats.static_route_static_tail_resumptive
    );
    eprintln!(
        "  run.runtime_evidence.static_route_static_abortive: {}",
        stats.static_route_static_abortive
    );
    eprintln!(
        "  run.runtime_evidence.static_route_static_other_arm: {}",
        stats.static_route_static_other_arm
    );
    eprintln!(
        "  run.runtime_evidence.static_route_dynamic_open_row: {}",
        stats.static_route_dynamic_open_row
    );
    eprintln!(
        "  run.runtime_evidence.static_route_dynamic_multiple_candidates: {}",
        stats.static_route_dynamic_multiple_candidates
    );
    eprintln!(
        "  run.runtime_evidence.static_route_dynamic_hygiene_barrier: {}",
        stats.static_route_dynamic_hygiene_barrier
    );
    eprintln!(
        "  run.runtime_evidence.static_route_dynamic_provider_env: {}",
        stats.static_route_dynamic_provider_env
    );
    eprintln!(
        "  run.runtime_evidence.static_route_dynamic_delayed_boundary: {}",
        stats.static_route_dynamic_delayed_boundary
    );
    eprintln!(
        "  run.runtime_evidence.static_route_dynamic_host_escape: {}",
        stats.static_route_dynamic_host_escape
    );
    eprintln!(
        "  run.runtime_evidence.static_route_dynamic_unclassified: {}",
        stats.static_route_dynamic_unclassified
    );
    eprintln!(
        "  run.runtime_evidence.static_route_mono_join_failures: {}",
        stats.static_route_mono_join_failures
    );
    eprintln!("  run.runtime_evidence.expr_evals: {}", stats.expr_evals);
    eprintln!("  run.runtime_evidence.env_clones: {}", stats.env_clones);
    eprintln!(
        "  run.runtime_evidence.max_env_depth: {}",
        stats.max_env_depth
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_frames: {}",
        stats.max_continuation_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_depth: {}",
        stats.max_continuation_depth
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_then_frames: {}",
        stats.max_continuation_then_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_state_frames: {}",
        stats.max_continuation_state_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_force_frames: {}",
        stats.max_continuation_force_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_apply_frames: {}",
        stats.max_continuation_apply_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_adapter_frames: {}",
        stats.max_continuation_adapter_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_case_frames: {}",
        stats.max_continuation_case_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_catch_frames: {}",
        stats.max_continuation_catch_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_scope_frames: {}",
        stats.max_continuation_scope_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_marker_frames: {}",
        stats.max_continuation_marker_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_provider_env_frames: {}",
        stats.max_continuation_provider_env_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_aggregate_frames: {}",
        stats.max_continuation_aggregate_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_select_frames: {}",
        stats.max_continuation_select_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_block_frames: {}",
        stats.max_continuation_block_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_continuation_ref_set_frames: {}",
        stats.max_continuation_ref_set_frames
    );
    eprintln!(
        "  run.runtime_evidence.max_active_frames_len: {}",
        stats.max_active_frames_len
    );
    eprintln!(
        "  run.runtime_evidence.max_active_handler_frames_len: {}",
        stats.max_active_handler_frames_len
    );
    eprintln!(
        "  run.runtime_evidence.max_active_add_ids_len: {}",
        stats.max_active_add_ids_len
    );
    eprintln!(
        "  run.runtime_evidence.max_active_marker_plans_len: {}",
        stats.max_active_marker_plans_len
    );
    eprintln!(
        "  run.runtime_evidence.max_active_provider_envs_len: {}",
        stats.max_active_provider_envs_len
    );
    eprintln!(
        "  run.runtime_evidence.max_active_provider_handlers_len: {}",
        stats.max_active_provider_handlers_len
    );
    eprintln!(
        "  run.runtime_evidence.max_active_state_handler_frames_len: {}",
        stats.max_active_state_handler_frames_len
    );
    eprintln!(
        "  run.runtime_evidence.max_host_scheduler_branches: {}",
        stats.max_host_scheduler_branches
    );
    eprintln!(
        "  run.runtime_evidence.max_host_scheduler_one_shot_tokens: {}",
        stats.max_host_scheduler_one_shot_tokens
    );
    eprintln!(
        "  run.runtime_evidence.max_host_scheduler_multi_shot_parents: {}",
        stats.max_host_scheduler_multi_shot_parents
    );
    eprintln!(
        "  run.runtime_evidence.max_host_scheduler_multi_shot_tokens: {}",
        stats.max_host_scheduler_multi_shot_tokens
    );
    eprintln!(
        "  run.runtime_evidence.max_suspended_host_continuations: {}",
        stats.max_suspended_host_continuations
    );
    eprintln!(
        "  run.runtime_evidence.continuation_appends: {}",
        stats.continuation_appends
    );
    eprintln!(
        "  run.runtime_evidence.continuation_owned_tail_appends: {}",
        stats.continuation_owned_tail_appends
    );
    eprintln!(
        "  run.runtime_evidence.continuation_append_steps: {}",
        stats.continuation_append_steps
    );
    eprintln!(
        "  run.runtime_evidence.continuation_resume_steps: {}",
        stats.continuation_resume_steps
    );
    eprintln!(
        "  run.runtime_evidence.continuation_resume_then_steps: {}",
        stats.continuation_resume_then_steps
    );
    eprintln!(
        "  run.runtime_evidence.continuation_resume_apply_steps: {}",
        stats.continuation_resume_apply_steps
    );
    eprintln!(
        "  run.runtime_evidence.continuation_resume_block_steps: {}",
        stats.continuation_resume_block_steps
    );
    eprintln!(
        "  run.runtime_evidence.continuation_resume_ref_set_steps: {}",
        stats.continuation_resume_ref_set_steps
    );
    eprintln!(
        "  run.runtime_evidence.marker_frame_entries: {}",
        stats.marker_frame_entries
    );
    eprintln!(
        "  run.runtime_evidence.marker_frame_markers: {}",
        stats.marker_frame_markers
    );
    eprintln!(
        "  run.runtime_evidence.marker_frame_active_add_id_markers: {}",
        stats.marker_frame_active_add_id_markers
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_would_loop: {}",
        stats.tail_invariant_base_would_loop
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_identity_mismatch: {}",
        stats.tail_invariant_base_rejected_identity_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_continuation_captured: {}",
        stats.tail_invariant_base_rejected_continuation_captured
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_carried_guard: {}",
        stats.tail_invariant_base_rejected_carried_guard
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_adapter_env: {}",
        stats.tail_invariant_base_rejected_adapter_env
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_other: {}",
        stats.tail_invariant_base_rejected_other
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_identity_mismatch_frames: {}",
        stats.tail_invariant_base_rejected_identity_mismatch_frames
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_identity_mismatch_handler_frames: {}",
        stats.tail_invariant_base_rejected_identity_mismatch_handler_frames
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_identity_mismatch_add_ids: {}",
        stats.tail_invariant_base_rejected_identity_mismatch_add_ids
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_identity_mismatch_marker_plans: {}",
        stats.tail_invariant_base_rejected_identity_mismatch_marker_plans
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_identity_mismatch_provider_envs: {}",
        stats.tail_invariant_base_rejected_identity_mismatch_provider_envs
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_identity_mismatch_provider_handlers: {}",
        stats.tail_invariant_base_rejected_identity_mismatch_provider_handlers
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_identity_mismatch_state_handler_frames: {}",
        stats.tail_invariant_base_rejected_identity_mismatch_state_handler_frames
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_identity_mismatch_host_branch: {}",
        stats.tail_invariant_base_rejected_identity_mismatch_host_branch
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_other_callee_not_closure: {}",
        stats.tail_invariant_base_rejected_other_callee_not_closure
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_other_no_active_marker_scope: {}",
        stats.tail_invariant_base_rejected_other_no_active_marker_scope
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_other_unsupported_marker_source: {}",
        stats.tail_invariant_base_rejected_other_unsupported_marker_source
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_other_handler_path: {}",
        stats.tail_invariant_base_rejected_other_handler_path
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_other_no_active_add_id: {}",
        stats.tail_invariant_base_rejected_other_no_active_add_id
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_rejected_other_no_candidate_marker_scope: {}",
        stats.tail_invariant_base_rejected_other_no_candidate_marker_scope
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_tail_would_loop: {}",
        stats.tail_invariant_base_at_tail_would_loop
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_tail_rejected_identity_mismatch: {}",
        stats.tail_invariant_base_at_tail_rejected_identity_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_tail_rejected_continuation_captured: {}",
        stats.tail_invariant_base_at_tail_rejected_continuation_captured
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_tail_rejected_carried_guard: {}",
        stats.tail_invariant_base_at_tail_rejected_carried_guard
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_tail_rejected_adapter_env: {}",
        stats.tail_invariant_base_at_tail_rejected_adapter_env
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_tail_rejected_other: {}",
        stats.tail_invariant_base_at_tail_rejected_other
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_would_loop: {}",
        stats.tail_invariant_base_at_resume_would_loop
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_rejected_identity_mismatch: {}",
        stats.tail_invariant_base_at_resume_rejected_identity_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_rejected_continuation_captured: {}",
        stats.tail_invariant_base_at_resume_rejected_continuation_captured
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_rejected_carried_guard: {}",
        stats.tail_invariant_base_at_resume_rejected_carried_guard
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_rejected_adapter_env: {}",
        stats.tail_invariant_base_at_resume_rejected_adapter_env
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_rejected_other: {}",
        stats.tail_invariant_base_at_resume_rejected_other
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_plain_would_loop: {}",
        stats.tail_invariant_base_at_resume_plain_would_loop
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_plain_rejected_identity_mismatch: {}",
        stats.tail_invariant_base_at_resume_plain_rejected_identity_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_plain_rejected_other: {}",
        stats.tail_invariant_base_at_resume_plain_rejected_other
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_recursive_would_loop: {}",
        stats.tail_invariant_base_at_resume_recursive_would_loop
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_recursive_rejected_identity_mismatch: {}",
        stats.tail_invariant_base_at_resume_recursive_rejected_identity_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.tail_invariant_base_at_resume_recursive_rejected_other: {}",
        stats.tail_invariant_base_at_resume_recursive_rejected_other
    );
    eprintln!(
        "  run.runtime_evidence.resume_marker_plan_enter_ops_total: {}",
        stats.resume_marker_plan_enter_ops_total
    );
    eprintln!(
        "  run.runtime_evidence.resume_marker_plan_active_add_id_ops: {}",
        stats.resume_marker_plan_active_add_id_ops
    );
    eprintln!(
        "  run.runtime_evidence.resume_marker_plan_to_legacy_push_pop: {}",
        stats.resume_marker_plan_to_legacy_push_pop
    );
    eprintln!(
        "  run.runtime_evidence.active_marker_plan_pushes: {}",
        stats.active_marker_plan_pushes
    );
    eprintln!(
        "  run.runtime_evidence.active_marker_plan_dedupes: {}",
        stats.active_marker_plan_dedupes
    );
    eprintln!(
        "  run.runtime_evidence.active_add_id_scans: {}",
        stats.active_add_id_scans
    );
    eprintln!(
        "  run.runtime_evidence.active_add_id_path_candidates: {}",
        stats.active_add_id_path_candidates
    );
    eprintln!(
        "  run.runtime_evidence.active_add_id_path_rejects: {}",
        stats.active_add_id_path_rejects
    );
    eprintln!(
        "  run.runtime_evidence.active_add_id_entry_except_rejects: {}",
        stats.active_add_id_entry_except_rejects
    );
    eprintln!(
        "  run.runtime_evidence.active_add_id_already_carried_rejects: {}",
        stats.active_add_id_already_carried_rejects
    );
    eprintln!(
        "  run.runtime_evidence.active_add_id_hits: {}",
        stats.active_add_id_hits
    );
    eprintln!(
        "  run.runtime_evidence.permission_visibility_guard_mask: {}",
        stats.permission_visibility_guard_mask
    );
    eprintln!(
        "  run.runtime_evidence.provider_add_id_shortcut_attempts: {}",
        stats.provider_add_id_shortcut_attempts
    );
    eprintln!(
        "  run.runtime_evidence.provider_add_id_shortcut_used: {}",
        stats.provider_add_id_shortcut_used
    );
    eprintln!(
        "  run.runtime_evidence.provider_add_id_shortcut_fallback_carry_after_frame: {}",
        stats.provider_add_id_shortcut_fallback_carry_after_frame
    );
    eprintln!(
        "  run.runtime_evidence.resume_marker_provider_pair_close_reject_carry_after_frame: {}",
        stats.resume_marker_provider_pair_close_reject_carry_after_frame
    );
    eprintln!(
        "  run.runtime_evidence.resume_marker_provider_prefix_boundary_reject_carry_after_frame: {}",
        stats.resume_marker_provider_prefix_boundary_reject_carry_after_frame
    );
    eprintln!(
        "  run.runtime_evidence.provider_env_foreign_boundary_reject_carry_after_frame: {}",
        stats.provider_env_foreign_boundary_reject_carry_after_frame
    );
    eprintln!(
        "  run.runtime_evidence.provider_env_foreign_miss_boundary_reject_carry_after_frame: {}",
        stats.provider_env_foreign_miss_boundary_reject_carry_after_frame
    );
    eprintln!(
        "  run.runtime_evidence.marked_force_carry_after_frame_markers: {}",
        stats.marked_force_carry_after_frame_markers
    );
    eprintln!(
        "  run.runtime_evidence.marked_force_reentry_same_identity_safe: {}",
        stats.marked_force_reentry_same_identity_safe
    );
    eprintln!(
        "  run.runtime_evidence.marked_force_reentry_fused: {}",
        stats.marked_force_reentry_fused
    );
    eprintln!(
        "  run.runtime_evidence.marked_force_reentry_same_identity_unsafe_materialized: {}",
        stats.marked_force_reentry_same_identity_unsafe_materialized
    );
    eprintln!(
        "  run.runtime_evidence.marked_force_reentry_different_identity: {}",
        stats.marked_force_reentry_different_identity
    );
    eprintln!(
        "  run.runtime_evidence.marked_force_no_reentry: {}",
        stats.marked_force_no_reentry
    );
    eprintln!(
        "  run.runtime_evidence.known_state_direct_gets: {}",
        stats.known_state_direct_gets
    );
    eprintln!(
        "  run.runtime_evidence.known_state_direct_sets: {}",
        stats.known_state_direct_sets
    );
    eprintln!(
        "  run.runtime_evidence.known_state_perform_short_circuit_gets: {}",
        stats.known_state_perform_short_circuit_gets
    );
    eprintln!(
        "  run.runtime_evidence.known_state_perform_short_circuit_sets: {}",
        stats.known_state_perform_short_circuit_sets
    );
    eprintln!(
        "  run.runtime_evidence.known_state_direct_missing_state: {}",
        stats.known_state_direct_missing_state
    );
    eprintln!(
        "  run.runtime_evidence.known_state_direct_non_resumptive: {}",
        stats.known_state_direct_non_resumptive
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_entries: {}",
        stats.known_state_frame_entries
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_exits: {}",
        stats.known_state_frame_exits
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_reads_late: {}",
        stats.known_state_frame_reads_late
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_writes_late: {}",
        stats.known_state_frame_writes_late
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_missing_late: {}",
        stats.known_state_frame_missing_late
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_shadow_compat_fallbacks: {}",
        stats.known_state_frame_shadow_compat_fallbacks
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_snapshots: {}",
        stats.known_state_frame_snapshots
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_snapshot_missing_frame: {}",
        stats.known_state_frame_snapshot_missing_frame
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_snapshot_max_depth: {}",
        stats.known_state_frame_snapshot_max_depth
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_forks: {}",
        stats.known_state_frame_forks
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_multishot_forks: {}",
        stats.known_state_frame_multishot_forks
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_resume_entries: {}",
        stats.known_state_frame_resume_entries
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_resume_exits: {}",
        stats.known_state_frame_resume_exits
    );
    eprintln!(
        "  run.runtime_evidence.known_state_frame_resume_request_rewraps: {}",
        stats.known_state_frame_resume_request_rewraps
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_state_get_candidate_hits: {}",
        stats.known_operation_state_get_candidate_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_state_set_candidate_hits: {}",
        stats.known_operation_state_set_candidate_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_state_get_active_frame_hits: {}",
        stats.known_operation_state_get_active_frame_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_state_set_active_frame_hits: {}",
        stats.known_operation_state_set_active_frame_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_state_get_active_frame_misses: {}",
        stats.known_operation_state_get_active_frame_misses
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_state_set_active_frame_misses: {}",
        stats.known_operation_state_set_active_frame_misses
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_state_direct_get_plan_hits: {}",
        stats.known_operation_state_direct_get_plan_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_state_direct_set_plan_hits: {}",
        stats.known_operation_state_direct_set_plan_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_shadow_hits: {}",
        stats.known_operation_route_shadow_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_shadow_get_hits: {}",
        stats.known_operation_route_shadow_get_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_shadow_set_hits: {}",
        stats.known_operation_route_shadow_set_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_shadow_missing_proof: {}",
        stats.known_operation_route_shadow_missing_proof
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_shadow_missing_frame: {}",
        stats.known_operation_route_shadow_missing_frame
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_shadow_role_mismatch: {}",
        stats.known_operation_route_shadow_role_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_get_attempts: {}",
        stats.known_operation_route_direct_get_attempts
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_get_hits: {}",
        stats.known_operation_route_direct_get_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_get_missing_proof: {}",
        stats.known_operation_route_direct_get_missing_proof
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_get_missing_frame: {}",
        stats.known_operation_route_direct_get_missing_frame
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_get_role_mismatch: {}",
        stats.known_operation_route_direct_get_role_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_get_payload_mismatch: {}",
        stats.known_operation_route_direct_get_payload_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_set_attempts: {}",
        stats.known_operation_route_direct_set_attempts
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_set_hits: {}",
        stats.known_operation_route_direct_set_hits
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_set_missing_proof: {}",
        stats.known_operation_route_direct_set_missing_proof
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_set_missing_frame: {}",
        stats.known_operation_route_direct_set_missing_frame
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_set_role_mismatch: {}",
        stats.known_operation_route_direct_set_role_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_route_direct_set_payload_mismatch: {}",
        stats.known_operation_route_direct_set_payload_mismatch
    );
    eprintln!(
        "  run.runtime_evidence.known_operation_reject_no_candidate_handler_hits: {}",
        stats.known_operation_reject_no_candidate_handler_hits
    );
    eprintln!(
        "  run.runtime_evidence.ref_set_evals: {}",
        stats.ref_set_evals
    );
    eprintln!(
        "  run.runtime_evidence.ref_set_update_effect_calls: {}",
        stats.ref_set_update_effect_calls
    );
    eprintln!(
        "  run.runtime_evidence.ref_set_assignment_ref_update_requests: {}",
        stats.ref_set_assignment_ref_update_requests
    );
    eprintln!(
        "  run.runtime_evidence.ref_set_value_ref_update_requests: {}",
        stats.ref_set_value_ref_update_requests
    );
    eprintln!(
        "  run.runtime_evidence.list_merge_calls: {}",
        stats.list_merge_calls
    );
}

fn print_evidence_plan_build_profile_stderr(profile: &evidence_vm::EvidenceVmPlanBuildProfile) {
    for line in format_evidence_plan_build_profile_lines("run.evidence_plan_build", profile) {
        eprintln!("{line}");
    }
}

fn format_evidence_plan_build_profile_lines(
    prefix: &str,
    profile: &evidence_vm::EvidenceVmPlanBuildProfile,
) -> Vec<String> {
    [
        (
            "control_evidence",
            format_duration(profile.control_evidence),
        ),
        (
            "runtime_node_index",
            format_duration(profile.runtime_node_index),
        ),
        (
            "lexical_handler_index",
            format_duration(profile.lexical_handler_index),
        ),
        ("handler_plans", format_duration(profile.handler_plans)),
        ("operation_plans", format_duration(profile.operation_plans)),
        ("function_plans", format_duration(profile.function_plans)),
        ("call_plans", format_duration(profile.call_plans)),
        ("value_env_plans", format_duration(profile.value_env_plans)),
        ("object_plan", format_duration(profile.object_plan)),
        ("object_slots", format_duration(profile.object_slots)),
        ("handler_objects", format_duration(profile.handler_objects)),
        (
            "handler_capabilities",
            format_duration(profile.handler_capabilities),
        ),
        (
            "known_handler_join",
            format_duration(profile.known_handler_join),
        ),
        (
            "function_objects",
            format_duration(profile.function_objects),
        ),
        (
            "lexical_handler_envs",
            format_duration(profile.lexical_handler_envs),
        ),
        ("value_objects", format_duration(profile.value_objects)),
        ("call_objects", format_duration(profile.call_objects)),
        (
            "static_route_index",
            format_duration(profile.static_route_index),
        ),
        (
            "operation_objects",
            format_duration(profile.operation_objects),
        ),
        (
            "static_route_join",
            format_duration(profile.static_route_join),
        ),
        (
            "known_operation_join",
            format_duration(profile.known_operation_join),
        ),
        ("provider_index", format_duration(profile.provider_index)),
        ("summary", format_duration(profile.summary)),
        ("walk_unique_bodies", profile.walk_unique_bodies.to_string()),
        ("walk_operations", profile.walk_operations.to_string()),
        (
            "walk_redundant_rewalks",
            profile.walk_redundant_rewalks.to_string(),
        ),
        (
            "walk_redundant_bodies",
            profile.walk_redundant_bodies.to_string(),
        ),
        (
            "walk_redundancy_ratio",
            format!("{:.2}", profile.walk_redundancy_ratio()),
        ),
    ]
    .into_iter()
    .map(|(name, value)| format!("  {prefix}.{name}: {value}"))
    .collect()
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
                application_provenance: cached.application_provenance,
                selection_provenance: cached.selection_provenance,
                diagnostic_sources: yulang::RuntimeDiagnosticSources::from_collected_sources(
                    &files,
                ),
                labels: cached.labels,
                host_manifest: cached.host_manifest,
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
            if let Some((mut output, cache_kind)) =
                build_poly_from_source_unit_prefix_cache(&files, key, cache, timings.as_deref_mut())
            {
                record_runtime_build_cache(&mut timings, cache_kind);
                output.diagnostic_sources =
                    yulang::RuntimeDiagnosticSources::from_collected_sources(&files);
                return output;
            }
            build_poly_full_miss_with_cache_timed(files, key, cache, timings.as_deref_mut())
        }
        Err(error) => {
            eprintln!("warning: {error}");
            record_runtime_build_cache(&mut timings, RuntimeBuildCacheKind::ErrorFallback);
            if timings.is_some() {
                let (output, lowering_timing) = run_route_to_value(
                    yulang::source::build_poly_from_collected_sources_with_lowering_timing(files),
                );
                record_runtime_role_resolution(&mut timings, lowering_timing);
                output
            } else {
                run_route_to_value(yulang::build_poly_from_collected_sources(files))
            }
        }
    }
}

fn build_poly_full_miss_with_cache_timed(
    files: Vec<yulang::CollectedSource>,
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
    mut timings: Option<&mut RuntimePhaseTimings>,
) -> yulang::BuildPolyOutput {
    record_runtime_build_cache(&mut timings, RuntimeBuildCacheKind::FullMiss);
    let output = if timings.is_some() {
        let (output, lowering_timing) = run_route_to_value(
            yulang::source::build_poly_and_compiled_unit_from_collected_sources_with_lowering_timing(
                files.clone(),
            ),
        );
        record_runtime_role_resolution(&mut timings, lowering_timing);
        output
    } else {
        run_route_to_value(yulang::build_poly_and_compiled_unit_from_collected_sources(
            files.clone(),
        ))
    };
    if let Err(error) = cache.write_compiled_unit_artifact(key, &output.compiled_unit) {
        eprintln!("warning: {error}");
    }
    write_source_unit_closure_artifacts(&files, cache);
    let poly = output.poly;
    let diagnostic_sources = poly.diagnostic_sources;
    let artifact = yulang::cache::CachedPolyArtifact {
        arena: poly.arena,
        application_provenance: poly.application_provenance,
        selection_provenance: poly.selection_provenance,
        labels: poly.labels,
        host_manifest: poly.host_manifest,
        file_count: poly.file_count,
        errors: poly.errors,
    };
    if let Err(error) = cache.write_poly_artifact(key, &artifact) {
        eprintln!("warning: {error}");
    }
    yulang::BuildPolyOutput {
        arena: artifact.arena,
        application_provenance: artifact.application_provenance,
        selection_provenance: artifact.selection_provenance,
        diagnostic_sources,
        labels: artifact.labels,
        host_manifest: artifact.host_manifest,
        file_count: artifact.file_count,
        errors: artifact.errors,
    }
}

fn build_poly_from_source_unit_prefix_cache(
    files: &[yulang::CollectedSource],
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
    mut timings: Option<&mut RuntimePhaseTimings>,
) -> Option<(yulang::BuildPolyOutput, RuntimeBuildCacheKind)> {
    if source_set_contains_std(files) {
        return build_poly_from_std_prefix_cache(files, key, cache, timings.as_deref_mut());
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
    if let Some(output) = build_poly_from_merged_source_unit_prefix_cache(
        files,
        key,
        cache,
        &candidates,
        timings.as_deref_mut(),
    ) {
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
        timings,
    )
    .map(|output| (output, RuntimeBuildCacheKind::SourceUnitPrefixHit))
}

fn build_poly_from_std_prefix_cache(
    files: &[yulang::CollectedSource],
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
    mut timings: Option<&mut RuntimePhaseTimings>,
) -> Option<(yulang::BuildPolyOutput, RuntimeBuildCacheKind)> {
    let plan = std_prefix_cache_plan(files)?;
    let (prefix, kind) = match cache.read_compiled_unit_artifact(plan.key) {
        Ok(Some(prefix)) if prefix.errors.is_empty() => {
            (prefix, RuntimeBuildCacheKind::StdPrefixHit)
        }
        Ok(Some(_)) | Ok(None) => (
            build_std_prefix_artifact(files, cache, &plan, timings.as_deref_mut())?,
            RuntimeBuildCacheKind::StdPrefixBuild,
        ),
        Err(error) => {
            eprintln!("warning: {error}");
            (
                build_std_prefix_artifact(files, cache, &plan, timings.as_deref_mut())?,
                RuntimeBuildCacheKind::StdPrefixBuild,
            )
        }
    };
    if let Some(timings) = timings.as_deref_mut() {
        timings.std_prefix_boundary_entries = Some(prefix.runtime.boundary.bounds.len());
    }
    if !std_prefix_cache_safety::can_reuse_for_program(files, &plan.file_indices, &prefix) {
        return None;
    }
    build_poly_from_compiled_source_unit_prefix(
        files,
        key,
        cache,
        &plan.file_indices,
        prefix,
        timings,
    )
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
    timings: Option<&mut RuntimePhaseTimings>,
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
    build_poly_from_compiled_source_unit_prefix(files, key, cache, &covered_files, prefix, timings)
}

fn build_poly_from_compiled_source_unit_prefix(
    files: &[yulang::CollectedSource],
    key: yulang::cache::SourceCacheKey,
    cache: &yulang::cache::ArtifactCache,
    prefix_file_indices: &[usize],
    prefix: yulang::cache::CachedCompiledUnitArtifact,
    mut timings: Option<&mut RuntimePhaseTimings>,
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
    let observed = timings.is_some();
    let output = match if observed {
        yulang::source::build_poly_and_compiled_unit_from_compiled_unit_prefix_and_collected_sources_with_lowering_timing(
            prefix,
            files.to_vec(),
            suffix,
        )
        .map(|(output, lowering_timing)| (output, Some(lowering_timing)))
    } else {
        yulang::build_poly_and_compiled_unit_from_compiled_unit_prefix_and_collected_sources(
            prefix,
            files.to_vec(),
            suffix,
        )
        .map(|output| (output, None))
    } {
        Ok(output) => output,
        Err(error) => {
            eprintln!("warning: {error}");
            return None;
        }
    };
    let (output, lowering_timing) = output;
    if let Some(lowering_timing) = lowering_timing {
        record_runtime_role_resolution(&mut timings, lowering_timing);
    }
    if !output.poly.errors.is_empty() {
        return None;
    }
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
    timings: Option<&mut RuntimePhaseTimings>,
) -> Option<yulang::cache::CachedCompiledUnitArtifact> {
    let prefix_files = plan
        .file_indices
        .iter()
        .map(|file| files[*file].clone())
        .collect::<Vec<_>>();
    let loaded = sources::load(std_prefix_lowering_source_files(files, &plan.file_indices));
    let artifact = if let Some(timings) = timings {
        match yulang::cache::compiled_unit_artifact_from_loaded_files_with_key_and_cache_interface_telemetry(
            &prefix_files,
            &loaded,
            plan.key,
        ) {
            Ok((artifact, telemetry)) => {
                timings.std_prefix_cache_interface = Some(telemetry);
                artifact
            }
            Err(error) => {
                eprintln!("warning: {error}");
                return None;
            }
        }
    } else {
        match yulang::cache::compiled_unit_artifact_from_loaded_files_with_key(
            &prefix_files,
            &loaded,
            plan.key,
        ) {
            Ok(artifact) => artifact,
            Err(error) => {
                eprintln!("warning: {error}");
                return None;
            }
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
    let diagnostic_sources = poly.diagnostic_sources;
    let artifact = yulang::cache::CachedPolyArtifact {
        arena: poly.arena,
        application_provenance: poly.application_provenance,
        selection_provenance: poly.selection_provenance,
        labels: poly.labels,
        host_manifest: poly.host_manifest,
        file_count: poly.file_count,
        errors: poly.errors,
    };
    if let Err(error) = cache.write_poly_artifact(key, &artifact) {
        eprintln!("warning: {error}");
    }
    yulang::BuildPolyOutput {
        arena: artifact.arena,
        application_provenance: artifact.application_provenance,
        selection_provenance: artifact.selection_provenance,
        diagnostic_sources,
        labels: artifact.labels,
        host_manifest: artifact.host_manifest,
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
    let evidence = control_ir::ControlEvidenceProgram::from_program(&output.program);
    let mut text = control_ir::format_control_evidence_program(&evidence);
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
            eprintln!("{}", format_mono_runtime_error(&error));
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

fn run_mono_compare_for_path(path: &PathBuf, options: &GlobalOptions) -> CliMonoRunOutput {
    let files = collect_control_sources_or_exit(path, options);
    abort_run_on_parse_diagnostics(&files);
    let mono_cache = mono_cache_for_files(&files, options.use_cache);
    let output = build_poly_with_optional_cache(files, options.use_cache);
    let program = specialize_mono_program(
        &output,
        mono_cache.as_ref().map(|(cache, key)| (cache, *key)),
    );
    run_mono_program_for_cli_compare(&program, &output.labels, output.errors)
}

fn run_mono_program_for_cli_compare(
    program: &specialize::mono::Program,
    labels: &poly::dump::DumpLabels,
    errors: Vec<String>,
) -> CliMonoRunOutput {
    let mut stdout = String::new();
    let values = match mono_runtime::run_program_with_host(program, |path, payload| {
        handle_mono_host_effect(path, payload, &mut stdout)
    }) {
        Ok(values) => values,
        Err(error) => {
            eprintln!("{}", format_mono_runtime_error(&error));
            process::exit(1);
        }
    };
    CliMonoRunOutput {
        text: yulang::format_run_mono_values_with_labels(&values, Some(labels)),
        stdout,
        errors,
    }
}

fn handle_mono_host_effect(
    path: &[String],
    payload: &mono_runtime::Value,
    stdout: &mut String,
) -> Option<mono_runtime::Value> {
    if path == ["std", "io", "console", "out", "write"] {
        push_mono_host_string_payload(payload, stdout)?;
        return Some(mono_runtime::Value::Unit);
    }
    None
}

fn push_mono_host_string_payload(value: &mono_runtime::Value, out: &mut String) -> Option<()> {
    match value {
        mono_runtime::Value::Str(value) => {
            value.push_to_string(out);
            Some(())
        }
        mono_runtime::Value::Marked { value, .. } => push_mono_host_string_payload(value, out),
        _ => None,
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
    for stage in ["control-ir", "mono", "poly", "compiled-unit"] {
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
        let output =
            build_control_path_with_optional_source_key_cache(&path, options, Some(&mut timings));
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

fn run_runtime_evidence_run(
    program: &str,
    debug_command: &str,
    options: &GlobalOptions,
    args: VecDeque<OsString>,
) {
    let total_start = Instant::now();
    let mut timings = RuntimeEvidenceRunTimings::default();
    let mut build_timings = RuntimePhaseTimings::default();
    let args_start = Instant::now();
    let args = parse_runtime_evidence_run_args(program, debug_command, args);
    timings.args_parse = args_start.elapsed();
    let build_start = Instant::now();
    let build = build_control_path_with_optional_source_key_cache(
        &args.path,
        options,
        Some(&mut build_timings),
    );
    timings.control_build_total = build_start.elapsed();
    let summary_start = Instant::now();
    let summary = RuntimeEvidenceBenchSummary::from_surface(&build.runtime_evidence);
    timings.evidence_summary = summary_start.elapsed();
    let plan_start = Instant::now();
    let (plan, plan_profile) =
        evidence_vm::build_plan_with_profile(&build.program, &build.runtime_evidence);
    timings.evidence_plan_build = plan_start.elapsed();
    timings.evidence_plan_profile = plan_profile;
    let run_start = Instant::now();
    let output = match evidence_vm::run_program_with_plan_deep_profile_with_labels(
        &build.program,
        &plan,
        args.runtime_evidence_profile_deep,
        &build.labels,
    ) {
        Ok(output) => output,
        Err(error) => {
            eprintln!("{error}");
            process::exit(1);
        }
    };
    timings.runtime_evidence_execute = run_start.elapsed();
    let format_start = Instant::now();
    let roots_text = output.roots_text_with_labels(Some(&build.labels));
    timings.root_format = format_start.elapsed();
    timings.total_before_compare = total_start.elapsed();

    runtime_evidence_debug::print_run_report(&summary, &output, &timings, &build_timings);

    if args.compare_mono {
        let mono = run_mono_compare_for_path(&args.path, options);
        if !mono.errors.is_empty() {
            for error in &mono.errors {
                eprintln!("error: {error}");
            }
            process::exit(1);
        }
        if output.stdout != mono.stdout {
            eprintln!("{debug_command} compare-mono stdout mismatch");
            eprintln!("expected stdout:\n{}", mono.stdout);
            eprintln!("actual stdout:\n{}", output.stdout);
            process::exit(1);
        }
        if roots_text != mono.text {
            eprintln!("{debug_command} compare-mono mismatch");
            eprintln!("expected:\n{}", mono.text);
            eprintln!("actual:\n{roots_text}");
            process::exit(1);
        }
        println!("  compare.mono: match");
    }

    print!("{}", output.stdout);
    print!("{roots_text}");
}

fn parse_runtime_evidence_run_args(
    program: &str,
    debug_command: &str,
    mut args: VecDeque<OsString>,
) -> RuntimeEvidenceRunArgs {
    let mut path = None;
    let mut compare_mono = false;
    let mut runtime_evidence_profile_deep = false;

    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--compare-mono") => compare_mono = true,
            Some("--runtime-evidence-profile-deep") => runtime_evidence_profile_deep = true,
            Some(value) if value.starts_with("--") => {
                print_usage_error_and_exit(
                    program,
                    &format!("unknown debug {debug_command} option: {value}"),
                );
            }
            _ => {
                if path.is_some() {
                    print_usage_error_and_exit(
                        program,
                        &format!("debug {debug_command} takes exactly one path"),
                    );
                }
                path = Some(PathBuf::from(arg));
            }
        }
    }

    let Some(path) = path else {
        print_usage_error_and_exit(program, &format!("debug {debug_command} requires a path"));
    };
    RuntimeEvidenceRunArgs {
        path,
        compare_mono,
        runtime_evidence_profile_deep,
    }
}

fn run_debug(program: &str, options: &GlobalOptions, mut args: VecDeque<OsString>) {
    let Some(op) = args.pop_front() else {
        print_usage_and_exit(program);
    };
    match op.to_str() {
        Some("host-act-manifest") => run_host_act_manifest(program, options, args),
        Some("runtime-evidence-bench") => run_runtime_evidence_bench(program, options, args),
        Some("runtime-evidence-run") => {
            run_runtime_evidence_run(program, "runtime-evidence-run", options, args)
        }
        Some("evidence-vm-run") => {
            run_runtime_evidence_run(program, "evidence-vm-run", options, args)
        }
        Some("evidence-vm-plan") => {
            let path = require_one_path(program, args);
            let files = collect_control_sources_or_exit(&path, options);
            let output = dump_evidence_vm_plan_with_optional_cache(files, options.use_cache);
            print_dump_mono_output(&output);
        }
        _ => print_usage_and_exit(program),
    }
}

fn run_host_act_manifest(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    if !args.is_empty() {
        print_usage_error_and_exit(program, "debug host-act-manifest does not take arguments");
    }

    let files = run_route_to_value(yulang::collect_local_source_text_with_std_options(
        PathBuf::from("host-act-manifest.yu"),
        "1\n".to_string(),
        &options.std_source_options(),
    ));
    let output = run_route_to_value(yulang::build_poly_and_compiled_unit_from_collected_sources(
        files,
    ));
    let Some(manifest) = output.poly.host_manifest else {
        eprintln!("failed to build compiler host manifest");
        process::exit(1);
    };

    println!("compiler host manifest:");
    println!("  hash={:016x}", manifest.hash.0);
    for operation in manifest.operations {
        let tier = generated_host_operation_tier_id(operation.tier);
        let surface = generated_host_operation_surface_id(operation.surface);
        println!(
            "  act={} op={} tier={} path={} sig={} surface={} column={} symbol={}",
            operation.act_id,
            operation.operation_id,
            tier,
            operation.path.join("."),
            operation.signature,
            surface,
            operation.column,
            operation.symbol
        );
    }
    println!("runtime host tiers:");
    for tier in supported_host_operation_tiers() {
        println!("  tier={}", generated_host_operation_tier_id(tier));
    }
}

fn supported_host_operation_tiers() -> [poly::host_manifest::HostOperationTier; 3] {
    [
        poly::host_manifest::HostOperationTier::Sync,
        poly::host_manifest::HostOperationTier::SuspendOneShot,
        poly::host_manifest::HostOperationTier::SuspendMultiShot,
    ]
}

fn generated_host_operation_tier_id(tier: poly::host_manifest::HostOperationTier) -> &'static str {
    match tier {
        poly::host_manifest::HostOperationTier::Sync => "sync",
        poly::host_manifest::HostOperationTier::SuspendOneShot => "suspend-one-shot",
        poly::host_manifest::HostOperationTier::SuspendMultiShot => "suspend-multi-shot",
    }
}

fn generated_host_operation_surface_id(
    surface: poly::host_manifest::HostOperationSurface,
) -> &'static str {
    match surface {
        poly::host_manifest::HostOperationSurface::Contract => "contract",
        poly::host_manifest::HostOperationSurface::RawCompat => "raw-compat",
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn owner_dirty_scheduler_benchmark_is_accepted_as_a_compatibility_no_op() {
        let (default_options, default_args) =
            parse_global_options(VecDeque::from([OsString::from("run")])).expect("parse default");
        assert!(!default_options.owner_dirty_scheduler_always_solve);

        let (compatibility_options, compatibility_args) = parse_global_options(VecDeque::from([
            OsString::from("--owner-dirty-scheduler-benchmark"),
            OsString::from("run"),
        ]))
        .expect("parse retained benchmark flag");

        assert_eq!(compatibility_options, default_options);
        assert_eq!(compatibility_args, default_args);
    }

    #[test]
    fn owner_dirty_scheduler_always_solve_flag_selects_the_disable_control() {
        let (options, args) = parse_global_options(VecDeque::from([
            OsString::from("--owner-dirty-scheduler-always-solve"),
            OsString::from("run"),
        ]))
        .expect("parse always-solve flag");

        assert!(options.owner_dirty_scheduler_always_solve);
        assert_eq!(args, VecDeque::from([OsString::from("run")]));
    }

    #[test]
    fn generalize_role_snapshot_always_solve_flag_selects_the_rollback_control() {
        let (options, args) = parse_global_options(VecDeque::from([
            OsString::from("--generalize-role-snapshot-always-solve"),
            OsString::from("check-poly"),
        ]))
        .expect("parse generalize snapshot always-solve flag");

        assert!(options.generalize_role_snapshot_always_solve);
        assert_eq!(args, VecDeque::from([OsString::from("check-poly")]));
    }

    #[test]
    fn generalize_role_snapshot_enable_reuse_flag_selects_the_opt_in() {
        let (options, args) = parse_global_options(VecDeque::from([
            OsString::from("--generalize-role-snapshot-enable-reuse"),
            OsString::from("check-poly"),
        ]))
        .expect("parse generalize snapshot reuse opt-in flag");

        assert!(options.generalize_role_snapshot_enable_reuse);
        assert!(!options.generalize_role_snapshot_always_solve);
        assert_eq!(args, VecDeque::from([OsString::from("check-poly")]));
    }
}
