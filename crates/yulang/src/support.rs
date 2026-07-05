use super::*;
use std::io::IsTerminal as _;

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
) -> (RunInput, RunSelection) {
    let mut path = None;
    let mut source = None;
    let mut selection = RunSelection::default();
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--print-roots") => {
                selection.print_roots = true;
            }
            Some("--runtime-evidence-profile-deep") => {
                selection.runtime_evidence_profile_deep = true;
            }
            Some("--interpreter") => {
                set_run_backend(program, &mut selection, RunBackend::Mono, "--interpreter");
            }
            Some("--evidence-vm") => {
                set_run_backend(
                    program,
                    &mut selection,
                    RunBackend::EvidenceVm,
                    "--evidence-vm",
                );
            }
            Some("--host") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(
                        program,
                        "run --host requires native, unsupported, or mock-server",
                    );
                };
                selection.host = parse_run_host_mode_or_exit(program, &value);
            }
            Some(value) if value.starts_with("--host=") => {
                let value = value.strip_prefix("--host=").unwrap_or_default();
                selection.host = parse_run_host_mode_str_or_exit(program, value);
            }
            Some("-e") | Some("--eval") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "run -e requires source text");
                };
                set_run_source(program, &mut source, value);
            }
            Some(value) if value.starts_with("--eval=") => {
                let value = value.strip_prefix("--eval=").unwrap_or_default();
                if value.is_empty() {
                    print_usage_error_and_exit(program, "run --eval requires source text");
                }
                set_run_source(program, &mut source, OsString::from(value));
            }
            Some(flag) if flag.starts_with("--") => {
                print_usage_error_and_exit(program, &format!("unsupported run option {flag}"));
            }
            _ => set_single_path(program, &mut path, arg),
        }
    }
    let input = match (path, source) {
        (Some(_), Some(_)) => {
            print_usage_error_and_exit(program, "run accepts either a path, -, or -e source")
        }
        (Some(path), None) if path == PathBuf::from("-") => RunInput::Source {
            path: stdin_virtual_path(),
            source: read_source_or_exit(None),
        },
        (Some(path), None) => RunInput::Path(path),
        (None, Some(source)) => RunInput::Source {
            path: eval_virtual_path(),
            source,
        },
        (None, None) if !io::stdin().is_terminal() => RunInput::Source {
            path: stdin_virtual_path(),
            source: read_source_or_exit(None),
        },
        (None, None) => print_usage_and_exit(program),
    };
    (input, selection)
}

fn set_run_backend(program: &str, selection: &mut RunSelection, backend: RunBackend, flag: &str) {
    if selection.backend_explicit && selection.backend != backend {
        print_usage_error_and_exit(program, &format!("conflicting run backend option {flag}"));
    }
    selection.backend = backend;
    selection.backend_explicit = true;
}

fn parse_run_host_mode_or_exit(program: &str, value: &OsString) -> RunHostMode {
    let Some(value) = value.to_str() else {
        print_usage_error_and_exit(program, "run --host value must be UTF-8");
    };
    parse_run_host_mode_str_or_exit(program, value)
}

fn parse_run_host_mode_str_or_exit(program: &str, value: &str) -> RunHostMode {
    match value {
        "native" => RunHostMode::Native,
        "unsupported" => RunHostMode::Unsupported,
        "mock-server" => RunHostMode::MockServer,
        _ => print_usage_error_and_exit(
            program,
            &format!(
                "unknown run --host value {value:?}; expected native, unsupported, or mock-server"
            ),
        ),
    }
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
            Some("--control-evidence") | Some("--evidence-ir") => {
                selection.control_evidence = true;
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
    if !selection.poly && !selection.poly_raw && !selection.mono && !selection.control_evidence {
        print_usage_error_and_exit(
            program,
            "dump requires at least one of --core-ir, --runtime-ir, --poly, --poly-raw, --mono, --control-evidence",
        );
    }
    let Some(path) = path else {
        print_usage_and_exit(program);
    };
    (path, selection)
}

pub(super) fn print_selected_dump_without_std(
    path: PathBuf,
    selection: DumpSelection,
    use_cache: bool,
) {
    let files = run_route_to_value(yulang::collect_local_sources(path));
    if selection.poly {
        let output = dump_poly_with_optional_cache(files.clone(), false, use_cache);
        print_dump_poly_output(&output);
    }
    if selection.poly_raw {
        let output = dump_poly_with_optional_cache(files.clone(), true, use_cache);
        print_dump_poly_output(&output);
    }
    if selection.mono {
        let output = dump_mono_with_optional_cache(files.clone(), use_cache);
        print_dump_mono_output(&output);
    }
    if selection.control_evidence {
        let output = dump_control_evidence_with_optional_cache(files, use_cache);
        print_dump_mono_output(&output);
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
        let output = dump_mono_with_optional_cache(files.clone(), use_cache);
        print_dump_mono_output(&output);
    }
    if selection.control_evidence {
        let output = dump_control_evidence_with_optional_cache(files, use_cache);
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

fn set_run_source(program: &str, source: &mut Option<String>, value: OsString) {
    if source.is_some() {
        print_usage_and_exit(program);
    }
    let Some(value) = value.to_str() else {
        print_usage_error_and_exit(program, "run source text must be UTF-8");
    };
    *source = Some(value.to_string());
}

fn stdin_virtual_path() -> PathBuf {
    PathBuf::from("<stdin>.yu")
}

fn eval_virtual_path() -> PathBuf {
    PathBuf::from("<eval>.yu")
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

pub(super) struct CliEvidenceRunOutput {
    pub text: String,
    pub stdout: String,
    pub errors: Vec<String>,
    pub stats: evidence_vm::RuntimeEvidenceRunStats,
    pub timings: CliEvidenceRunTimings,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct CliEvidenceRunTimings {
    pub plan_build: Duration,
    pub plan_profile: evidence_vm::EvidenceVmPlanBuildProfile,
    pub execute: Duration,
    pub root_format: Duration,
}

pub(super) fn run_built_evidence_for_cli(
    build: yulang::BuildControlOutput,
) -> CliEvidenceRunOutput {
    run_built_evidence_for_cli_with_host(build, RunHostMode::Native)
}

pub(super) fn run_built_evidence_for_cli_with_host(
    build: yulang::BuildControlOutput,
    host: RunHostMode,
) -> CliEvidenceRunOutput {
    run_built_evidence_for_cli_with_host_profile(build, host, false)
}

pub(super) fn run_built_evidence_for_cli_with_host_profile(
    build: yulang::BuildControlOutput,
    host: RunHostMode,
    deep_profile: bool,
) -> CliEvidenceRunOutput {
    run_built_evidence_for_cli_with_host_profile_and_plan_profile(build, host, deep_profile, false)
}

pub(super) fn run_built_evidence_for_cli_with_host_profile_and_plan_profile(
    build: yulang::BuildControlOutput,
    host: RunHostMode,
    deep_profile: bool,
    plan_profile_enabled: bool,
) -> CliEvidenceRunOutput {
    run_runtime_on_cli_stack(move || {
        let yulang::BuildControlOutput {
            program,
            runtime_evidence,
            labels,
            file_count: _,
            errors,
        } = build;

        let plan_start = Instant::now();
        let (plan, plan_profile) = if plan_profile_enabled {
            evidence_vm::build_plan_with_profile(&program, &runtime_evidence)
        } else {
            (
                evidence_vm::build_plan(&program, &runtime_evidence),
                evidence_vm::EvidenceVmPlanBuildProfile::default(),
            )
        };
        let plan_build = plan_start.elapsed();

        let run_start = Instant::now();
        let run_result = match host {
            RunHostMode::Native => {
                if deep_profile {
                    evidence_vm::run_program_with_plan_deep_profile_with_labels_flushing_stdout_on_external_wait(
                        &program,
                        &plan,
                        true,
                        &labels,
                    )
                } else {
                    evidence_vm::run_program_with_plan_with_labels_flushing_stdout_on_external_wait(
                        &program, &plan, &labels,
                    )
                }
            }
            RunHostMode::Unsupported => {
                if deep_profile {
                    evidence_vm::run_program_with_plan_deep_profile_without_native_host_operations_with_labels(
                        &program,
                        &plan,
                        true,
                        &labels,
                    )
                } else {
                    evidence_vm::run_program_with_plan_without_native_host_operations_with_labels(
                        &program, &plan, &labels,
                    )
                }
            }
            RunHostMode::MockServer => {
                if deep_profile {
                    evidence_vm::run_program_with_plan_deep_profile_with_in_process_server_host_with_labels(
                        &program,
                        &plan,
                        true,
                        &labels,
                    )
                } else {
                    evidence_vm::run_program_with_plan_with_in_process_server_host_with_labels(
                        &program, &plan, &labels,
                    )
                }
            }
        };
        let output = match run_result {
            Ok(output) => output,
            Err(error) => {
                eprintln!("{}", format_runtime_evidence_run_error(&error));
                process::exit(1);
            }
        };
        let execute = run_start.elapsed();

        let root_format_start = Instant::now();
        let text = output.roots_text_with_labels(Some(&labels));
        let root_format = root_format_start.elapsed();

        CliEvidenceRunOutput {
            text,
            stdout: output.stdout,
            errors,
            stats: output.evidence_stats,
            timings: CliEvidenceRunTimings {
                plan_build,
                plan_profile,
                execute,
                root_format,
            },
        }
    })
}

fn format_runtime_evidence_run_error(error: &evidence_vm::RuntimeEvidenceRunError) -> String {
    match error {
        evidence_vm::RuntimeEvidenceRunError::EscapedEffect(path) => format!(
            "runtime error [yulang.unhandled-effect]: unhandled effect request {}\n  hint: handle this computation with a matching effect handler before running it",
            path.join("::")
        ),
        evidence_vm::RuntimeEvidenceRunError::UnsupportedHostCapability(path) => format!(
            "runtime error [yulang.unsupported-host-capability]: host capability {} is not available in this runtime\n  hint: use a host that grants this capability or handle the capability with a mock effect handler",
            path.join("::")
        ),
        evidence_vm::RuntimeEvidenceRunError::HostIoError {
            operation,
            path,
            kind,
        } => format!(
            "runtime error [yulang.host-io-error]: host operation {} failed for {path} ({kind})\n  hint: check that the target path exists and that this process has the required file permissions",
            operation.join("::")
        ),
        evidence_vm::RuntimeEvidenceRunError::HostAbiError { operation, message } => format!(
            "runtime error [yulang.host-abi-error]: host operation {} failed ({message})\n  hint: this host implementation returned a value outside its ABI contract",
            operation.join("::")
        ),
        evidence_vm::RuntimeEvidenceRunError::NotFunction(value) => format!(
            "runtime error [yulang.not-callable]: tried to call a non-function value {value}\n  hint: check the expression before the argument; calls are written as `f x` or `f(...)`"
        ),
        evidence_vm::RuntimeEvidenceRunError::NotRecord(value) => format!(
            "runtime error [yulang.not-record]: tried to read fields from non-record value {value}\n  hint: use `.field` only on record values"
        ),
        evidence_vm::RuntimeEvidenceRunError::PatternMismatch => {
            "runtime error [yulang.pattern-mismatch]: no pattern matched the value\n  hint: add a fallback pattern such as `_ -> ...`".to_string()
        }
        evidence_vm::RuntimeEvidenceRunError::MissingRecordField(name) => format!(
            "runtime error [yulang.missing-field]: record does not contain field `{name}`\n  hint: check the field name or provide a record value with this field"
        ),
        evidence_vm::RuntimeEvidenceRunError::DivideByZero => {
            "runtime error [yulang.divide-by-zero]: attempted to divide by zero\n  hint: check the divisor before division".to_string()
        }
        evidence_vm::RuntimeEvidenceRunError::NotThunk(value) => format!(
            "runtime error [yulang.runtime-internal]: expected a delayed computation, got {value}\n  hint: report this with the source program if it came from normal `yulang run`"
        ),
        evidence_vm::RuntimeEvidenceRunError::UnsupportedExpr(feature) => format!(
            "runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: {feature}\n  hint: try the interpreter oracle or reduce this source to a smaller report"
        ),
        evidence_vm::RuntimeEvidenceRunError::UnsupportedPrimitive(op) => format!(
            "runtime error [yulang.unsupported-runtime-feature]: unsupported primitive in runtime: {op:?}\n  hint: this primitive is not available in the selected runtime"
        ),
        evidence_vm::RuntimeEvidenceRunError::MissingExpr(_)
        | evidence_vm::RuntimeEvidenceRunError::MissingInstance(_)
        | evidence_vm::RuntimeEvidenceRunError::MismatchedInstanceSlot { .. }
        | evidence_vm::RuntimeEvidenceRunError::RecursiveInstance(_)
        | evidence_vm::RuntimeEvidenceRunError::UnboundLocal(_) => format!(
            "runtime error [yulang.runtime-internal]: {error}\n  hint: report this with the source program if it came from normal `yulang run`"
        ),
    }
}

// The VM runtimes still have recursive eval/apply paths. CLI execution isolates
// those paths on a dedicated stack until the runtimes are fully trampolined.
const RUNTIME_CLI_STACK_SIZE: usize = 256 * 1024 * 1024;

#[cfg(not(target_arch = "wasm32"))]
fn run_runtime_on_cli_stack<T: Send>(run: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        let handle = std::thread::Builder::new()
            .name("yulang-runtime".to_string())
            .stack_size(RUNTIME_CLI_STACK_SIZE)
            .spawn_scoped(scope, run)
            .unwrap_or_else(|error| {
                eprintln!("failed to start runtime thread: {error}");
                process::exit(1);
            });
        match handle.join() {
            Ok(output) => output,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    })
}

#[cfg(target_arch = "wasm32")]
fn run_runtime_on_cli_stack<T: Send>(run: impl FnOnce() -> T + Send) -> T {
    run()
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
            eprintln!("{}", format_route_error(&error));
            process::exit(1);
        }
    }
}

pub(super) fn run_route_to_value<T>(result: Result<T, yulang::RouteError>) -> T {
    match result {
        Ok(output) => output,
        Err(error) => {
            eprintln!("{}", format_route_error(&error));
            process::exit(1);
        }
    }
}

pub(super) fn format_runtime_lowering_errors(errors: &[String]) -> String {
    format_route_error(&yulang::RouteError::LoweringDiagnostics {
        errors: errors.to_vec(),
    })
}

pub(super) fn format_route_error(error: &yulang::RouteError) -> String {
    match error {
        yulang::RouteError::Specialize(specialize::SpecializeError::UnsatisfiedSubtype {
            origin:
                Some(specialize::UnsatisfiedSubtypeOrigin::MissingRecordField {
                    field,
                    actual_fields,
                }),
            ..
        }) => {
            let actual = if actual_fields.is_empty() {
                "no fields".to_string()
            } else {
                format!("fields {}", actual_fields.join(", "))
            };
            format!(
                "compile error [yulang.unsatisfied-subtype]: record is missing field `{field}`\n  detail: {error}\n  hint: add `{field}` to this record or use a value that provides it; actual record has {actual}"
            )
        }
        yulang::RouteError::Specialize(specialize::SpecializeError::UnsatisfiedSubtype {
            ..
        }) => {
            format!(
                "compile error [yulang.unsatisfied-subtype]: {error}\n  hint: check that the value provides the fields or shape required by this use"
            )
        }
        yulang::RouteError::Specialize(
            specialize::SpecializeError::UnresolvedTypeclassMethod { .. },
        ) => {
            format!(
                "compile error [yulang.unresolved-method]: no role implementation satisfies this method call\n  detail: {error}\n  hint: add or import an impl for the receiver type, or call a method supported by that value"
            )
        }
        yulang::RouteError::Specialize(specialize::SpecializeError::AmbiguousTypeclassMethod {
            ..
        }) => {
            format!(
                "compile error [yulang.ambiguous-method]: more than one role implementation satisfies this method call\n  detail: {error}\n  hint: make the receiver type more specific or keep only one matching impl in scope"
            )
        }
        yulang::RouteError::Runtime(error) => format_mono_runtime_error(error),
        _ => error.to_string(),
    }
}

pub(super) fn format_mono_runtime_error(error: &mono_runtime::RuntimeError) -> String {
    match error {
        mono_runtime::RuntimeError::UnhandledEffect { path } => {
            format_unhandled_effect_runtime_error(path)
        }
        mono_runtime::RuntimeError::NotFunction { value } => {
            format_not_callable_runtime_error(&format_mono_runtime_value(value))
        }
        mono_runtime::RuntimeError::ExpectedRecord { value } => {
            format_not_record_runtime_error(&format_mono_runtime_value(value))
        }
        mono_runtime::RuntimeError::MissingRecordField { name } => {
            format_missing_field_runtime_error(name)
        }
        mono_runtime::RuntimeError::PatternMismatch
        | mono_runtime::RuntimeError::NoMatchingCase => format_pattern_mismatch_runtime_error(),
        mono_runtime::RuntimeError::NonBoolGuard { value } => {
            format_non_bool_guard_runtime_error(&format_mono_runtime_value(value))
        }
        mono_runtime::RuntimeError::ExpectedInt { value } => {
            format_expected_runtime_type_error("int", &format_mono_runtime_value(value))
        }
        mono_runtime::RuntimeError::ExpectedFloat { value } => {
            format_expected_runtime_type_error("float", &format_mono_runtime_value(value))
        }
        mono_runtime::RuntimeError::ExpectedBool { value } => {
            format_expected_runtime_type_error("bool", &format_mono_runtime_value(value))
        }
        mono_runtime::RuntimeError::ExpectedList { value } => {
            format_expected_runtime_type_error("list", &format_mono_runtime_value(value))
        }
        mono_runtime::RuntimeError::ExpectedBytes { value } => {
            format_expected_runtime_type_error("bytes", &format_mono_runtime_value(value))
        }
        mono_runtime::RuntimeError::UnsupportedExpr { feature }
        | mono_runtime::RuntimeError::UnsupportedPattern { feature }
        | mono_runtime::RuntimeError::UnsupportedBoundary { feature } => {
            format_unsupported_runtime_feature_error(feature)
        }
        mono_runtime::RuntimeError::MissingPrimitiveContext { op }
        | mono_runtime::RuntimeError::UnsupportedPrimitive { op } => format!(
            "runtime error [yulang.unsupported-runtime-feature]: unsupported primitive in runtime: {op:?}\n  hint: this primitive is not available in the selected runtime"
        ),
        mono_runtime::RuntimeError::ExpectedFunctionType
        | mono_runtime::RuntimeError::NotThunk { .. }
        | mono_runtime::RuntimeError::MissingInstance { .. }
        | mono_runtime::RuntimeError::MismatchedInstanceSlot { .. }
        | mono_runtime::RuntimeError::RecursiveInstance { .. }
        | mono_runtime::RuntimeError::UnboundLocal { .. }
        | mono_runtime::RuntimeError::MissingContinuation { .. }
        | mono_runtime::RuntimeError::UnresolvedSelect { .. } => {
            format_internal_runtime_error(&error.to_string())
        }
    }
}

fn format_unhandled_effect_runtime_error(path: &[String]) -> String {
    format!(
        "runtime error [yulang.unhandled-effect]: unhandled effect request {}\n  hint: handle this computation with a matching effect handler before running it",
        path.join("::")
    )
}

fn format_not_callable_runtime_error(value: &str) -> String {
    format!(
        "runtime error [yulang.not-callable]: tried to call a non-function value {value}\n  hint: check the expression before the argument; calls are written as `f x` or `f(...)`"
    )
}

fn format_not_record_runtime_error(value: &str) -> String {
    format!(
        "runtime error [yulang.not-record]: tried to read fields from non-record value {value}\n  hint: use `.field` only on record values"
    )
}

fn format_missing_field_runtime_error(name: &str) -> String {
    format!(
        "runtime error [yulang.missing-field]: record does not contain field `{name}`\n  hint: check the field name or provide a record value with this field"
    )
}

fn format_pattern_mismatch_runtime_error() -> String {
    "runtime error [yulang.pattern-mismatch]: no pattern matched the value\n  hint: add a fallback pattern such as `_ -> ...`".to_string()
}

fn format_non_bool_guard_runtime_error(value: &str) -> String {
    format!(
        "runtime error [yulang.non-bool-guard]: case guard returned non-bool value {value}\n  hint: make the guard return true or false"
    )
}

fn format_expected_runtime_type_error(expected: &str, actual: &str) -> String {
    format!(
        "runtime error [yulang.runtime-type]: expected {expected}, got {actual}\n  hint: check the value passed to this operation"
    )
}

fn format_unsupported_runtime_feature_error(feature: &str) -> String {
    format!(
        "runtime error [yulang.unsupported-runtime-feature]: unsupported runtime feature: {feature}\n  hint: try the interpreter oracle or reduce this source to a smaller report"
    )
}

fn format_internal_runtime_error(detail: &str) -> String {
    format!(
        "runtime error [yulang.runtime-internal]: {detail}\n  hint: report this with the source program if it came from normal `yulang run`"
    )
}

fn format_mono_runtime_value(value: &mono_runtime::Value) -> String {
    let text = yulang::format_run_mono_values(std::slice::from_ref(value));
    text.strip_prefix("run roots [")
        .and_then(|text| text.strip_suffix("]\n"))
        .unwrap_or(text.trim())
        .to_string()
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

pub(super) fn print_cli_evidence_run_output_with_roots(
    output: &CliEvidenceRunOutput,
    print_roots: bool,
) {
    print!("{}", output.stdout);
    if print_roots {
        print!("{}", output.text);
    }
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

pub(super) fn print_check_poly_output(output: &yulang::CheckPolyOutput) {
    print_check_diagnostics_summary(&output.diagnostics, output.diagnostic_source.as_ref());
    print!("{}", output.text);
}

pub(super) fn print_check_diagnostics_summary(
    diagnostics: &[yulang::SourceDiagnostic],
    source: Option<&yulang::CheckDiagnosticSource>,
) {
    if diagnostics.is_empty() {
        return;
    }
    println!("diagnostics:");
    for diagnostic in diagnostics {
        let severity = source_diagnostic_severity_name(diagnostic.severity);
        match (diagnostic.code.as_deref(), diagnostic.label.as_deref()) {
            (Some(code), Some(label)) => {
                println!("  {severity} [{code}]: {label}: {}", diagnostic.message)
            }
            (Some(code), None) => println!("  {severity} [{code}]: {}", diagnostic.message),
            (None, Some(label)) => println!("  {severity}: {label}: {}", diagnostic.message),
            (None, None) => println!("  {severity}: {}", diagnostic.message),
        }
        if let Some(range) = diagnostic.range {
            print_source_frame(source, range);
        }
        if let Some(hint) = &diagnostic.hint {
            println!("    hint: {hint}");
        }
        for related in &diagnostic.related {
            println!("    note: {}", related.message);
            print_source_frame(source, related.range);
        }
    }
}

fn source_diagnostic_severity_name(severity: yulang::SourceDiagnosticSeverity) -> &'static str {
    match severity {
        yulang::SourceDiagnosticSeverity::Error => "error",
    }
}

fn print_source_frame(source: Option<&yulang::CheckDiagnosticSource>, range: yulang::SourceRange) {
    let Some(source) = source else {
        return;
    };
    let Some(range) = diagnostic_display_range(source, range) else {
        return;
    };
    let Some(frame) = source_frame(&source.source, range) else {
        return;
    };
    let number_width = frame.line_number.to_string().len();
    println!(
        "    --> line {}, column {}",
        frame.line_number, frame.column_number
    );
    println!(
        "    {:>number_width$} | {}",
        frame.line_number, frame.line_text
    );
    println!(
        "    {:>number_width$} | {}{}",
        "",
        " ".repeat(frame.marker_start),
        "^".repeat(frame.marker_len)
    );
}

fn diagnostic_display_range(
    source: &yulang::CheckDiagnosticSource,
    range: yulang::SourceRange,
) -> Option<yulang::SourceRange> {
    if range.end <= source.range_offset {
        return None;
    }
    let start = range.start.saturating_sub(source.range_offset);
    let end = range.end.saturating_sub(source.range_offset);
    Some(yulang::SourceRange {
        start: start.min(source.source.len()),
        end: end.max(start).min(source.source.len()),
    })
}

struct SourceFrame {
    line_number: usize,
    column_number: usize,
    line_text: String,
    marker_start: usize,
    marker_len: usize,
}

fn source_frame(source: &str, range: yulang::SourceRange) -> Option<SourceFrame> {
    let starts = source_line_starts(source);
    let line_index = starts
        .partition_point(|start| *start <= range.start)
        .saturating_sub(1);
    let line_start = *starts.get(line_index)?;
    let line_end = source[line_start..]
        .find('\n')
        .map(|offset| line_start + offset)
        .unwrap_or(source.len());
    let range_start = range.start.clamp(line_start, line_end);
    let range_end = range.end.clamp(range_start, line_end);
    let marker_start = source[line_start..range_start].chars().count();
    let marker_len = source[range_start..range_end].chars().count().max(1);
    Some(SourceFrame {
        line_number: line_index + 1,
        column_number: marker_start + 1,
        line_text: source[line_start..line_end].to_string(),
        marker_start,
        marker_len,
    })
}

fn source_line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    starts.extend(
        source
            .char_indices()
            .filter_map(|(index, ch)| (ch == '\n').then_some(index + 1)),
    );
    starts
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
        "       {program} [--std-root <path>] contract [--repo-root <path>] [--case <name>]... [--contract <tag>] <cases.toml>"
    );
    eprintln!(
        "       {program} [--std-root <path>] [--no-prelude] [--no-cache] build [--out <path>] <path>"
    );
    eprintln!(
        "       {program} [--std-root <path>] [--no-prelude] [--no-cache] run [--evidence-vm|--interpreter] [--host <native|unsupported|mock-server>] [--print-roots] [--runtime-evidence-profile-deep] [-e <source>|-|<path>]"
    );
    eprintln!(
        "       {program} [--std-root <path>] [--no-prelude] dump <path> (--core-ir | --runtime-ir | --poly | --poly-raw | --mono)"
    );
    eprintln!("       {program} parse [path] --as <expr|pat|stmt|type|mark>");
    eprintln!("       {program} [--std-root <path>] install std");
    eprintln!("       {program} cache <clear|path|stats>");
    eprintln!("       {program} realm freeze [path] --version <version>");
    eprintln!("       {program} realm install [path] [--version <version>]");
    eprintln!("       {program} [--std-root <path>] server");
    eprintln!(
        "       {program} debug <host-act-manifest|runtime-evidence-bench|runtime-evidence-run|evidence-vm-plan|evidence-vm-run> [--compare-mono] ..."
    );
    eprintln!("       {program} dump-poly <path>");
    eprintln!("       {program} dump-poly-raw <path>");
    eprintln!("       {program} dump-mono <path>");
    eprintln!("       {program} run-mono <path>");
    eprintln!("       {program} [--std-root <path>] dump-poly-std <path>");
    eprintln!("       {program} [--std-root <path>] dump-mono-std <path>");
    eprintln!("       {program} [--std-root <path>] run-mono-std <path>");
    eprintln!("       {program} [--std-root <path>] check-poly-std <path>");
    eprintln!("       {program} [--std-root <path>] check-poly-std-in <path> <module>");
    eprintln!("       {program} [--std-root <path>] dump-poly-std-in <path> <module>");
    eprintln!("       {program} [--std-root <path>] dump-poly-std-raw <path>");
    eprintln!("       {program} [--std-root <path>] dump-poly-std-in-raw <path> <module>");
    process::exit(2);
}
