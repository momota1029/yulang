use std::collections::{BTreeSet, VecDeque};
use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{self, Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::GlobalOptions;
use crate::support::{
    format_route_error, format_runtime_evidence_run_error,
    format_test_assertion_equality_failure_at_span, format_test_assertion_failure_at_span,
    print_usage_error_and_exit,
};

const ASSERTION_FAILURE_EXIT: i32 = 10;
const RUNTIME_FAILURE_EXIT: i32 = 11;
const ASSERTION_EQUALITY_FAILURE_EXIT: i32 = 12;

pub(super) fn run(program: &str, options: &GlobalOptions, args: VecDeque<OsString>) {
    let args = parse_test_args(program, args);
    let files = crate::collect_control_sources_or_exit(&args.entry, options);
    let build = yulang::build_test_control_from_collected_sources(files).unwrap_or_else(|error| {
        eprintln!("{}", format_route_error(&error));
        process::exit(1);
    });
    args.validate_filters(&build.test_modules);

    let module_cases = build.test_modules.iter().flat_map(|module| {
        module.bindings.iter().map(move |binding| TestCase {
            name: format!("{}::{}", module.name, binding.name),
            module: Some(module.name.clone()),
            binding: Some(binding.name.clone()),
            source_span: binding.source_span.clone(),
        })
    });
    let doc_cases = build.doc_tests.iter().map(|test| TestCase {
        name: test.name.clone(),
        module: None,
        binding: None,
        source_span: Some(test.source_span.clone()),
    });
    let selected = module_cases
        .chain(doc_cases)
        .enumerate()
        .filter(|(_, test)| args.matches(test))
        .collect::<Vec<_>>();
    if build.control.program.roots.len()
        != build
            .test_modules
            .iter()
            .map(|module| module.bindings.len())
            .sum::<usize>()
            + build.doc_tests.len()
    {
        eprintln!("internal test runner error: test binding/root count mismatch");
        process::exit(1);
    }

    let diagnostic_sources = build.control.diagnostic_sources.clone();
    let artifact_root = TestArtifactRoot::new();
    let cache = yulang::cache::ArtifactCache::new(artifact_root.path());
    let artifact = yulang::cache::CachedControlArtifact {
        program: build.control.program,
        runtime_evidence: build.control.runtime_evidence,
        application_provenance: build.control.application_provenance,
        selection_provenance: build.control.selection_provenance,
        labels: build.control.labels,
        file_count: build.control.file_count,
        errors: build.control.errors,
    };
    cache
        .write_control_artifact(test_worker_cache_key(), &artifact)
        .unwrap_or_else(|error| {
            eprintln!("failed to prepare test worker artifact: {error}");
            process::exit(1);
        });

    let mut passed = 0usize;
    let mut failed = 0usize;
    for (root_index, test) in selected {
        let output = run_test_worker(options, artifact_root.path(), root_index, &args.entry);
        if output.status.success() {
            print!("{}", String::from_utf8_lossy(&output.stdout));
            passed += 1;
            if args.show_passes {
                println!("PASS {}", test.name);
            }
            continue;
        }

        failed += 1;
        eprintln!("FAIL {}", test.name);
        let stderr = String::from_utf8_lossy(&output.stderr);
        if output.status.code() == Some(ASSERTION_FAILURE_EXIT)
            && let Some(source_span) = test.source_span.as_ref()
        {
            eprintln!(
                "{}",
                format_test_assertion_failure_at_span(source_span, &diagnostic_sources)
            );
        } else if output.status.code() == Some(ASSERTION_EQUALITY_FAILURE_EXIT)
            && let Some(source_span) = test.source_span.as_ref()
            && let Some((expected, actual)) = assertion_equality_failure_values(&stderr)
        {
            eprintln!(
                "{}",
                format_test_assertion_equality_failure_at_span(
                    source_span,
                    &diagnostic_sources,
                    expected,
                    actual,
                )
            );
        } else if stderr.is_empty() {
            eprintln!("runtime error: test worker exited with {}", output.status);
        } else {
            eprint!("{stderr}");
            if !stderr.ends_with('\n') {
                eprintln!();
            }
        }
        if !output.stdout.is_empty() {
            eprintln!("  captured stdout:");
            for line in String::from_utf8_lossy(&output.stdout).lines() {
                eprintln!("    {line}");
            }
        }
    }

    println!("test result: {passed} passed; {failed} failed");
    if failed != 0 {
        process::exit(1);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TestCase {
    name: String,
    module: Option<String>,
    binding: Option<String>,
    source_span: Option<infer::SourceSpan>,
}

pub(super) fn run_worker(program: &str, options: &GlobalOptions, mut args: VecDeque<OsString>) {
    let Some(artifact_root) = args.pop_front().map(PathBuf::from) else {
        print_usage_error_and_exit(program, "test worker requires an artifact root");
    };
    let Some(root_index) = args
        .pop_front()
        .and_then(|value| value.to_str().and_then(|value| value.parse::<usize>().ok()))
    else {
        print_usage_error_and_exit(program, "test worker requires a root index");
    };
    let Some(entry) = args.pop_front().map(PathBuf::from) else {
        print_usage_error_and_exit(program, "test worker requires an entry path");
    };
    if !args.is_empty() {
        print_usage_error_and_exit(program, "test worker received unexpected arguments");
    }

    let cache = yulang::cache::ArtifactCache::new(artifact_root);
    let Some(artifact) = cache
        .read_control_artifact(test_worker_cache_key())
        .unwrap_or_else(|error| {
            eprintln!("failed to read test worker artifact: {error}");
            process::exit(RUNTIME_FAILURE_EXIT);
        })
    else {
        eprintln!("test worker artifact is missing");
        process::exit(RUNTIME_FAILURE_EXIT);
    };
    let Some(root) = artifact.program.roots.get(root_index).cloned() else {
        eprintln!("test worker root index {root_index} is out of range");
        process::exit(RUNTIME_FAILURE_EXIT);
    };
    let files = crate::collect_control_sources_or_exit(&entry, options);
    let diagnostic_sources = yulang::RuntimeDiagnosticSources::from_collected_sources(&files);
    let mut program = artifact.program;
    program.roots = vec![root];
    let plan = evidence_vm::build_plan(&program, &artifact.runtime_evidence);
    match evidence_vm::run_test_program_with_plan_with_labels(&program, &plan, &artifact.labels) {
        Ok(output) => print!("{}", output.stdout),
        Err(error) => {
            let code = match &error {
                evidence_vm::RuntimeEvidenceRunError::AssertionFailed { .. } => {
                    eprintln!(
                        "{}",
                        format_runtime_evidence_run_error(
                            &error,
                            &artifact.application_provenance,
                            &artifact.selection_provenance,
                            &diagnostic_sources,
                        )
                    );
                    ASSERTION_FAILURE_EXIT
                }
                evidence_vm::RuntimeEvidenceRunError::AssertionEqualityFailed {
                    expected,
                    actual,
                    ..
                } => {
                    eprintln!("{expected}");
                    eprintln!("{actual}");
                    ASSERTION_EQUALITY_FAILURE_EXIT
                }
                _ => {
                    eprintln!(
                        "{}",
                        format_runtime_evidence_run_error(
                            &error,
                            &artifact.application_provenance,
                            &artifact.selection_provenance,
                            &diagnostic_sources,
                        )
                    );
                    RUNTIME_FAILURE_EXIT
                }
            };
            process::exit(code);
        }
    }
}

fn assertion_equality_failure_values(stderr: &str) -> Option<(&str, &str)> {
    let mut lines = stderr.lines();
    let expected = lines.next()?;
    let actual = lines.next()?;
    (lines.next().is_none()).then_some((expected, actual))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TestArgs {
    entry: PathBuf,
    module_filters: BTreeSet<String>,
    binding_filters: BTreeSet<String>,
    show_passes: bool,
}

impl TestArgs {
    fn validate_filters(&self, modules: &[yulang::SourceTestModule]) {
        for filter in &self.module_filters {
            if modules.iter().any(|module| &module.name == filter) {
                continue;
            }
            eprintln!("test source has no test module `{filter}`");
            process::exit(1);
        }
        for filter in &self.binding_filters {
            if modules
                .iter()
                .flat_map(|module| &module.bindings)
                .any(|binding| &binding.name == filter)
            {
                continue;
            }
            eprintln!("test source has no test binding `{filter}`");
            process::exit(1);
        }
    }

    fn matches(&self, test: &TestCase) -> bool {
        if test.module.is_none() {
            return self.module_filters.is_empty() && self.binding_filters.is_empty();
        }
        let module = test.module.as_deref().expect("module test has a module");
        let binding = test.binding.as_deref().expect("module test has a binding");
        (self.module_filters.is_empty() || self.module_filters.contains(module))
            && (self.binding_filters.is_empty() || self.binding_filters.contains(binding))
    }
}

fn parse_test_args(program: &str, mut args: VecDeque<OsString>) -> TestArgs {
    let mut entry = None;
    let mut module_filters = BTreeSet::new();
    let mut binding_filters = BTreeSet::new();
    let mut show_passes = false;
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--module") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "test --module requires a name");
                };
                module_filters.insert(value.to_string_lossy().into_owned());
            }
            Some(value) if value.starts_with("--module=") => {
                let value = value.trim_start_matches("--module=");
                if value.is_empty() {
                    print_usage_error_and_exit(program, "test --module requires a name");
                }
                module_filters.insert(value.to_string());
            }
            Some("--binding") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "test --binding requires a name");
                };
                binding_filters.insert(value.to_string_lossy().into_owned());
            }
            Some(value) if value.starts_with("--binding=") => {
                let value = value.trim_start_matches("--binding=");
                if value.is_empty() {
                    print_usage_error_and_exit(program, "test --binding requires a name");
                }
                binding_filters.insert(value.to_string());
            }
            Some("--show-passes") => show_passes = true,
            Some(value) if value.starts_with("--") => {
                print_usage_error_and_exit(program, &format!("unknown test option: {value}"));
            }
            _ => {
                if entry.is_some() {
                    print_usage_error_and_exit(program, "test takes exactly one entry path");
                }
                entry = Some(PathBuf::from(arg));
            }
        }
    }
    let Some(entry) = entry else {
        print_usage_error_and_exit(program, "test requires an entry path");
    };
    TestArgs {
        entry,
        module_filters,
        binding_filters,
        show_passes,
    }
}

fn run_test_worker(
    options: &GlobalOptions,
    artifact_root: &Path,
    root_index: usize,
    entry: &Path,
) -> Output {
    let exe = env::current_exe().unwrap_or_else(|error| {
        eprintln!("failed to resolve current yulang executable: {error}");
        process::exit(1);
    });
    let mut command = Command::new(exe);
    if let Some(std_root) = &options.std_root {
        command.arg("--std-root").arg(std_root);
    }
    if options.no_prelude {
        command.arg("--no-prelude");
    }
    command
        .env("YULANG_CACHE_DIR", artifact_root.join("worker-cache"))
        .arg("__test-worker")
        .arg(artifact_root)
        .arg(root_index.to_string())
        .arg(entry)
        .output()
        .unwrap_or_else(|error| {
            eprintln!("failed to run test worker: {error}");
            process::exit(1);
        })
}

fn test_worker_cache_key() -> yulang::cache::SourceCacheKey {
    yulang::cache::source_cache_key(&[yulang::CollectedSource::new(
        PathBuf::from("__yulang_test_worker__.yu"),
        sources::Path::default(),
        "TEST-B worker artifact".to_string(),
    )])
}

struct TestArtifactRoot {
    path: PathBuf,
}

impl TestArtifactRoot {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        let path = env::temp_dir().join(format!("yulang-test-runner-{}-{nonce}", process::id()));
        fs::create_dir_all(&path).unwrap_or_else(|error| {
            eprintln!(
                "failed to create test artifact root {}: {error}",
                path.display()
            );
            process::exit(1);
        });
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TestArtifactRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
