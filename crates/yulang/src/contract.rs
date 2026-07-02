use std::collections::VecDeque;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{self, Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::Deserialize;

use crate::support::{format_route_error, print_usage_error_and_exit};

pub(super) fn run(program: &str, std_root: Option<PathBuf>, args: VecDeque<OsString>) {
    let options = ContractOptions { std_root };
    let contract_args = parse_contract_args(program, args);
    let manifest = read_contract_manifest(&contract_args.manifest);
    contract_args.validate_contract_filters(&manifest);
    let repo_root = contract_args
        .repo_root
        .clone()
        .unwrap_or_else(|| default_contract_repo_root(&contract_args.manifest));

    let mut checked = 0usize;
    for case in manifest.case {
        if !contract_args.matches(&case) {
            continue;
        }
        run_contract_case(&options, &repo_root, &case);
        checked += 1;
    }

    if checked == 0 {
        eprintln!(
            "contract manifest {} matched no cases for {}",
            contract_args.manifest.display(),
            contract_args.filter_label()
        );
        process::exit(1);
    }

    println!("contract cases ok: {checked}");
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ContractOptions {
    std_root: Option<PathBuf>,
}

impl ContractOptions {
    fn std_source_options(&self) -> yulang::StdSourceOptions {
        yulang::StdSourceOptions {
            std_root: self.std_root.clone(),
        }
    }
}

#[derive(Debug, Deserialize)]
struct ContractManifest {
    case: Vec<ContractCase>,
}

#[derive(Debug, Deserialize)]
struct ContractCase {
    name: String,
    file: String,
    kind: String,
    root: Option<String>,
    std: Option<String>,
    expect_success: Option<bool>,
    print_roots: Option<bool>,
    module: Option<String>,
    symbol: Option<String>,
    symbol_contains: Option<String>,
    expect_stdout: Option<String>,
    expect_stderr: Option<String>,
    expect_type: Option<String>,
    expect_diagnostic_count: Option<usize>,
    expect_diagnostic_code: Option<String>,
    expect_diagnostic_severity: Option<String>,
    expect_diagnostic_label: Option<String>,
    expect_diagnostic_start: Option<usize>,
    expect_diagnostic_end: Option<usize>,
    expect_diagnostic_related_count: Option<usize>,
    #[serde(default)]
    expect_stdout_contains: Vec<String>,
    #[serde(default)]
    expect_stderr_contains: Vec<String>,
    #[serde(default)]
    expect_type_contains: Vec<String>,
    #[serde(default)]
    deny_type_contains: Vec<String>,
    #[serde(default)]
    expect_diagnostic_related_origins: Vec<String>,
    #[serde(default)]
    contracts: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ContractArgs {
    manifest: PathBuf,
    repo_root: Option<PathBuf>,
    case_filter: Option<String>,
    contract_filters: Vec<String>,
}

impl ContractArgs {
    fn validate_contract_filters(&self, manifest: &ContractManifest) {
        for filter in &self.contract_filters {
            if manifest
                .case
                .iter()
                .any(|case| case.contracts.iter().any(|contract| contract == filter))
            {
                continue;
            }
            eprintln!(
                "contract manifest {} has no contract tag `{filter}`",
                self.manifest.display()
            );
            process::exit(1);
        }
    }

    fn matches(&self, case: &ContractCase) -> bool {
        if let Some(filter) = &self.case_filter {
            if &case.name != filter {
                return false;
            }
        }
        self.contract_filters
            .iter()
            .all(|filter| case.contracts.iter().any(|contract| contract == filter))
    }

    fn filter_label(&self) -> String {
        let mut parts = Vec::new();
        if let Some(filter) = &self.case_filter {
            parts.push(format!("case={filter}"));
        }
        parts.extend(
            self.contract_filters
                .iter()
                .map(|filter| format!("contract={filter}")),
        );
        if parts.is_empty() {
            "<all cases>".to_string()
        } else {
            parts.join(", ")
        }
    }
}

fn parse_contract_args(program: &str, mut args: VecDeque<OsString>) -> ContractArgs {
    let mut manifest = None;
    let mut repo_root = None;
    let mut case_filter = None;
    let mut contract_filters = Vec::new();
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--case") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "contract --case requires a value");
                };
                case_filter = Some(value.to_string_lossy().into_owned());
            }
            Some(value) if value.starts_with("--case=") => {
                let value = value.strip_prefix("--case=").unwrap_or_default();
                if value.is_empty() {
                    print_usage_error_and_exit(program, "contract --case requires a value");
                }
                case_filter = Some(value.to_string());
            }
            Some("--contract") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "contract --contract requires a tag");
                };
                let value = value.to_string_lossy().into_owned();
                if value.is_empty() {
                    print_usage_error_and_exit(program, "contract --contract requires a tag");
                }
                contract_filters.push(value);
            }
            Some(value) if value.starts_with("--contract=") => {
                let value = value.strip_prefix("--contract=").unwrap_or_default();
                if value.is_empty() {
                    print_usage_error_and_exit(program, "contract --contract requires a tag");
                }
                contract_filters.push(value.to_string());
            }
            Some("--repo-root") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "contract --repo-root requires a path");
                };
                repo_root = Some(PathBuf::from(value));
            }
            Some(value) if value.starts_with("--repo-root=") => {
                let value = value.strip_prefix("--repo-root=").unwrap_or_default();
                if value.is_empty() {
                    print_usage_error_and_exit(program, "contract --repo-root requires a path");
                }
                repo_root = Some(PathBuf::from(value));
            }
            Some(value) if value.starts_with("--") => {
                print_usage_error_and_exit(program, &format!("unknown contract option: {value}"));
            }
            _ => {
                if manifest.is_some() {
                    print_usage_error_and_exit(program, "contract takes exactly one manifest path");
                }
                manifest = Some(PathBuf::from(arg));
            }
        }
    }

    let Some(manifest) = manifest else {
        print_usage_error_and_exit(program, "contract requires a manifest path");
    };
    ContractArgs {
        manifest,
        repo_root,
        case_filter,
        contract_filters,
    }
}

fn read_contract_manifest(path: &Path) -> ContractManifest {
    let text = fs::read_to_string(path).unwrap_or_else(|error| {
        eprintln!(
            "failed to read contract manifest {}: {error}",
            path.display()
        );
        process::exit(1);
    });
    toml::from_str(&text).unwrap_or_else(|error| {
        eprintln!(
            "failed to parse contract manifest {}: {error}",
            path.display()
        );
        process::exit(1);
    })
}

fn default_contract_repo_root(manifest: &Path) -> PathBuf {
    let Some(dir) = manifest.parent() else {
        return env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    };
    if dir.file_name().is_some_and(|name| name == "yulang") {
        if let Some(tests_dir) = dir.parent() {
            if tests_dir.file_name().is_some_and(|name| name == "tests") {
                if let Some(repo_root) = tests_dir.parent() {
                    return repo_root.to_path_buf();
                }
            }
        }
    }
    env::current_dir().unwrap_or_else(|_| PathBuf::from("."))
}

fn run_contract_case(options: &ContractOptions, repo_root: &Path, case: &ContractCase) {
    match case.kind.as_str() {
        "run" => run_contract_run_case(options, repo_root, case),
        "check" => run_contract_check_case(options, repo_root, case),
        "public-signature" => run_contract_public_signature_case(options, repo_root, case),
        other => contract_fail(case, &format!("unsupported contract case kind `{other}`")),
    }
}

fn run_contract_run_case(options: &ContractOptions, repo_root: &Path, case: &ContractCase) {
    let root = contract_temp_root(&case.name);
    let _ = fs::remove_dir_all(&root);
    if let Err(error) = fs::create_dir_all(&root) {
        contract_fail(
            case,
            &format!("failed to create temp root {}: {error}", root.display()),
        );
    }
    let cache_root = root.join("cache-root");
    let entry = contract_case_entry(repo_root, case);
    let mut command = contract_child_command(options, case);
    command.env("YULANG_CACHE_DIR", &cache_root).arg("run");
    if case.print_roots.unwrap_or(true) {
        command.arg("--print-roots");
    }
    let output = contract_output(case, command.arg(&entry));
    assert_contract_status(case, &output);
    assert_contract_output(case, &output);
    let _ = fs::remove_dir_all(&root);
}

fn run_contract_check_case(options: &ContractOptions, repo_root: &Path, case: &ContractCase) {
    let entry = contract_case_entry(repo_root, case);
    let mut command = contract_child_command(options, case);
    command.arg("--no-cache").arg("check").arg(&entry);
    let output = contract_output(case, &mut command);
    assert_contract_status(case, &output);
    assert_contract_output(case, &output);
    assert_contract_diagnostics(options, case, &entry);
}

fn run_contract_public_signature_case(
    options: &ContractOptions,
    repo_root: &Path,
    case: &ContractCase,
) {
    let entry = contract_case_entry(repo_root, case);
    let source_options = options.std_source_options();
    let output = match (
        case.std.as_deref().unwrap_or("repo"),
        case.module.as_deref(),
    ) {
        ("repo", Some(module)) => {
            yulang::dump_poly_from_entry_with_std_in_module_options(&entry, module, &source_options)
        }
        ("repo", None) => yulang::dump_poly_from_entry_with_std_options(&entry, &source_options),
        ("none", None) => yulang::dump_poly_from_entry(&entry),
        ("none", Some(module)) => contract_fail(
            case,
            &format!("cannot request module `{module}` without std"),
        ),
        (other, _) => contract_fail(case, &format!("unsupported std mode `{other}`")),
    }
    .unwrap_or_else(|error| contract_fail(case, &format_route_error(&error)));

    let ty = contract_public_signature_type(case, &output);
    assert_contract_public_signature_type_is_clean(case, &ty);
    if let Some(expected) = &case.expect_type {
        assert_contract_eq(case, "type", &ty, expected);
    }
    for expected in &case.expect_type_contains {
        if !ty.contains(expected) {
            contract_fail(case, &format!("missing type fragment {expected:?}:\n{ty}"));
        }
    }
    for denied in &case.deny_type_contains {
        if ty.contains(denied) {
            contract_fail(
                case,
                &format!("leaked denied type fragment {denied:?}:\n{ty}"),
            );
        }
    }
}

fn contract_child_command(options: &ContractOptions, case: &ContractCase) -> Command {
    let exe = env::current_exe().unwrap_or_else(|error| {
        eprintln!("failed to resolve current yulang executable: {error}");
        process::exit(1);
    });
    let mut command = Command::new(exe);
    push_contract_std_args(&mut command, options, case);
    command
}

fn push_contract_std_args(command: &mut Command, options: &ContractOptions, case: &ContractCase) {
    match case.std.as_deref().unwrap_or("repo") {
        "repo" => {
            if let Some(std_root) = &options.std_root {
                command.arg("--std-root").arg(std_root);
            }
        }
        "none" => {
            command.arg("--no-prelude");
        }
        other => contract_fail(case, &format!("unsupported std mode `{other}`")),
    }
}

fn contract_output(case: &ContractCase, command: &mut Command) -> Output {
    command.output().unwrap_or_else(|error| {
        contract_fail(
            case,
            &format!("failed to run child yulang process: {error}"),
        )
    })
}

fn contract_case_entry(repo_root: &Path, case: &ContractCase) -> PathBuf {
    match case.root.as_deref().unwrap_or("tests/yulang") {
        "tests/yulang" => repo_root.join("tests/yulang").join(&case.file),
        "repo" => repo_root.join(&case.file),
        other => contract_fail(case, &format!("unsupported root mode `{other}`")),
    }
}

fn assert_contract_diagnostics(options: &ContractOptions, case: &ContractCase, entry: &Path) {
    let expects_diagnostic = case.expect_diagnostic_count.is_some()
        || case.expect_diagnostic_code.is_some()
        || case.expect_diagnostic_severity.is_some()
        || case.expect_diagnostic_label.is_some()
        || case.expect_diagnostic_start.is_some()
        || case.expect_diagnostic_end.is_some()
        || case.expect_diagnostic_related_count.is_some()
        || !case.expect_diagnostic_related_origins.is_empty();
    if !expects_diagnostic {
        return;
    }

    let source = fs::read_to_string(entry).unwrap_or_else(|error| {
        contract_fail(
            case,
            &format!(
                "failed to read diagnostic fixture {}: {error}",
                entry.display()
            ),
        )
    });
    let output = match case.std.as_deref().unwrap_or("repo") {
        "repo" => yulang::analyze_entry_source_with_std_options(
            entry,
            source,
            &options.std_source_options(),
        ),
        "none" => yulang::analyze_entry_source(entry, source),
        other => contract_fail(case, &format!("unsupported std mode `{other}`")),
    }
    .unwrap_or_else(|error| contract_fail(case, &format_route_error(&error)));
    let diagnostic = output
        .diagnostics
        .first()
        .unwrap_or_else(|| contract_fail(case, "expected a diagnostic payload"));

    if let Some(expected) = case.expect_diagnostic_count {
        assert_contract_usize_eq(case, "diagnostic count", output.diagnostics.len(), expected);
    }
    if let Some(expected) = &case.expect_diagnostic_code {
        assert_contract_optional_str_eq(
            case,
            "diagnostic code",
            diagnostic.code.as_deref(),
            expected,
        );
    }
    if let Some(expected) = &case.expect_diagnostic_severity {
        assert_contract_eq(
            case,
            "diagnostic severity",
            contract_diagnostic_severity_name(diagnostic.severity),
            expected,
        );
    }
    if let Some(expected) = &case.expect_diagnostic_label {
        assert_contract_optional_str_eq(
            case,
            "diagnostic label",
            diagnostic.label.as_deref(),
            expected,
        );
    }
    if case.expect_diagnostic_start.is_some() || case.expect_diagnostic_end.is_some() {
        let range = diagnostic
            .range
            .unwrap_or_else(|| contract_fail(case, "expected a diagnostic primary range"));
        if let Some(expected) = case.expect_diagnostic_start {
            assert_contract_usize_eq(case, "diagnostic start", range.start, expected);
        }
        if let Some(expected) = case.expect_diagnostic_end {
            assert_contract_usize_eq(case, "diagnostic end", range.end, expected);
        }
    }
    if let Some(expected) = case.expect_diagnostic_related_count {
        assert_contract_usize_eq(
            case,
            "diagnostic related count",
            diagnostic.related.len(),
            expected,
        );
    }
    if !case.expect_diagnostic_related_origins.is_empty() {
        let origins = diagnostic
            .related
            .iter()
            .map(|related| contract_related_origin_name(related.origin.as_ref()))
            .collect::<Vec<_>>();
        if origins != case.expect_diagnostic_related_origins {
            contract_fail(
                case,
                &format!(
                    "diagnostic related origins mismatch\nexpected: {:?}\nactual:   {:?}",
                    case.expect_diagnostic_related_origins, origins
                ),
            );
        }
    }
}

fn contract_related_origin_name(
    origin: Option<&yulang::SourceDiagnosticRelatedOrigin>,
) -> &'static str {
    match origin {
        Some(yulang::SourceDiagnosticRelatedOrigin::TypeAnnotation) => "type-annotation",
        Some(yulang::SourceDiagnosticRelatedOrigin::Expression) => "expression",
        None => "none",
    }
}

fn contract_diagnostic_severity_name(severity: yulang::SourceDiagnosticSeverity) -> &'static str {
    match severity {
        yulang::SourceDiagnosticSeverity::Error => "error",
    }
}

fn contract_public_signature_type(case: &ContractCase, output: &yulang::DumpPolyOutput) -> String {
    match (&case.symbol, &case.symbol_contains) {
        (Some(symbol), None) => contract_dump_public_signature_type(output, symbol).to_string(),
        (None, Some(needle)) => {
            contract_dump_public_signature_type_containing(output, needle).to_string()
        }
        _ => contract_fail(
            case,
            "public-signature case must set exactly one of symbol or symbol_contains",
        ),
    }
}

fn contract_dump_public_signature_type<'a>(
    output: &'a yulang::DumpPolyOutput,
    symbol: &str,
) -> &'a str {
    let signature = contract_dump_public_signature(output, symbol);
    let quoted = format!("\"{symbol}\": ");
    if let Some(start) = signature.find(&quoted) {
        return &signature[start + quoted.len()..];
    }
    let simple = format!(":{symbol}: ");
    if let Some(start) = signature.find(&simple) {
        return &signature[start + simple.len()..];
    }
    eprintln!("public symbol {symbol:?} has an unexpected signature line:\n{signature}");
    process::exit(1);
}

fn contract_dump_public_signature<'a>(output: &'a yulang::DumpPolyOutput, symbol: &str) -> &'a str {
    let quoted = format!("\"{symbol}\"");
    let simple = (!symbol.contains('.')).then(|| format!(":{symbol}:"));
    let line = output
        .text
        .lines()
        .find(|line| {
            if !line.trim_start().starts_with("pub ") {
                return false;
            }
            line.contains(&quoted) || simple.as_ref().is_some_and(|simple| line.contains(simple))
        })
        .unwrap_or_else(|| {
            eprintln!(
                "public symbol {symbol:?} should be dumped:\n{}",
                output.text
            );
            process::exit(1);
        });
    contract_trim_public_signature_body(line)
}

fn contract_dump_public_signature_type_containing<'a>(
    output: &'a yulang::DumpPolyOutput,
    needle: &str,
) -> &'a str {
    let signature = contract_dump_public_signature_containing(output, needle);
    let Some(start) = signature.find("\": ") else {
        eprintln!("public signature containing {needle:?} is not quoted:\n{signature}");
        process::exit(1);
    };
    &signature[start + "\": ".len()..]
}

fn contract_dump_public_signature_containing<'a>(
    output: &'a yulang::DumpPolyOutput,
    needle: &str,
) -> &'a str {
    let line = output
        .text
        .lines()
        .find(|line| line.trim_start().starts_with("pub ") && line.contains(needle))
        .unwrap_or_else(|| {
            eprintln!(
                "public signature containing {needle:?} should be dumped:\n{}",
                output.text
            );
            process::exit(1);
        });
    contract_trim_public_signature_body(line)
}

fn contract_trim_public_signature_body(line: &str) -> &str {
    line.find(" = e")
        .or_else(|| line.find(" = <missing>"))
        .map(|body_start| &line[..body_start])
        .unwrap_or(line)
}

fn assert_contract_public_signature_type_is_clean(case: &ContractCase, ty: &str) {
    for denied in ["#", "AllExcept", "Unknown", "Any"] {
        if ty.contains(denied) {
            contract_fail(
                case,
                &format!("leaked private public-signature fragment {denied:?}:\n{ty}"),
            );
        }
    }
}

fn assert_contract_status(case: &ContractCase, output: &Output) {
    let expected_success = case.expect_success.unwrap_or(true);
    if output.status.success() != expected_success {
        contract_fail(
            case,
            &format!(
                "status mismatch\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
                output.status,
                contract_stdout(output),
                contract_stderr(output)
            ),
        );
    }
}

fn assert_contract_output(case: &ContractCase, output: &Output) {
    let stdout = contract_stdout(output);
    let stderr = contract_stderr(output);

    if let Some(expected) = &case.expect_stdout {
        assert_contract_eq(case, "stdout", &stdout, expected);
    }
    if let Some(expected) = &case.expect_stderr {
        assert_contract_eq(case, "stderr", &stderr, expected);
    }
    for expected in &case.expect_stdout_contains {
        if !stdout.contains(expected) {
            contract_fail(
                case,
                &format!("missing stdout fragment {expected:?}:\n{stdout}"),
            );
        }
    }
    for expected in &case.expect_stderr_contains {
        if !stderr.contains(expected) {
            contract_fail(
                case,
                &format!("missing stderr fragment {expected:?}:\n{stderr}"),
            );
        }
    }
}

fn assert_contract_optional_str_eq(
    case: &ContractCase,
    label: &str,
    actual: Option<&str>,
    expected: &str,
) {
    if actual != Some(expected) {
        contract_fail(
            case,
            &format!("{label} mismatch\nexpected: {expected:?}\nactual:   {actual:?}"),
        );
    }
}

fn assert_contract_usize_eq(case: &ContractCase, label: &str, actual: usize, expected: usize) {
    if actual != expected {
        contract_fail(
            case,
            &format!("{label} mismatch\nexpected: {expected}\nactual:   {actual}"),
        );
    }
}

fn assert_contract_eq(case: &ContractCase, label: &str, actual: &str, expected: &str) {
    if actual != expected {
        contract_fail(
            case,
            &format!("{label} mismatch\nexpected:\n{expected}\nactual:\n{actual}"),
        );
    }
}

fn contract_stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).to_string()
}

fn contract_stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).to_string()
}

fn contract_temp_root(name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    env::temp_dir().join(format!("yulang-contract-{name}-{nanos}"))
}

fn contract_fail(case: &ContractCase, message: &str) -> ! {
    eprintln!("contract case {} failed: {message}", case.name);
    process::exit(1);
}
