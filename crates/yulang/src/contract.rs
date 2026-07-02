use std::collections::{BTreeSet, VecDeque};
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
    validate_contract_manifest(&contract_args.manifest, &manifest);
    contract_args.validate_case_filters(&manifest);
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
    backend: Option<String>,
    host: Option<String>,
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
    temp_files: Vec<ContractTempFile>,
    #[serde(default)]
    contracts: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct ContractTempFile {
    placeholder: String,
    contents: Option<String>,
    #[serde(default)]
    missing: bool,
    #[serde(default)]
    directory: bool,
    expect_contents: Option<String>,
}

struct MaterializedContractRunCase {
    entry: PathBuf,
    temp_files: Vec<MaterializedContractTempFile>,
}

struct MaterializedContractTempFile {
    path: PathBuf,
    expect_contents: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ContractArgs {
    manifest: PathBuf,
    repo_root: Option<PathBuf>,
    case_filters: BTreeSet<String>,
    contract_filters: Vec<String>,
}

impl ContractArgs {
    fn validate_case_filters(&self, manifest: &ContractManifest) {
        for filter in &self.case_filters {
            if manifest.case.iter().any(|case| &case.name == filter) {
                continue;
            }
            eprintln!(
                "contract manifest {} has no case `{filter}`",
                self.manifest.display()
            );
            process::exit(1);
        }
    }

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
        if !self.case_filters.is_empty() && !self.case_filters.contains(&case.name) {
            return false;
        }
        self.contract_filters
            .iter()
            .all(|filter| case.contracts.iter().any(|contract| contract == filter))
    }

    fn filter_label(&self) -> String {
        let mut parts = Vec::new();
        parts.extend(
            self.case_filters
                .iter()
                .map(|filter| format!("case={filter}")),
        );
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
    let mut case_filters = BTreeSet::new();
    let mut contract_filters = Vec::new();
    while let Some(arg) = args.pop_front() {
        match arg.to_str() {
            Some("--case") => {
                let Some(value) = args.pop_front() else {
                    print_usage_error_and_exit(program, "contract --case requires a value");
                };
                let value = value.to_string_lossy().into_owned();
                if value.is_empty() {
                    print_usage_error_and_exit(program, "contract --case requires a value");
                }
                case_filters.insert(value);
            }
            Some(value) if value.starts_with("--case=") => {
                let value = value.strip_prefix("--case=").unwrap_or_default();
                if value.is_empty() {
                    print_usage_error_and_exit(program, "contract --case requires a value");
                }
                case_filters.insert(value.to_string());
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
        case_filters,
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

fn validate_contract_manifest(path: &Path, manifest: &ContractManifest) {
    let mut names = BTreeSet::new();
    for case in &manifest.case {
        if !names.insert(case.name.as_str()) {
            contract_manifest_fail(
                path,
                &format!("duplicate contract case name `{}`", case.name),
            );
        }
        validate_contract_case_tags(path, case);
        validate_contract_case_backend(path, case);
        validate_contract_case_host(path, case);
        validate_contract_case_kind_tags(path, case);
        validate_contract_case_shape_tags(path, case);
        validate_contract_case_expectation_shape(path, case);
    }
}

fn validate_contract_case_tags(path: &Path, case: &ContractCase) {
    if case.contracts.is_empty() {
        contract_manifest_fail(
            path,
            &format!("contract case `{}` should list contract tags", case.name),
        );
    }
    for tag in &case.contracts {
        if !is_canonical_contract_tag(tag) {
            contract_manifest_fail(
                path,
                &format!(
                    "contract case `{}` has non-canonical contract tag `{tag}`",
                    case.name
                ),
            );
        }
        if !is_known_contract_tag(tag) {
            contract_manifest_fail(
                path,
                &format!(
                    "contract case `{}` has unknown contract tag `{tag}`",
                    case.name
                ),
            );
        }
    }
}

fn validate_contract_case_backend(path: &Path, case: &ContractCase) {
    let backend = case.backend.as_deref().unwrap_or("evidence-vm");
    match backend {
        "evidence-vm" | "control-vm" | "interpreter" => {}
        other => contract_manifest_fail(
            path,
            &format!(
                "contract case `{}` has unsupported backend mode `{other}`",
                case.name
            ),
        ),
    }
    if backend != "evidence-vm" && case.kind != "run" {
        contract_manifest_fail(
            path,
            &format!(
                "contract case `{}` should only set backend mode on run cases",
                case.name
            ),
        );
    }
    if case.host.as_deref().unwrap_or("native") != "native" && backend != "evidence-vm" {
        contract_manifest_fail(
            path,
            &format!(
                "contract case `{}` should only combine non-native host mode with backend = \"evidence-vm\"",
                case.name
            ),
        );
    }
    for (tag, expected) in [
        ("backend.evidence-vm", "evidence-vm"),
        ("backend.control-vm", "control-vm"),
        ("backend.interpreter", "interpreter"),
    ] {
        if contract_case_has_tag(case, tag) && backend != expected {
            contract_manifest_fail(
                path,
                &format!(
                    "contract case `{}` uses {tag} but sets backend = {:?}",
                    case.name, case.backend
                ),
            );
        }
    }
    if backend == "control-vm" && !contract_case_has_tag(case, "backend.control-vm") {
        contract_manifest_fail(
            path,
            &format!(
                "control-vm contract case `{}` should carry backend.control-vm",
                case.name
            ),
        );
    }
    if backend == "interpreter" && !contract_case_has_tag(case, "backend.interpreter") {
        contract_manifest_fail(
            path,
            &format!(
                "interpreter contract case `{}` should carry backend.interpreter",
                case.name
            ),
        );
    }
}

fn validate_contract_case_host(path: &Path, case: &ContractCase) {
    let host = case.host.as_deref().unwrap_or("native");
    match host {
        "native" | "unsupported" => {}
        other => contract_manifest_fail(
            path,
            &format!(
                "contract case `{}` has unsupported host mode `{other}`",
                case.name
            ),
        ),
    }
    if host != "native" && case.kind != "run" {
        contract_manifest_fail(
            path,
            &format!(
                "contract case `{}` should only set host mode on run cases",
                case.name
            ),
        );
    }
    if host == "unsupported" && !contract_case_has_tag(case, "host.unsupported") {
        contract_manifest_fail(
            path,
            &format!(
                "unsupported-host contract case `{}` should carry host.unsupported",
                case.name
            ),
        );
    }
    if contract_case_has_tag(case, "host.unsupported") && host != "unsupported" {
        contract_manifest_fail(
            path,
            &format!(
                "host.unsupported contract case `{}` should set host = \"unsupported\"",
                case.name
            ),
        );
    }
}

fn validate_contract_case_kind_tags(path: &Path, case: &ContractCase) {
    match case.kind.as_str() {
        "run" => {
            if !contract_case_has_any_tag(case, &["runtime", "runtime-error", "public-example"]) {
                contract_manifest_fail(
                    path,
                    &format!(
                        "run contract case `{}` should carry runtime, runtime-error, or public-example",
                        case.name
                    ),
                );
            }
        }
        "check" => {
            if !contract_case_has_tag(case, "diagnostics") {
                contract_manifest_fail(
                    path,
                    &format!(
                        "check contract case `{}` should carry diagnostics",
                        case.name
                    ),
                );
            }
        }
        "public-signature" => {
            if !contract_case_has_tag(case, "public-signature") {
                contract_manifest_fail(
                    path,
                    &format!(
                        "public-signature contract case `{}` should carry public-signature",
                        case.name
                    ),
                );
            }
        }
        other => contract_manifest_fail(
            path,
            &format!(
                "contract case `{}` has unsupported kind `{other}`",
                case.name
            ),
        ),
    }
}

fn validate_contract_case_shape_tags(path: &Path, case: &ContractCase) {
    if contract_case_has_tag(case, "runtime-error") {
        let runtime_failure = contract_case_has_tag(case, "runtime-failure");
        let compile_error = contract_case_has_tag(case, "compile-error");
        if case.expect_success != Some(false) {
            contract_manifest_fail(
                path,
                &format!(
                    "runtime-error contract case `{}` should set expect_success = false",
                    case.name
                ),
            );
        }
        if runtime_failure == compile_error {
            contract_manifest_fail(
                path,
                &format!(
                    "runtime-error contract case `{}` should carry exactly one of runtime-failure or compile-error",
                    case.name
                ),
            );
        }
    } else if contract_case_has_any_tag(case, &["runtime-failure", "compile-error"]) {
        contract_manifest_fail(
            path,
            &format!(
                "contract case `{}` should only use runtime-failure or compile-error with runtime-error",
                case.name
            ),
        );
    }

    if contract_case_has_tag(case, "stable-core")
        && contract_case_has_any_tag(case, &["preview", "migration-canary", "compile-error"])
    {
        contract_manifest_fail(
            path,
            &format!(
                "stable-core contract case `{}` should not carry preview, migration-canary, or compile-error",
                case.name
            ),
        );
    }

    if contract_case_has_tag(case, "standard-api") {
        let stable_api = contract_case_has_tag(case, "stable-api");
        let migration_canary = contract_case_has_tag(case, "migration-canary");
        if stable_api == migration_canary {
            contract_manifest_fail(
                path,
                &format!(
                    "standard-api contract case `{}` should carry exactly one of stable-api or migration-canary",
                    case.name
                ),
            );
        }
        if !contract_case_has_any_tag(case, &["result", "errors", "path", "file"]) {
            contract_manifest_fail(
                path,
                &format!(
                    "standard-api contract case `{}` should carry a narrower API area tag",
                    case.name
                ),
            );
        }
    } else if contract_case_has_any_tag(case, &["stable-api", "migration-canary"]) {
        contract_manifest_fail(
            path,
            &format!(
                "contract case `{}` should only use stable-api or migration-canary with standard-api",
                case.name
            ),
        );
    }

    if contract_case_has_tag(case, "file-resource") {
        if contract_case_has_tag(case, "stable-core") {
            contract_manifest_fail(
                path,
                &format!(
                    "file-resource contract case `{}` should not carry stable-core",
                    case.name
                ),
            );
        }
        if !contract_case_has_tag(case, "standard-api") || !contract_case_has_tag(case, "file") {
            contract_manifest_fail(
                path,
                &format!(
                    "file-resource contract case `{}` should carry standard-api and file",
                    case.name
                ),
            );
        }
        if case.kind == "run" {
            let has_mock_host = contract_case_has_tag(case, "mock-host");
            let has_native_host = contract_case_has_tag(case, "host.native");
            let has_unsupported_host = contract_case_has_tag(case, "host.unsupported");
            if has_mock_host {
                if has_native_host {
                    contract_manifest_fail(
                        path,
                        &format!(
                            "file-resource mock-host runtime case `{}` should not also carry host.native",
                            case.name
                        ),
                    );
                }
                if !has_unsupported_host {
                    contract_manifest_fail(
                        path,
                        &format!(
                            "file-resource mock-host runtime case `{}` should also run with host.unsupported",
                            case.name
                        ),
                    );
                }
            } else if [has_native_host, has_unsupported_host]
                .into_iter()
                .filter(|present| *present)
                .count()
                != 1
            {
                contract_manifest_fail(
                    path,
                    &format!(
                        "file-resource runtime case `{}` should carry exactly one native or unsupported host scope",
                        case.name
                    ),
                );
            }
            if !has_unsupported_host
                && !contract_case_has_any_tag(case, &["resource-lifetime", "metadata", "host-act"])
            {
                contract_manifest_fail(
                    path,
                    &format!(
                        "file-resource runtime case `{}` should carry resource-lifetime, metadata, or host-act",
                        case.name
                    ),
                );
            }
            if has_mock_host && !contract_case_has_any_tag(case, &["host-act", "resource-lifetime"])
            {
                contract_manifest_fail(
                    path,
                    &format!(
                        "file-resource mock-host runtime case `{}` should carry host-act or resource-lifetime",
                        case.name
                    ),
                );
            }
        }
    }

    if contract_case_has_tag(case, "file")
        && !contract_case_has_any_tag(case, &["host.native", "host.unsupported", "mock-host"])
    {
        contract_manifest_fail(
            path,
            &format!(
                "file contract case `{}` should carry host.native, host.unsupported, or mock-host",
                case.name
            ),
        );
    }
}

fn validate_contract_case_expectation_shape(path: &Path, case: &ContractCase) {
    if case.kind == "public-signature" && case.expect_type.is_none() {
        contract_manifest_fail(
            path,
            &format!(
                "public-signature contract case `{}` should set expect_type",
                case.name
            ),
        );
    }
    if case.kind == "check" {
        if case.expect_diagnostic_count.is_none()
            || case.expect_diagnostic_code.is_none()
            || case.expect_diagnostic_severity.is_none()
            || case.expect_diagnostic_start.is_none()
            || case.expect_diagnostic_end.is_none()
            || case.expect_diagnostic_related_count.is_none()
        {
            contract_manifest_fail(
                path,
                &format!(
                    "check contract case `{}` should assert diagnostic count, code, severity, primary range, and related count",
                    case.name
                ),
            );
        }
    } else if case.expect_diagnostic_start.is_some() || case.expect_diagnostic_end.is_some() {
        contract_manifest_fail(
            path,
            &format!(
                "non-check contract case `{}` should not assert source diagnostic primary ranges",
                case.name
            ),
        );
    }
    if !case.temp_files.is_empty() && case.kind != "run" {
        contract_manifest_fail(
            path,
            &format!(
                "contract case `{}` should only use temp_files with run cases",
                case.name
            ),
        );
    }
    for temp_file in &case.temp_files {
        if temp_file.missing && temp_file.directory {
            contract_manifest_fail(
                path,
                &format!(
                    "temp file placeholder `{}` in contract case `{}` should not be both missing and directory",
                    temp_file.placeholder, case.name
                ),
            );
        }
        if temp_file.missing {
            if temp_file.contents.is_some() || temp_file.expect_contents.is_some() {
                contract_manifest_fail(
                    path,
                    &format!(
                        "missing temp file placeholder `{}` in contract case `{}` should not set contents or expect_contents",
                        temp_file.placeholder, case.name
                    ),
                );
            }
        } else if temp_file.directory {
            if temp_file.contents.is_some() || temp_file.expect_contents.is_some() {
                contract_manifest_fail(
                    path,
                    &format!(
                        "directory temp placeholder `{}` in contract case `{}` should not set contents or expect_contents",
                        temp_file.placeholder, case.name
                    ),
                );
            }
        } else if temp_file.contents.is_none() {
            contract_manifest_fail(
                path,
                &format!(
                    "temp file placeholder `{}` in contract case `{}` should set contents, missing = true, or directory = true",
                    temp_file.placeholder, case.name
                ),
            );
        }
    }
}

fn contract_case_has_any_tag(case: &ContractCase, tags: &[&str]) -> bool {
    tags.iter().any(|tag| contract_case_has_tag(case, tag))
}

fn contract_case_has_tag(case: &ContractCase, tag: &str) -> bool {
    case.contracts.iter().any(|contract| contract == tag)
}

fn is_canonical_contract_tag(tag: &str) -> bool {
    !tag.is_empty()
        && tag.bytes().all(|byte| {
            byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'.' || byte == b'-'
        })
}

fn is_known_contract_tag(tag: &str) -> bool {
    matches!(
        tag,
        "attached-impl"
            | "backend.control-vm"
            | "backend.evidence-vm"
            | "backend.interpreter"
            | "bindings"
            | "bundled-std"
            | "callback-residual"
            | "calls"
            | "casts"
            | "compile-error"
            | "console"
            | "data-position-effect"
            | "deep-handler"
            | "defaults"
            | "diagnostics"
            | "display"
            | "effect-hygiene"
            | "effects"
            | "errors"
            | "file"
            | "file-resource"
            | "filesystem"
            | "from"
            | "handler-syntax"
            | "host-act"
            | "host.native"
            | "host.unsupported"
            | "junction"
            | "lists"
            | "metadata"
            | "migration-canary"
            | "mock-host"
            | "names"
            | "parser-dsl"
            | "path"
            | "patterns"
            | "preview"
            | "public-example"
            | "public-signature"
            | "raw-compat"
            | "records"
            | "refs"
            | "related-ranges"
            | "release-artifact"
            | "result"
            | "resource-lifetime"
            | "roles"
            | "runtime"
            | "runtime-error"
            | "runtime-failure"
            | "showcase"
            | "stable-core"
            | "stable-api"
            | "standard-api"
            | "std.flow"
            | "std.nondet"
            | "std.parse"
            | "std.ref"
            | "sub-return"
            | "syntax"
            | "typechecker"
            | "typed-failure"
            | "types"
            | "up"
            | "update"
    )
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
    let source_entry = contract_case_entry(repo_root, case);
    let materialized = materialize_contract_run_case(case, &source_entry, &root);
    let mut command = contract_child_command(options, case);
    command.env("YULANG_CACHE_DIR", &cache_root).arg("run");
    push_contract_backend_args(&mut command, case);
    push_contract_host_args(&mut command, case);
    if case.print_roots.unwrap_or(true) {
        command.arg("--print-roots");
    }
    let output = contract_output(case, command.arg(&materialized.entry));
    assert_contract_status(case, &output);
    assert_contract_output(case, &output);
    assert_contract_temp_files(case, &materialized.temp_files);
    let _ = fs::remove_dir_all(&root);
}

fn materialize_contract_run_case(
    case: &ContractCase,
    source_entry: &Path,
    root: &Path,
) -> MaterializedContractRunCase {
    if case.temp_files.is_empty() {
        return MaterializedContractRunCase {
            entry: source_entry.to_path_buf(),
            temp_files: Vec::new(),
        };
    }

    let mut source = fs::read_to_string(source_entry).unwrap_or_else(|error| {
        contract_fail(
            case,
            &format!(
                "failed to read contract case source {}: {error}",
                source_entry.display()
            ),
        )
    });
    let mut temp_files = Vec::new();
    for (index, temp_file) in case.temp_files.iter().enumerate() {
        if !source.contains(&temp_file.placeholder) {
            contract_fail(
                case,
                &format!(
                    "temp file placeholder {:?} is not present in {}",
                    temp_file.placeholder,
                    source_entry.display()
                ),
            );
        }
        let path = root.join(if temp_file.directory {
            format!("temp-{index}.dir")
        } else {
            format!("temp-{index}.txt")
        });
        if temp_file.directory {
            fs::create_dir_all(&path).unwrap_or_else(|error| {
                contract_fail(
                    case,
                    &format!(
                        "failed to create temp directory {}: {error}",
                        path.display()
                    ),
                )
            });
        } else if let Some(contents) = &temp_file.contents {
            fs::write(&path, contents).unwrap_or_else(|error| {
                contract_fail(
                    case,
                    &format!("failed to write temp file {}: {error}", path.display()),
                )
            });
        }
        source = source.replace(
            &temp_file.placeholder,
            &contract_yulang_string_literal(&path),
        );
        temp_files.push(MaterializedContractTempFile {
            path,
            expect_contents: temp_file.expect_contents.clone(),
        });
    }

    let entry = root.join("main.yu");
    fs::write(&entry, source).unwrap_or_else(|error| {
        contract_fail(
            case,
            &format!(
                "failed to materialize contract source {}: {error}",
                entry.display()
            ),
        )
    });
    MaterializedContractRunCase { entry, temp_files }
}

fn assert_contract_temp_files(case: &ContractCase, temp_files: &[MaterializedContractTempFile]) {
    for temp_file in temp_files {
        if let Some(expected) = &temp_file.expect_contents {
            let actual = fs::read_to_string(&temp_file.path).unwrap_or_else(|error| {
                contract_fail(
                    case,
                    &format!(
                        "failed to read temp file {}: {error}",
                        temp_file.path.display()
                    ),
                )
            });
            assert_contract_eq(
                case,
                &format!("temp file {}", temp_file.path.display()),
                &actual,
                expected,
            );
        }
    }
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

fn push_contract_backend_args(command: &mut Command, case: &ContractCase) {
    match case.backend.as_deref().unwrap_or("evidence-vm") {
        "evidence-vm" => {}
        "control-vm" => {
            command.arg("--control-vm");
        }
        "interpreter" => {
            command.arg("--interpreter");
        }
        other => contract_fail(case, &format!("unsupported backend mode `{other}`")),
    }
}

fn push_contract_host_args(command: &mut Command, case: &ContractCase) {
    match case.host.as_deref().unwrap_or("native") {
        "native" => {}
        "unsupported" => {
            command.arg("--host").arg("unsupported");
        }
        other => contract_fail(case, &format!("unsupported host mode `{other}`")),
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

fn contract_yulang_string_literal(path: &Path) -> String {
    format!("{:?}", path.display().to_string())
}

fn contract_fail(case: &ContractCase, message: &str) -> ! {
    eprintln!("contract case {} failed: {message}", case.name);
    process::exit(1);
}

fn contract_manifest_fail(path: &Path, message: &str) -> ! {
    eprintln!("contract manifest {} failed: {message}", path.display());
    process::exit(1);
}
