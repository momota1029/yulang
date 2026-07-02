use std::collections::BTreeSet;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use serde::Deserialize;

#[test]
fn compatible_run_accepts_explicit_std_root() {
    let (entry, std_root) = write_fixture("run-explicit-std-root", "1\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
}

#[test]
fn compatible_run_suppresses_roots_without_print_roots() {
    let (entry, std_root) = write_fixture("run-suppress-roots", "1\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("run")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "");
}

#[test]
fn compatible_run_prints_console_stdout_without_roots() {
    let entry = write_entry("run-console-stdout", "say \"Hello, World\"\nsay: 1 + 2\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("run")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "Hello, World\n3\n");
}

#[test]
fn compatible_run_std_file_read_write_text_host_contract() {
    let root = temp_root("run-std-file-read-write-text");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let input = root.join("input.txt");
    let output_path = root.join("output.txt");
    let entry = root.join("main.yu");
    fs::write(&input, "hello").unwrap();
    fs::write(
        &entry,
        format!(
            "\
my input = {input}
my output = {output}
my before = std::io::file::read_text input
my wrote = std::io::file::write_text output (before + \" world\")
my after = std::io::file::read_text output
(before, after, std::io::file::exists output, std::io::file::is_file output, std::io::file::is_dir output)
",
            input = yulang_string_literal(&input),
            output = yulang_string_literal(&output_path),
        ),
    )
    .unwrap();

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(
        stdout(&output),
        "run roots [(\"hello\", \"hello world\", true, true, false)]\n"
    );
    assert_eq!(fs::read_to_string(&output_path).unwrap(), "hello world");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_std_file_missing_error_displays_path() {
    let root = temp_root("run-std-file-missing-error-display");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let missing = root.join("missing.txt");
    let entry = root.join("main.yu");
    fs::write(
        &entry,
        format!(
            "\
my result = std::io::file::io_err::wrap:
    std::io::file::read_text {missing}
case result:
    ok text -> text
    err e -> e.show
",
            missing = yulang_string_literal(&missing),
        ),
    )
    .unwrap();

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(
        stdout(&output),
        format!("run roots [\"not_found: {}\"]\n", missing.display())
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_std_file_meta_reports_file_dir_and_missing_kind() {
    let root = temp_root("run-std-file-meta-kind");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let file = root.join("input.txt");
    let dir = root.join("dir");
    let missing = root.join("missing.txt");
    let entry = root.join("main.yu");
    fs::write(&file, "hello").unwrap();
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        &entry,
        format!(
            "\
my file_meta = std::io::file::meta {file}
my dir_meta = std::io::file::meta {dir}
my missing_meta = std::io::file::meta {missing}
(file_meta.kind, dir_meta.kind, missing_meta.kind)
",
            file = yulang_string_literal(&file),
            dir = yulang_string_literal(&dir),
            missing = yulang_string_literal(&missing),
        ),
    )
    .unwrap();

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(
        stdout(&output),
        "run roots [(file_kind::file, file_kind::dir, file_kind::missing)]\n"
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_std_file_open_text_ref_host_contract() {
    let root = temp_root("run-std-file-open-text-ref");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let direct = root.join("direct.txt");
    let scoped = root.join("scoped.txt");
    let entry = root.join("main.yu");
    fs::write(&direct, "hello").unwrap();
    fs::write(&scoped, "hi").unwrap();
    fs::write(
        &entry,
        format!(
            "\
my direct_result = {{
    my &txt = std::io::file::open_text {direct}
    my before = $txt
    &txt = before + \" direct\"
    my after = std::io::file::read_text {direct}
    (before, after)
}}

my scoped_result = std::io::file::open_in {scoped}: \\&txt ->
    my before = $txt
    &txt = before + \" scoped\"
    my buffer = $txt
    my backing_during_scope = std::io::file::read_text {scoped}
    (before, buffer, backing_during_scope)

my scoped_after = std::io::file::read_text {scoped}

(direct_result, scoped_result, scoped_after)
",
            direct = yulang_string_literal(&direct),
            scoped = yulang_string_literal(&scoped),
        ),
    )
    .unwrap();

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(
        stdout(&output),
        "run roots [((\"hello\", \"hello direct\"), (\"hi\", \"hi scoped\", \"hi\"), \"hi scoped\")]\n"
    );
    assert_eq!(fs::read_to_string(&direct).unwrap(), "hello direct");
    assert_eq!(fs::read_to_string(&scoped).unwrap(), "hi scoped");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_std_file_text_shorthand_host_contract() {
    let root = temp_root("run-std-file-text-shorthand");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let direct = root.join("direct.txt");
    let scoped = root.join("scoped.txt");
    let entry = root.join("main.yu");
    fs::write(&direct, "hello").unwrap();
    fs::write(&scoped, "hi").unwrap();
    fs::write(
        &entry,
        format!(
            "\
my direct_result = {{
    my &txt = std::io::file::text {direct}
    my before = $txt
    &txt = before + \" text\"
    my after = std::io::file::read_text {direct}
    (before, after)
}}

my scoped_result = std::io::file::text_with {scoped}: \\&txt ->
    my before = $txt
    &txt = before + \" scoped\"
    my buffer = $txt
    my backing_during_scope = std::io::file::read_text {scoped}
    (before, buffer, backing_during_scope)

my scoped_after = std::io::file::read_text {scoped}

(direct_result, scoped_result, scoped_after)
",
            direct = yulang_string_literal(&direct),
            scoped = yulang_string_literal(&scoped),
        ),
    )
    .unwrap();

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(
        stdout(&output),
        "run roots [((\"hello\", \"hello text\"), (\"hi\", \"hi scoped\", \"hi\"), \"hi scoped\")]\n"
    );
    assert_eq!(fs::read_to_string(&direct).unwrap(), "hello text");
    assert_eq!(fs::read_to_string(&scoped).unwrap(), "hi scoped");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_accepts_eval_source() {
    let output = yulang_command()
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg("-e")
        .arg("1")
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
}

#[test]
fn compatible_run_reads_piped_stdin_without_path() {
    let output = yulang_command_with_stdin(["--no-prelude", "run", "--print-roots"], "1\n");

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
}

#[test]
fn compatible_run_reads_explicit_stdin_path() {
    let output = yulang_command_with_stdin(["--no-prelude", "run", "--print-roots", "-"], "1\n");

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
}

#[test]
fn compatible_run_print_roots_keeps_console_stdout_before_roots() {
    let entry = write_entry("run-console-stdout-roots", "say \"Hello\"\n1 + 2\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "Hello\nrun roots [(), 3]\n");
}

#[test]
fn compatible_run_reports_unhandled_effect_hint() {
    let entry = write_entry(
        "run-unhandled-nondet-effect",
        "use std::control::nondet::*\n\neach [1, 2]\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains(
            "runtime error [yulang.unhandled-effect]: unhandled effect request std::control::nondet::nondet::branch\n"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains(
            "hint: handle this computation with a matching effect handler before running it"
        ),
        "{stderr}"
    );
}

#[test]
fn compatible_run_reports_not_callable_hint() {
    let entry = write_entry("run-not-callable", "my x = 1 2\nx\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains(
            "runtime error [yulang.not-callable]: tried to call a non-function value 1\n"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains(
            "hint: check the expression before the argument; calls are written as `f x` or `f(...)`"
        ),
        "{stderr}"
    );
}

#[test]
fn compatible_run_interpreter_reports_unsupported_runtime_feature_hint() {
    let entry = write_entry("run-interpreter-not-callable", "my x = 1 2\nx\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("run")
        .arg("--interpreter")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains("runtime error [yulang.unsupported-runtime-feature]:"),
        "{stderr}"
    );
    assert!(
        stderr
            .contains("hint: try the control VM oracle or reduce this source to a smaller report"),
        "{stderr}"
    );
    assert!(!stderr.contains("value is not a function"), "{stderr}");
}

#[test]
fn compatible_run_control_vm_reports_unsupported_runtime_feature_hint() {
    let entry = write_entry("run-control-not-callable", "my x = 1 2\nx\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("run")
        .arg("--control-vm")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains("runtime error [yulang.unsupported-runtime-feature]:"),
        "{stderr}"
    );
    assert!(
        stderr
            .contains("hint: try the control VM oracle or reduce this source to a smaller report"),
        "{stderr}"
    );
    assert!(!stderr.contains("value is not a function"), "{stderr}");
}

#[test]
fn compatible_run_control_artifact_reports_unsupported_runtime_feature_hint() {
    let entry = write_entry("run-control-artifact-not-callable", "my x = 1 2\nx\n");
    let artifact = entry.with_extension("yuir");

    let build_output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("build")
        .arg("--out")
        .arg(&artifact)
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&build_output);

    let output = yulang_command()
        .arg("run")
        .arg("--print-roots")
        .arg(&artifact)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains("runtime error [yulang.unsupported-runtime-feature]:"),
        "{stderr}"
    );
    assert!(
        stderr
            .contains("hint: try the control VM oracle or reduce this source to a smaller report"),
        "{stderr}"
    );
    assert!(!stderr.contains("value is not a function"), "{stderr}");
}

#[test]
fn compatible_run_reports_not_record_hint() {
    let entry = write_entry("run-not-record", "1.a\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains(
            "runtime error [yulang.not-record]: tried to read fields from non-record value 1\n"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains("hint: use `.field` only on record values"),
        "{stderr}"
    );
}

#[test]
fn compatible_run_reports_pattern_mismatch_hint() {
    let entry = write_entry("run-pattern-mismatch", "case 1:\n  2 -> 3\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains("runtime error [yulang.pattern-mismatch]: no pattern matched the value\n"),
        "{stderr}"
    );
    assert!(
        stderr.contains("hint: add a fallback pattern such as `_ -> ...`"),
        "{stderr}"
    );
}

#[test]
fn compatible_run_reports_unsatisfied_subtype_hint() {
    let entry = write_entry("run-unsatisfied-subtype", "{ a: 1 }.b\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr
            .contains("compile error [yulang.unsatisfied-subtype]: record is missing field `b`\n"),
        "{stderr}"
    );
    assert!(
        stderr.contains("detail: unsatisfied subtype constraint: {a: int} <: {b: 'open"),
        "{stderr}"
    );
    assert!(
        stderr.contains("hint: add `b` to this record or use a value that provides it; actual record has fields a"),
        "{stderr}"
    );
}

#[test]
fn compatible_run_reports_unresolved_method_hint() {
    let entry = write_entry("run-unresolved-method", "(\\x -> x).show\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains(
            "compile error [yulang.unresolved-method]: no role implementation satisfies this method call\n"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains("detail: unresolved typeclass method"),
        "{stderr}"
    );
    assert!(
        stderr.contains(
            "hint: add or import an impl for the receiver type, or call a method supported by that value"
        ),
        "{stderr}"
    );
}

#[test]
fn compatible_run_reports_ambiguous_method_hint() {
    let entry = write_entry(
        "run-ambiguous-method",
        "role R 'a:\n    our a.foo: int\n\nimpl int: R:\n    our x.foo = 1\n\nimpl int: R:\n    our x.foo = 2\n\n1.foo\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains(
            "compile error [yulang.ambiguous-method]: more than one role implementation satisfies this method call\n"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains("detail: ambiguous typeclass method"),
        "{stderr}"
    );
    assert!(
        stderr.contains(
            "hint: make the receiver type more specific or keep only one matching impl in scope"
        ),
        "{stderr}"
    );
}

#[test]
fn compatible_check_accepts_explicit_std_root() {
    let (entry, std_root) = write_fixture("check-explicit-std-root", "1\n");

    let output = yulang_command()
        .arg("check")
        .arg("--std-root")
        .arg(&std_root)
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("check-poly-std\n"), "{stdout}");
    assert!(stdout.contains("files: 3\n"), "{stdout}");
    assert!(stdout.contains("lowering errors: 0\n"), "{stdout}");
}

#[test]
fn compatible_check_no_prelude_uses_local_source_only() {
    let entry = write_entry("check-no-prelude", "1\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("check-poly\n"), "{stdout}");
    assert!(stdout.contains("files: 1\n"), "{stdout}");
}

#[test]
fn public_diagnostics_check_reports_type_annotation_mismatch() {
    let entry = repo_yulang_fixture("regressions/diagnostics/type_annotation_mismatch.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.type-mismatch]: x: type mismatch: bool is not int\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains("    --> line 1, column 4\n    1 | my x: int = true\n      |    ^\n"),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "    note: expected type comes from this type annotation: int\n    --> line 1, column 7\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "    note: actual type comes from this expression: bool\n    --> line 1, column 13\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains("  x: type mismatch: bool is not int\n"),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_source_frame_uses_user_source_with_std_root() {
    let entry = write_entry("diagnostics-source-frame-std-root", "my x: int = true\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("    --> line 1, column 4\n    1 | my x: int = true\n      |    ^\n"),
        "{stdout}"
    );
    assert!(!stdout.contains("line 3, column 4"), "{stdout}");
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_unresolved_value_name() {
    let entry = repo_yulang_fixture("regressions/diagnostics/unresolved_value_name.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.unresolved-value]: result: unresolved value name: missing\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "    hint: define `missing` before this use, or import the module that provides it\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains("  result: unresolved value name: missing\n"),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_unresolved_type_name() {
    let entry = repo_yulang_fixture("regressions/diagnostics/unresolved_type_name.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.unresolved-type]: x: unresolved type name: missing_type\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "    hint: define type `missing_type` before this annotation, or import it\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains("  x: unresolved type name: missing_type\n"),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_unsupported_type_syntax() {
    let entry =
        repo_yulang_fixture("regressions/diagnostics/unsupported_record_type_annotation.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.unsupported-type-syntax]: x: unsupported type annotation syntax: TypeRecord\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains("  x: unsupported type annotation syntax: TypeRecord\n"),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_top_level_mutable_binding() {
    let entry = repo_yulang_fixture("regressions/diagnostics/top_level_mutable_binding.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.top-level-mutable-binding]: $x: top-level mutable binding $x is not supported; move it into a block or function body\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains(
            "  $x: top-level mutable binding $x is not supported; move it into a block or function body\n"
        ),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_rule_lazy_quantifier() {
    let entry = repo_yulang_fixture("regressions/diagnostics/rule_lazy_quantifier.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.unsupported-rule-lazy-quantifier]: p: rule lazy quantifier `*?` is not supported; rule uses PEG-style greedy repetition\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains(
            "  p: rule lazy quantifier `*?` is not supported; rule uses PEG-style greedy repetition\n"
        ),
        "{stdout}"
    );
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_recovers_unclosed_paren_without_panic() {
    let entry = repo_yulang_fixture("regressions/diagnostics/unclosed_paren.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.syntax]: syntax error: unexpected end of input\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains("    --> line 1, column 10\n    1 | my x = (1\n      |          ^\n"),
        "{stdout}"
    );
    assert!(stdout.contains("check-poly\n"), "{stdout}");
    assert!(stdout.contains("lowering errors: 0\n"), "{stdout}");
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_trailing_operator_syntax() {
    let entry = repo_yulang_fixture("regressions/diagnostics/trailing_operator.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("diagnostics:\n  error [yulang.syntax]: syntax error: unexpected token\n"),
        "{stdout}"
    );
    assert!(
        stdout.contains("    --> line 1, column 10\n    1 | my x = 1 +\n      |          ^\n"),
        "{stdout}"
    );
    assert!(stdout.contains("check-poly\n"), "{stdout}");
    assert!(stdout.contains("lowering errors: 0\n"), "{stdout}");
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_catch_missing_arm_body() {
    let entry = repo_yulang_fixture("regressions/diagnostics/catch_missing_arm_body.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.missing-catch-arm-body]: catch arm is missing a body expression\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains("    hint: write an expression after `->`\n"),
        "{stdout}"
    );
    assert!(!stdout.contains("MissingCatchArmBody"), "{stdout}");
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_catch_missing_scrutinee() {
    let entry = repo_yulang_fixture("regressions/diagnostics/catch_missing_scrutinee.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.missing-catch-scrutinee]: catch expression is missing the computation to handle\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains("    hint: write `catch <expr>:` before the handler arms\n"),
        "{stdout}"
    );
    assert!(!stdout.contains("MissingCatchScrutinee"), "{stdout}");
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_catch_missing_arm_pattern() {
    let entry = repo_yulang_fixture("regressions/diagnostics/catch_missing_arm_pattern.yu");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("check")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains(
            "diagnostics:\n  error [yulang.missing-catch-arm-pattern]: catch arm is missing a value pattern or effect operation\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains("    hint: write a value pattern or effect operation before `->`\n"),
        "{stdout}"
    );
    assert!(!stdout.contains("MissingCatchArmPattern"), "{stdout}");
    assert_eq!(stderr(&output), "");
}

#[test]
fn compatible_global_cst_and_timing_flags_are_accepted() {
    let entry = write_entry("global-cst", "1\n");

    let output = yulang_command()
        .arg("check")
        .arg("--cst")
        .arg("--infer-phase-timings")
        .arg("--no-cache")
        .arg("--no-prelude")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("Root\n"), "{stdout}");
    assert!(stdout.contains("check-poly\n"), "{stdout}");
}

#[test]
fn compatible_build_writes_control_vm_artifact_and_run_loads_it() {
    let entry = write_entry("build-artifact", "1\n");
    let artifact = entry.with_extension("yuir");

    let build_output = yulang_command()
        .arg("--no-prelude")
        .arg("build")
        .arg("--out")
        .arg(&artifact)
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&build_output);
    assert_eq!(
        stdout(&build_output),
        format!("build: {}\n", artifact.display())
    );
    let artifact_source = fs::read_to_string(&artifact).unwrap();
    assert!(
        artifact_source.starts_with("YULANG-CONTROL-VM 1\n"),
        "{artifact_source}"
    );

    let run_output = yulang_command()
        .arg("run")
        .arg("--print-roots")
        .arg(&artifact)
        .output()
        .unwrap();
    assert_success(&run_output);
    assert_eq!(stdout(&run_output), "run roots [1]\n");

    let debug_output = yulang_command()
        .arg("debug")
        .arg("control-vm-load")
        .arg("--print-roots")
        .arg(&artifact)
        .output()
        .unwrap();
    assert_success(&debug_output);
    assert_eq!(stdout(&debug_output), "run roots [1]\n");
}

#[test]
fn compatible_dump_core_ir_accepts_explicit_std_root() {
    let (entry, std_root) = write_fixture("dump-core-explicit-std-root", "1\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("dump")
        .arg("--core-ir")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("roots d0:std\n"), "{stdout}");
    assert!(stdout.contains("root exprs e0:1\n"), "{stdout}");
}

#[test]
fn compatible_dump_runtime_ir_maps_to_mono_dump() {
    let (entry, std_root) = write_fixture("dump-runtime-explicit-std-root", "1\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("dump")
        .arg("--runtime-ir")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "mono roots [1]\n");
}

#[test]
fn compatible_dump_control_evidence_accepts_explicit_std_root() {
    let (entry, std_root) = write_fixture("dump-control-evidence-explicit-std-root", "1\n");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("dump")
        .arg("--control-evidence")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("control evidence roots ["), "{stdout}");
    assert!(stdout.contains("runtime evidence tasks ["), "{stdout}");
    assert!(stdout.contains("  graph slots "), "{stdout}");
}

#[test]
fn compatible_dump_control_evidence_prints_runtime_source_sites() {
    let (entry, std_root) = write_fixture(
        "dump-control-evidence-runtime-sites",
        "act out:\n  our say: int -> unit\n\n\
         my handle(action: [out] _) = catch action:\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n\n\
         handle(out::say(1))\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("dump")
        .arg("--control-evidence")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("  nodes "), "{stdout}");
    assert!(stdout.contains("  sites "), "{stdout}");
    assert!(
        stdout.contains("operation-call callee"),
        "operation call site should be visible in dump:\n{stdout}"
    );
    assert!(
        stdout.contains("catch body"),
        "catch site should be visible in dump:\n{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_bench_prints_timing_and_size_metrics() {
    let entry = write_entry(
        "debug-runtime-evidence-bench",
        "act out:\n  our say: int -> unit\n\n\
         my handle(action: [out] _) = catch action:\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n\n\
         handle(out::say(1))\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-bench")
        .arg("--repeat")
        .arg("1")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("runtime evidence bench:"), "{stdout}");
    assert!(stdout.contains("iteration 1:"), "{stdout}");
    assert!(stdout.contains("bench.cache: disabled"), "{stdout}");
    assert!(stdout.contains("bench.specialize:"), "{stdout}");
    assert!(stdout.contains("bench.control_lower:"), "{stdout}");
    assert!(stdout.contains("evidence.tasks:"), "{stdout}");
    assert!(stdout.contains("evidence.nodes:"), "{stdout}");
    assert!(stdout.contains("evidence.node_evidence_refs:"), "{stdout}");
    assert!(stdout.contains("evidence.type_stack_weights:"), "{stdout}");
}

#[test]
fn debug_evidence_vm_plan_prints_handler_passing_plan() {
    let entry = write_entry(
        "debug-evidence-vm-plan",
        "act out:\n  our say: int -> unit\n\n\
         catch ((\\_ -> out::say(1)) ()):\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("evidence vm plan:"), "{stdout}");
    assert!(stdout.contains("handlers:"), "{stdout}");
    assert!(stdout.contains("operations:"), "{stdout}");
    assert!(
        stdout.contains("evidence_param_functions:"),
        "evidence parameters should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence_env_values:"),
        "value evidence environments should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence_slot_keys:"),
        "evidence slot keys should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence_object_slots:"),
        "evidence object slot summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("function_objects:") && stdout.contains("value_objects:"),
        "function and value object summaries should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("call_objects:"),
        "call object summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("provider_slots:") && stdout.contains("provider_candidates:"),
        "provider summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("env_provider_slots:") && stdout.contains("env_provider_candidates:"),
        "value environment provider summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("known_handler_objects:") && stdout.contains("compiler_state_certificates"),
        "known handler plan summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("known_operation_calls:") && stdout.contains("known_operation_rejects:"),
        "known operation call classification summary should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence object graph:"),
        "evidence object graph should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("function-objects:"),
        "function evidence objects should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("value-objects:"),
        "value evidence objects should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("env_providers [s") && stdout.contains("=[h"),
        "value evidence provider environments should carry handler object candidates:\n{stdout}"
    );
    assert!(
        stdout.contains("handler-objects:"),
        "handler evidence objects should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("operation-objects:"),
        "operation evidence objects should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("provider-index:") && stdout.contains("needs-evidence-env"),
        "provider candidates should be visible without forcing direct lowering:\n{stdout}"
    );
    assert!(
        stdout.contains("class tail-resumptive"),
        "handler arm classification should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("signature params [") && stdout.contains("signature captures ["),
        "function and value evidence signatures should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("values:") && stdout.contains("lambda body"),
        "lambda evidence captures should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("lexical-handler-candidate")
            || stdout.contains("generic-fallback")
            || stdout.contains("direct-handler"),
        "operation lowering should be explicit:\n{stdout}"
    );
}

#[test]
fn debug_evidence_vm_plan_marks_local_var_known_state_handler() {
    let entry = write_entry(
        "debug-evidence-vm-plan-local-var-known-state",
        concat!("my f =\n", "  my $x = 1\n", "  $x\n", "f\n",),
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("known_handler_objects: 1 state 1 compiler_state_certificates 1"),
        "compiler-generated local var should produce one known state handler:\n{stdout}"
    );
    assert!(
        stdout.contains("known-handlers:")
            && stdout.contains("state d")
            && stdout.contains("source compiler-local-var"),
        "known state handler details should be visible:\n{stdout}"
    );
    assert!(
        stdout.contains("continuation snapshot-fork"),
        "known state handler should carry snapshot/fork continuation semantics:\n{stdout}"
    );
    assert!(
        stdout.contains(
            "known_operation_calls: 3 state_get_candidates 2 state_set_candidates 1 direct_gets 2 direct_sets 1 route_proofs 3"
        ),
        "compiler local var should produce known state get/set call candidates:\n{stdout}"
    );
    assert!(
        stdout.contains("known-operation-calls:")
            && stdout.contains("state-get")
            && stdout.contains("proof p")
            && stdout.contains("direct_ready=true reject -")
            && stdout.contains("state-set")
            && !stdout.contains("reject direct-execution-disabled"),
        "known state operation call route proofs should enable direct get/set:\n{stdout}"
    );
    assert!(
        stdout.contains("known-state-operation-route-proofs:")
            && stdout.contains("source compiler-local-var")
            && stdout.contains("visibility clean-known-state-catch")
            && stdout.contains("payload unit-payload-for-get"),
        "plan-only known state operation route proofs should be printed:\n{stdout}"
    );
}

#[test]
fn debug_evidence_vm_plan_does_not_mark_user_state_like_handler_without_certificate() {
    let entry = write_entry(
        "debug-evidence-vm-plan-user-state-like-not-known",
        concat!(
            "act state 't:\n",
            "  pub get: () -> 't\n",
            "  pub set: 't -> ()\n",
            "my run(v: int, x: [_] int): int = catch x:\n",
            "  state::get(), k -> run v: k v\n",
            "  state::set v, k -> run v: k()\n",
            "my f = run 1: state::get()\n",
            "f\n",
        ),
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("known_handler_objects: 0 state 0 compiler_state_certificates 0"),
        "state-like source handler should not be marked without compiler certificate:\n{stdout}"
    );
    assert!(
        !stdout.contains("known-handlers:"),
        "uncertified user handler should not produce known handler details:\n{stdout}"
    );
    assert!(
        stdout.contains("known_operation_calls: 0 state_get_candidates 0 state_set_candidates 0"),
        "uncertified user handler should not produce known operation candidates:\n{stdout}"
    );
    assert!(
        !stdout.contains("known-operation-calls:"),
        "uncertified user handler should not produce known operation details:\n{stdout}"
    );
}

#[test]
fn debug_evidence_vm_plan_records_handler_definition_env() {
    let entry = write_entry(
        "debug-evidence-vm-handler-definition-env",
        "act out:\n  our say: int -> unit\n\n\
         catch (catch out::say(1):\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n\
         ):\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("handler-objects:"),
        "handler evidence objects should be visible in the plan:\n{stdout}"
    );
    assert!(
        stdout.contains("def_env [h0]"),
        "nested handler objects should record outer definition handler ids:\n{stdout}"
    );
}

#[test]
fn debug_evidence_vm_plan_visits_method_select_handler_body() {
    let entry = write_entry(
        "debug-evidence-vm-plan-method-select-handler",
        "use std::control::nondet::*\n\n\
         {\n\
         \x20 my xs = (each 1..2).list\n\
         \x20 ()\n\
         }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("std::control::nondet::nondet::branch resumptive class may-escape-yield"),
        "method-select handler bodies should classify delayed continuation use as escaping:\n{stdout}"
    );
    assert!(
        stdout.contains("std::control::nondet::nondet::reject resumptive class abortive"),
        "method-select handler bodies should contribute abortive operation evidence:\n{stdout}"
    );
}

#[test]
fn debug_evidence_vm_plan_classifies_direct_multi_shot_resume() {
    let entry = write_entry(
        "debug-evidence-vm-plan-multi-shot-resume",
        "act flip:\n  our coin: () -> bool\n\n\
         catch flip::coin():\n\
         \x20 flip::coin(), k -> {\n\
         \x20\x20 k(true)\n\
         \x20\x20 k(false)\n\
         \x20 }\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-plan")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(
        stdout.contains("flip::coin resumptive class multi-shot-yield"),
        "directly invoking a continuation twice should be classified as multi-shot:\n{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_matches_control_vm_on_pure_lambda_subset() {
    let entry = write_entry("debug-runtime-evidence-run", "my id x = x\nid 3\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("runtime evidence run:"), "{stdout}");
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("evidence.tasks: 2"), "{stdout}");
    assert!(stdout.contains("run roots [3]\n"), "{stdout}");
}

#[test]
fn debug_evidence_vm_run_alias_matches_control_vm_on_pure_lambda_subset() {
    let entry = write_entry("debug-evidence-vm-run", "my id x = x\nid 3\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("runtime evidence run:"), "{stdout}");
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [3]\n"), "{stdout}");
}

#[test]
fn debug_evidence_vm_run_passes_call_evidence_to_returned_effect_thunks() {
    let entry = write_entry(
        "debug-evidence-vm-run-call-evidence",
        "use std::control::nondet::*\n\n(each 1..2).list\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    let route_hits = stdout
        .lines()
        .find_map(|line| {
            line.trim()
                .strip_prefix("runtime_evidence.provider_env_route_hits: ")
                .and_then(|value| value.parse::<usize>().ok())
        })
        .unwrap_or(0);
    assert!(
        route_hits > 0,
        "call evidence should reach effect thunks returned by the callee:\n{stdout}"
    );
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [[1, 2]]\n"), "{stdout}");
}

#[test]
fn debug_evidence_vm_run_captures_provider_env_on_closure_value() {
    let entry = write_entry(
        "debug-evidence-vm-run-provider-env",
        "act out:\n  our say: int -> unit\n\n\
         catch ((\\_ -> out::say(1)) ()):\n\
         \x20 out::say(n), k -> k()\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("evidence.plan_env_provider_slots: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_env_provider_candidates: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.provider_env_values: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.provider_env_reads: 1"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [()]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_matches_control_vm_on_std_int_primitives() {
    let entry = write_entry(
        "debug-runtime-evidence-run-std-int",
        "1 + 2\nmy add1 x = x + 1\nadd1 3\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("evidence.tasks:"), "{stdout}");
    assert!(stdout.contains("run roots [3, 4]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_reads_struct_record_payload_fields() {
    let entry = write_entry(
        "debug-runtime-evidence-run-struct-field",
        "struct point { x: int, y: int } with:\n\
         \x20 our p.norm2 = p.x * p.x + p.y * p.y\n\n\
         point { x: 3, y: 4 } .norm2\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [25]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_matches_control_vm_on_record_pattern_defaults() {
    let entry = write_entry(
        "debug-runtime-evidence-run-record-pattern-defaults",
        "my area({width = 1, height = 2}) = width * height\n\
         area { width: 3 }\n\
         area {}\n\
         area { width: 3, height: 4 }\n\
         my next_area({width = 2, height = width + 1}) = width * height\n\
         next_area { width: 3 }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [6, 2, 12, 12]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_applies_function_adapter_for_each() {
    let entry = write_entry(
        "debug-runtime-evidence-run-each-list",
        "use std::control::nondet::*\n\n(each 1..3).list\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [[1, 2, 3]]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_inlines_pure_for_adapter_thunks() {
    let entry = write_entry(
        "debug-runtime-evidence-run-pure-for-adapter-inline",
        "{\n\
         \x20 for x in 1..3:\n\
         \x20\x20 x + 1\n\
         \x20 ()\n\
         }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [()]\n"), "{stdout}");
    assert!(
        stdout.contains("runtime_evidence.apply_adapter_inline_attempts: 6"),
        "pure for callbacks should try the adapter inline route:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.apply_adapter_inline_hits: 6"),
        "pure for callbacks should finish adapter application without continuation frames:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.apply_adapter_inline_effect_fallbacks: 0"),
        "pure for callbacks should not need the effect fallback in the adapter inline route:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.adapt_value_inline_thunk_wraps: 6"),
        "pure for callback returns should wrap values into thunk values directly:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.catch_body_env_clone_elided: 20"),
        "pure for loop-control catches should reuse env when the body cannot extend it:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.catch_body_env_clone_kept: 0"),
        "pure for loop-control catches should not clone env for preserving bodies:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.continuation_resume_adapter_steps: 0"),
        "pure for callbacks should not resume adapter continuation frames:\n{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_evaluates_list_view_raw() {
    let entry = write_entry(
        "debug-runtime-evidence-run-list-view-raw",
        "use std::data::list::*\n\n[1, 2, 3].rev\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [[3, 2, 1]]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_matches_control_vm_on_text_and_bytes_primitives() {
    let entry = write_entry(
        "debug-runtime-evidence-run-text-bytes",
        "std::text::str::index_raw \"aβc\" 1\n\
         std::text::str::index_range_raw \"aβc\" 1 3\n\
         std::text::str::splice_raw \"abcd\" 1 3 \"XY\"\n\
         std::text::str::line_count \"a\\nb\"\n\
         std::text::str::index_range \"abcdef\" (std::data::range::range 1 4)\n\
         std::data::list::index_range [1, 2, 3, 4] (std::data::range::range 1 3)\n\
         std::data::list::splice_raw [1, 2, 3, 4] 1 3 [9]\n\
         std::text::bytes::len(std::text::str::to_bytes \"abc\")\n\
         std::text::bytes::index_raw(std::text::str::to_bytes \"abc\", 1)\n\
         std::text::bytes::to_utf8_raw(std::text::str::to_bytes \"abc\")\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains(
            "run roots [\"β\", \"βc\", \"aXYd\", 2, \"bcd\", [2, 3], [1, 9, 4], 3, 98, (\"abc\", 3)]\n"
        ),
        "{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_carries_function_adapter_hygiene_markers() {
    let entry = write_entry(
        "debug-runtime-evidence-run-function-adapter-hygiene",
        "pub act sub 'a:\n\
         \x20 pub return: 'a -> never\n\
         \x20 pub sub(x: [_] 'a): 'a = catch x:\n\
         \x20\x20 return a, _ -> a\n\
         \x20\x20 a -> a\n\n\
         pub act note:\n\
         \x20 pub tell: () -> ()\n\n\
         our use_int = sub::sub:\n\
         \x20 sub::return 0\n\n\
         our use_str = sub::sub:\n\
         \x20 sub::return \"done\"\n\n\
         our use_residual() = sub::sub:\n\
         \x20 note::tell()\n\
         \x20 1\n\n\
         (use_int, use_str, use_residual)\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("run roots [(0, \"done\", <closure>)]\n"),
        "{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_resumes_carried_callback_markers() {
    let entry = write_entry(
        "debug-runtime-evidence-run-repeated-callback-hygiene",
        "pub act tick:\n\
         \x20 pub ping: () -> ()\n\n\
         pub strip_tick(action: [tick] _) = catch action:\n\
         \x20 tick::ping(), k -> strip_tick(k ())\n\
         \x20 v -> v\n\n\
         pub count_tick(action: [tick] _) = catch action:\n\
         \x20 tick::ping(), k -> 1 + count_tick(k ())\n\
         \x20 _ -> 0\n\n\
         pub bounce(n: int, f, x) =\n\
         \x20 if n == 0:\n\
         \x20\x20 x\n\
         \x20 else:\n\
         \x20\x20 strip_tick: f (f (bounce(n - 1, f, x)))\n\n\
         count_tick:\n\
         \x20 bounce(3, \\x -> {\n\
         \x20\x20 tick::ping()\n\
         \x20\x20 x + 1\n\
         \x20 }, 0)\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [6]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_handles_for_last_and_nullary_constructors() {
    let entry = write_entry(
        "debug-runtime-evidence-run-for-last",
        "{\n\
         \x20 for x in 0..:\n\
         \x20\x20 if x == 5: last\n\
         \x20 5\n\
         }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [5]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_formats_labeled_nullary_constructor_results() {
    let entry = write_entry(
        "debug-runtime-evidence-run-once",
        "use std::control::nondet::*\n\n\
         once:\n\
         \x20 my a = each 1..\n\
         \x20 my b = each a<..\n\
         \x20 my c = each b<..\n\
         \x20 guard: a * a + b * b == c * c\n\
         \x20 (a, b, c)\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("run roots [opt::just((3, 4, 5))]\n"),
        "{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_handles_ref_set() {
    let entry = write_entry(
        "debug-runtime-evidence-run-ref-set",
        "{\n\
         \x20 my $x = 10\n\
         \x20 my $y = 20\n\
         \x20 &x = $x + 1\n\
         \x20 &y = $y + 1\n\
         \x20 ($x, $y)\n\
         }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [(11, 21)]\n"), "{stdout}");
    assert!(
        stdout.contains("runtime_evidence.known_state_direct_gets: 3"),
        "compiler local refs should use direct state get handling:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_direct_sets: 1"),
        "compiler local refs should use direct state set handling:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_entries: 1"),
        "known state catch should push a runtime state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_exits: 1"),
        "known state catch should pop the runtime state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_reads_late: 0"),
        "request-free known state gets should bypass late request reads:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_writes_late: 0"),
        "request-free known state sets should bypass late request writes:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_missing_late: 0"),
        "known state frame lookup should not miss in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_shadow_compat_fallbacks: 0"),
        "local ref canary should not need env shadow compatibility fallback:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_snapshots: 0"),
        "straight-line local ref handling should not snapshot state frames:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_forks: 0"),
        "straight-line local ref handling should not fork state frames:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_get_candidates: 2"),
        "known operation plan should classify the two static get call sites:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_set_candidates: 1"),
        "known operation plan should classify the static set call site:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_state_operation_route_proofs: 3"),
        "known operation plan should build plan-only route proofs for local refs:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_direct_gets: 2"),
        "D3 should enable direct get for the two static local ref get sites:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_direct_sets: 1"),
        "D4 should enable direct set for the static local ref set site:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_reject_direct_execution_disabled: 0"),
        "D4 should not leave route-proven local refs on the disabled direct path:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_get_candidate_hits: 3"),
        "known operation runtime hits should count forced get requests:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_set_candidate_hits: 1"),
        "known operation runtime hits should count forced set requests:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_get_active_frame_hits: 3"),
        "known get operations should see the active state frame at force time:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_set_active_frame_hits: 1"),
        "known set operations should see the active state frame at force time:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_get_active_frame_misses: 0"),
        "known get operations should not miss the active state frame in this canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_set_active_frame_misses: 0"),
        "known set operations should not miss the active state frame in this canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_hits: 4"),
        "route proof shadow guard should hit for every dynamic local ref operation:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_get_hits: 3"),
        "route proof shadow guard should count dynamic local ref gets:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_set_hits: 1"),
        "route proof shadow guard should count dynamic local ref sets:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_missing_proof: 0"),
        "route proof shadow guard should not miss proofs in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_missing_frame: 0"),
        "route proof shadow guard should see the active state frame in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_role_mismatch: 0"),
        "route proof shadow guard should not see role mismatches in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_attempts: 3"),
        "route proof direct get guard should run for every dynamic local ref get:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_hits: 3"),
        "route proof direct get guard should bypass requests for local ref gets:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_missing_proof: 0"),
        "route proof direct get guard should not miss proofs in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_missing_frame: 0"),
        "route proof direct get guard should see the active state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_role_mismatch: 0"),
        "route proof direct get guard should not see role mismatches:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_payload_mismatch: 0"),
        "route proof direct get guard should only see unit get payloads:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_attempts: 1"),
        "route proof direct set guard should run for every dynamic local ref set:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_hits: 1"),
        "route proof direct set guard should bypass requests for local ref sets:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_missing_proof: 0"),
        "route proof direct set guard should not miss proofs in the local ref canary:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_missing_frame: 0"),
        "route proof direct set guard should see the active state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_role_mismatch: 0"),
        "route proof direct set guard should not see role mismatches:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_payload_mismatch: 0"),
        "route proof direct set guard should see a single-value set payload proof:\n{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_known_state_frame_matches_control_across_nondet_resume() {
    let entry = write_entry(
        "debug-runtime-evidence-run-known-state-frame-nondet",
        "use std::control::nondet::*\n\n\
         {\n\
         \x20 my $x = 0\n\
         \x20 my ys = {\n\
         \x20\x20 my b = each [true, false]\n\
         \x20\x20 &x = $x + 1\n\
         \x20\x20 $x\n\
         \x20 }.list\n\
         \x20 (ys, $x)\n\
         }\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [([1, 2], 2)]\n"), "{stdout}");
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_entries: 1"),
        "known state frame should be active across the nondet body:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_exits: 1"),
        "known state frame should be popped after the enclosing state handler:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_reads_late: 0"),
        "request-free known state reads should bypass late request handling:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_writes_late: 0"),
        "request-free known state writes should update the runtime state frame directly:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_missing_late: 0"),
        "nondet resume should not lose the active state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_snapshots: 0"),
        "state outside nondet/list should stay shared rather than snapshotted:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_forks: 0"),
        "state outside nondet/list should not be forked by nondet resume:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_get_active_frame_hits: 7"),
        "known get operations should see the active state frame across nondet resume:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_set_active_frame_hits: 2"),
        "known set operations should see the active state frame across nondet resume:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_hits: 7"),
        "known get operations should use route-proof direct reads across nondet resume:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_hits: 2"),
        "known set operations should use route-proof direct writes across nondet resume:\n{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_handles_console_stdout_host_effect() {
    let entry = write_entry(
        "debug-runtime-evidence-run-console-stdout",
        "say \"Hello, World\"\n\
         say: 1 + 2\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("Hello, World\n3\nrun roots [(), ()]\n"),
        "{stdout}"
    );
}

#[test]
fn debug_runtime_evidence_run_uses_direct_handler_evidence() {
    let entry = write_entry(
        "debug-runtime-evidence-run-direct-handler",
        "act flip:\n  our coin: () -> bool\n\n\
         catch flip::coin():\n\
         \x20 flip::coin(), k -> k true\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("control_evidence.effect_calls: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("control_evidence.direct_effect_calls: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_provider_slots: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_provider_candidates: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_direct_candidates: 2"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_effect_routes: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_direct_effect_routes: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.static_route_sites_total: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.static_route_static_handler: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.static_route_static_tail_resumptive: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.static_route_dynamic_unclassified: 0"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.static_route_runtime_hits_static_tail: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.static_route_runtime_hits_dynamic_unclassified: 0"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [true]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_classifies_unused_continuation_as_direct_abortive() {
    let entry = write_entry(
        "debug-runtime-evidence-run-direct-abortive-handler",
        "act stop:\n  our now: () -> int\n\n\
         catch (stop::now(), 1):\n\
         \x20 stop::now(), _ -> (42, 0)\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("evidence.plan_direct_effect_routes: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_direct_abortive_effect_routes: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_direct_tail_resumptive_effect_routes: 0"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.static_route_sites_total: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.static_route_static_handler: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.static_route_static_abortive: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.static_route_runtime_hits_static_other: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.thunk_force_continuation: 0"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.continuation_appends: 0"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.request_continuation_steps: 0"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [(42, 0)]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_falls_through_handler_arm_patterns_and_guards() {
    let entry = write_entry(
        "debug-runtime-evidence-run-handler-arm-fallthrough",
        "act log:\n  our put: int -> int\n\n\
         catch log::put 1:\n\
         \x20 log::put 0, k -> k 10\n\
         \x20 log::put _, k if false -> k 20\n\
         \x20 log::put _, k -> k 30\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [30]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_falls_through_value_arm_patterns_and_guards() {
    let entry = write_entry(
        "debug-runtime-evidence-run-value-arm-fallthrough",
        "catch 1:\n\
         \x20 0 -> 10\n\
         \x20 _ if false -> 20\n\
         \x20 _ -> 30\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [30]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_falls_through_case_patterns_and_guards() {
    let entry = write_entry(
        "debug-runtime-evidence-run-case-fallthrough",
        "case 1:\n\
         \x20 0 -> 10\n\
         \x20 _ if false -> 20\n\
         \x20 _ -> 30\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [30]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_handles_annotated_handler_function_with_state() {
    let entry = write_entry(
        "debug-runtime-evidence-run-handler-function-state",
        "act log:\n\
         \x20 pub put: str -> ()\n\n\
         my collect_count(comp: [log] 'a): int =\n\
         \x20 my $count = 0\n\
         \x20 catch comp:\n\
         \x20\x20 log::put _, k ->\n\
         \x20\x20\x20 &count = $count + 1\n\
         \x20\x20\x20 k ()\n\
         \x20\x20 v -> v\n\
         \x20 $count\n\n\
         collect_count: log::put \"a\"\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [1]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_resumes_direct_effect_in_apply_argument() {
    let entry = write_entry(
        "debug-runtime-evidence-run-apply-argument-effect",
        "act flip:\n  our coin: () -> bool\n\n\
         my id x = x\n\n\
         catch id flip::coin():\n\
         \x20 flip::coin(), k -> k true\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("control_evidence.direct_effect_calls: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_direct_tail_resumptive_effect_routes: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.request_continuation_steps: 0"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [true]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_resumes_direct_effect_in_tuple_item() {
    let entry = write_entry(
        "debug-runtime-evidence-run-tuple-item-effect",
        "act flip:\n  our coin: () -> bool\n\n\
         catch (1, flip::coin()):\n\
         \x20 flip::coin(), k -> k true\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [(1, true)]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_resumes_direct_effect_in_record_field() {
    let entry = write_entry(
        "debug-runtime-evidence-run-record-field-effect",
        "act flip:\n  our coin: () -> bool\n\n\
         catch ({a: flip::coin()}):\n\
         \x20 flip::coin(), k -> k true\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [{a: true}]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_leaves_value_arm_thunk_unforced() {
    let entry = write_entry(
        "debug-runtime-evidence-run-value-arm-thunk",
        "act flip:\n  our coin: () -> bool\n\n\
         catch ({a: true}).a:\n\
         \x20 flip::coin(), k -> k true\n\
         \x20 v -> v\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [<thunk>]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_handles_recursive_all_paths_marker_route() {
    let entry = write_entry(
        "debug-runtime-evidence-run-all-paths",
        "act flip:\n  our coin: () -> bool\n\n\
         our all_paths(action: [flip] _) = catch action:\n\
         \x20 flip::coin(), k -> all_paths(k true) + all_paths(k false)\n\
         \x20 v -> [v]\n\n\
         all_paths:\n\
         \x20 if flip::coin(): 1 else: 0\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains("control_evidence.direct_effect_calls: 0"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [[1, 0]]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_resumes_through_primitive_apply() {
    let entry = write_entry(
        "debug-runtime-evidence-run-amount-primitive-apply",
        "act amount:\n  our coin: () -> int\n\n\
         our one(action: [amount] _) = catch action:\n\
         \x20 amount::coin(), k -> k 1\n\
         \x20 v -> v\n\n\
         one:\n\
         \x20 amount::coin() * 10\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [10]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_handles_recursive_amount_handler() {
    let entry = write_entry(
        "debug-runtime-evidence-run-recursive-amount",
        "act amount:\n  our coin: () -> int\n\n\
         our total_amount(action: [amount] _) =\n\
         \x20 my loop(n, action: [amount] _) = catch action:\n\
         \x20\x20 amount::coin(), k -> loop(n, k n)\n\
         \x20\x20 v -> v\n\
         \x20 [loop(1, action), loop(2, action)]\n\n\
         total_amount:\n\
         \x20 amount::coin() * 10\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(stdout.contains("run roots [[10, 20]]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_handles_nested_flip_amount_handlers() {
    let entry = write_entry(
        "debug-runtime-evidence-run-nested-flip-amount",
        "act flip:\n\
         \x20 our coin: () -> bool\n\
         act amount:\n\
         \x20 our coin: () -> int\n\n\
         our all_paths(action: [flip] _) = catch action:\n\
         \x20 flip::coin(), k -> all_paths(k true) + all_paths(k false)\n\
         \x20 v -> [v]\n\n\
         our total_amount(action: [amount] _) =\n\
         \x20 my loop(n, action: [amount] _) = catch action:\n\
         \x20\x20 amount::coin(), k -> loop(n, k n)\n\
         \x20\x20 v -> v\n\
         \x20 [loop(1, action), loop(2, action)]\n\n\
         total_amount: all_paths:\n\
         \x20 my a = if flip::coin(): amount::coin() else: 0\n\
         \x20 my b = if flip::coin(): amount::coin() * 10 else: 0\n\
         \x20 my c = if flip::coin(): amount::coin() * 100 else: 0\n\
         \x20 a + b + c\n",
    );

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-control")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.control: match"), "{stdout}");
    assert!(
        stdout.contains(
            "run roots [[[111, 11, 101, 1, 110, 10, 100, 0], \
             [222, 22, 202, 2, 220, 20, 200, 0]]]\n"
        ),
        "{stdout}"
    );
}

#[test]
fn compatible_dump_no_prelude_uses_cache() {
    let entry = write_entry("dump-no-prelude-cache", "1\n");
    let root = entry.parent().unwrap().to_path_buf();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("dump")
        .arg("--poly")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert!(stdout(&output).contains("roots"), "{}", stdout(&output));
    assert_eq!(control_cache_file_count(&cache_root), 0);
    assert_eq!(poly_cache_file_count(&cache_root), 1);
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 1);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_parse_expr_prints_event_tree() {
    let entry = write_entry("parse-expr", "1 + 2\n");

    let output = yulang_command()
        .arg("parse")
        .arg(&entry)
        .arg("--as")
        .arg("expr")
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("Expr\n"), "{stdout}");
    assert!(stdout.contains("Number \"1\""), "{stdout}");
    assert!(stdout.contains("Infix \"+\""), "{stdout}");
}

#[test]
fn install_std_writes_explicit_std_root() {
    let root = temp_root("install-std");
    let std_root = root.join("custom-std");

    let output = yulang_command()
        .arg("--std-root")
        .arg(&std_root)
        .arg("install")
        .arg("std")
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "");
    assert_eq!(stderr(&output), format!("{}\n", std_root.display()));
    assert!(std_root.join("std.yu").is_file());
    assert!(std_root.join("std").join("prelude.yu").is_file());
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn cache_path_and_clear_use_yulang_cache_dir() {
    let root = temp_root("cache");
    let cache_root = root.join("cache-root");
    fs::create_dir_all(&cache_root).unwrap();
    fs::write(cache_root.join("entry"), "cached").unwrap();
    fs::create_dir_all(cache_root.join("artifacts").join("control-vm")).unwrap();
    fs::create_dir_all(cache_root.join("artifacts").join("poly")).unwrap();
    fs::create_dir_all(cache_root.join("artifacts").join("compiled-unit")).unwrap();
    fs::write(
        cache_root
            .join("artifacts")
            .join("control-vm")
            .join("one.yuvm"),
        "",
    )
    .unwrap();
    fs::write(
        cache_root.join("artifacts").join("poly").join("one.yuir"),
        "",
    )
    .unwrap();
    fs::write(
        cache_root.join("artifacts").join("poly").join("two.yuir"),
        "",
    )
    .unwrap();

    let path_output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("cache")
        .arg("path")
        .output()
        .unwrap();
    assert_success(&path_output);
    assert_eq!(stdout(&path_output), format!("{}\n", cache_root.display()));

    let stats_output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("cache")
        .arg("stats")
        .output()
        .unwrap();
    assert_success(&stats_output);
    assert_eq!(
        stdout(&stats_output),
        format!(
            "cache: {}\ncontrol-vm: 1\nmono: 0\npoly: 2\ncompiled-unit: 0\nrealm-resolution: 0\n",
            cache_root.display()
        )
    );

    let clear_output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("cache")
        .arg("clear")
        .output()
        .unwrap();
    assert_success(&clear_output);
    assert_eq!(
        stdout(&clear_output),
        format!("cleared {}\n", cache_root.display())
    );
    assert!(!cache_root.exists());
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_dump_mono_writes_exact_mono_cache_artifact() {
    let root = temp_root("dump-mono-cache");
    let _ = fs::remove_dir_all(&root);
    let entry = root.join("main.yu");
    fs::create_dir_all(&root).unwrap();
    fs::write(&entry, "my id x = x\nid 1\n").unwrap();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("dump-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(mono_cache_file_count(&cache_root), 1);
    assert_eq!(control_cache_file_count(&cache_root), 0);
    assert_eq!(poly_cache_file_count(&cache_root), 1);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_build_populates_control_vm_cache_unless_disabled() {
    let entry = write_entry("build-control-cache", "1\n");
    let root = entry.parent().unwrap().to_path_buf();
    let cache_root = root.join("cache-root");
    let artifact = root.join("main.yuir");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("build")
        .arg("--out")
        .arg(&artifact)
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), format!("build: {}\n", artifact.display()));
    assert_eq!(control_cache_file_count(&cache_root), 1);
    assert_eq!(poly_cache_file_count(&cache_root), 1);

    let disabled_cache_root = root.join("disabled-cache");
    let disabled_artifact = root.join("disabled.yuir");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &disabled_cache_root)
        .arg("--no-cache")
        .arg("--no-prelude")
        .arg("build")
        .arg("--out")
        .arg(&disabled_artifact)
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(control_cache_file_count(&disabled_cache_root), 0);
    assert_eq!(poly_cache_file_count(&disabled_cache_root), 0);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_populates_control_vm_cache() {
    let entry = write_entry("run-control-cache", "1\n");
    let root = entry.parent().unwrap().to_path_buf();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_eq!(control_cache_file_count(&cache_root), 1);
    assert_eq!(poly_cache_file_count(&cache_root), 1);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_runtime_phase_timings_report_cache_route() {
    let entry = write_entry("runtime-phase-cache-route", "1\n");
    let root = entry.parent().unwrap().to_path_buf();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_cache_route(&output, "full-miss");
    assert_run_backend(&output, "evidence-vm");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_cache_route_any(&output, &["source-key-control-hit", "control-hit"]);
    assert_run_backend(&output, "evidence-vm");

    remove_cache_stage(&cache_root, "control-vm");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_cache_route(&output, "poly-hit");
    assert_run_backend(&output, "evidence-vm");

    remove_cache_stage(&cache_root, "control-vm");
    remove_cache_stage(&cache_root, "poly");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_cache_route(&output, "compiled-unit-hit");
    assert_run_backend(&output, "evidence-vm");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_reuses_std_compiled_unit_prefix_for_new_entry() {
    let root = temp_root("run-std-prefix-cache");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let std_root = write_minimal_std(&root);
    let cache_root = root.join("cache-root");
    let first = root.join("first.yu");
    let second = root.join("second.yu");
    fs::write(&first, "1\n").unwrap();
    fs::write(&second, "2\n").unwrap();

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(&std_root)
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&first)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [1]\n");
    assert_cache_route(&output, "std-prefix-build");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 2);

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(&std_root)
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&second)
        .output()
        .unwrap();
    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [2]\n");
    assert_cache_route(&output, "std-prefix-hit");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 3);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_uses_single_source_unit_prefix_cache() {
    let root = temp_root("run-source-unit-prefix-cache");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("a")).unwrap();
    let entry = root.join("main.yu");
    fs::write(&entry, "mod a;\nuse a::*\nx\n").unwrap();
    fs::write(root.join("a.yu"), "mod b;\npub x = b::y\n").unwrap();
    fs::write(root.join("a").join("b.yu"), "pub y = 7\n").unwrap();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [7]\n");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 3);
    assert_eq!(poly_cache_file_count(&cache_root), 1);
    assert_eq!(control_cache_file_count(&cache_root), 1);

    fs::write(&entry, "mod a;\nuse a::*\nmy keep v = v\nkeep x\n").unwrap();
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [7]\n");
    assert!(stderr(&output).contains("run.cache: source-unit-prefix-hit"));
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 4);
    assert_eq!(poly_cache_file_count(&cache_root), 2);
    assert_eq!(control_cache_file_count(&cache_root), 2);

    remove_cache_stage(&cache_root, "control-vm");
    remove_cache_stage(&cache_root, "poly");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [7]\n");
    assert_cache_route(&output, "compiled-unit-hit");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 4);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_uses_source_unit_prefix_for_editable_realm_band_imports() {
    let root = temp_root("run-editable-realm-band-source-unit-prefix-cache");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("helper")).unwrap();
    fs::write(
        root.join("realm.toml"),
        r#"[realm]
identity = "test/editable-realm-band"
"#,
    )
    .unwrap();
    let entry = root.join("main.yu");
    fs::write(
        &entry,
        "use realm/helper::answer\nuse realm/view::describe\ndescribe answer\n",
    )
    .unwrap();
    fs::write(
        root.join("helper.yu"),
        "mod inner;\nuse band::inner::value as inner_value\npub answer = inner_value\n",
    )
    .unwrap();
    fs::write(root.join("helper").join("inner.yu"), "our value = 42\n").unwrap();
    fs::write(root.join("view.yu"), "pub describe value = value\n").unwrap();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [42]\n");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 4);
    assert_eq!(poly_cache_file_count(&cache_root), 1);
    assert_eq!(control_cache_file_count(&cache_root), 1);

    fs::write(
        &entry,
        "use realm/helper::answer\nuse realm/view::describe\nmy keep value = value\nkeep (describe answer)\n",
    )
    .unwrap();
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [42]\n");
    assert_cache_route_any(
        &output,
        &["source-unit-prefix-hit", "merged-source-unit-prefix-hit"],
    );
    assert_eq!(poly_cache_file_count(&cache_root), 2);
    assert_eq!(control_cache_file_count(&cache_root), 2);

    remove_cache_stage(&cache_root, "control-vm");
    remove_cache_stage(&cache_root, "poly");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [42]\n");
    assert_cache_route(&output, "compiled-unit-hit");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_reports_dependency_lowering_errors_before_runtime() {
    let root = temp_root("run-dependency-lowering-error-before-runtime");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("helper")).unwrap();
    let entry = root.join("main.yu");
    fs::write(&entry, "use realm/helper::answer\nanswer\n").unwrap();
    fs::write(
        root.join("helper.yu"),
        "mod inner;\nuse band::inner::bonus\npub answer = 40 + bonus\n",
    )
    .unwrap();
    fs::write(root.join("helper").join("inner.yu"), "our bonus = 2\n").unwrap();

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    let stderr = stderr(&output);
    assert!(
        stderr.contains("compile error [yulang.lowering]: source has lowering errors"),
        "{stderr}"
    );
    assert!(
        stderr.contains("detail: unresolved value name: #op:infix:+"),
        "{stderr}"
    );
    assert!(
        stderr.contains("hint: run `yulang check` to see source ranges before running"),
        "{stderr}"
    );
    assert!(!stderr.contains("unbound local"), "{stderr}");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_uses_merged_source_unit_prefix_when_many_are_cached() {
    let root = temp_root("run-many-source-unit-prefix-cache");
    let _ = fs::remove_dir_all(&root);
    let entry = root.join("main.yu");
    fs::create_dir_all(&root).unwrap();
    fs::write(&entry, "mod a;\nmod b;\n(a::x, b::y)\n").unwrap();
    fs::write(root.join("a.yu"), "pub x = 10\n").unwrap();
    fs::write(root.join("b.yu"), "pub y = 2\n").unwrap();
    let cache_root = root.join("cache-root");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [(10, 2)]\n");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 3);
    assert_eq!(poly_cache_file_count(&cache_root), 1);
    assert_eq!(control_cache_file_count(&cache_root), 1);

    fs::write(&entry, "mod a;\nmod b;\nmy keep v = v\nkeep (a::x, b::y)\n").unwrap();
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [(10, 2)]\n");
    assert_cache_route(&output, "merged-source-unit-prefix-hit");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 5);
    assert_eq!(poly_cache_file_count(&cache_root), 2);
    assert_eq!(control_cache_file_count(&cache_root), 2);

    remove_cache_stage(&cache_root, "control-vm");
    remove_cache_stage(&cache_root, "poly");
    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--no-prelude")
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [(10, 2)]\n");
    assert_cache_route(&output, "compiled-unit-hit");
    assert_eq!(compiled_unit_cache_file_count(&cache_root), 5);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn public_regression_list_update_runs_through_cli_cache() {
    let root = temp_root("public-regression-list-update");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let cache_root = root.join("cache-root");
    let entry = repo_yulang_fixture("regressions/runtime/list_update.yu");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [[2, 6, 4]]\n");
    assert_eq!(control_cache_file_count(&cache_root), 1);
    assert_eq!(poly_cache_file_count(&cache_root), 1);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn public_regression_runtime_fixtures_run_through_cli_golden() {
    let cases = [
        (
            "nondet-once-triple",
            "regressions/runtime/nondet_once_triple.yu",
            "run roots [opt::just((3, 4, 5))]\n",
        ),
        (
            "optional-record-defaults",
            "regressions/runtime/optional_record_defaults.yu",
            "run roots [6, 2, 12, 12]\n",
        ),
        (
            "attached-impl-pick",
            "regressions/runtime/attached_impl_pick.yu",
            "run roots [(10, false)]\n",
        ),
    ];

    for (slug, fixture, expected_stdout) in cases {
        let root = temp_root(&format!("public-regression-{slug}"));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        let cache_root = root.join("cache-root");
        let entry = repo_yulang_fixture(fixture);

        let output = yulang_command()
            .env("YULANG_CACHE_DIR", &cache_root)
            .arg("--std-root")
            .arg(repo_lib_root())
            .arg("run")
            .arg("--print-roots")
            .arg(&entry)
            .output()
            .unwrap();

        assert_success(&output);
        assert_eq!(stdout(&output), expected_stdout, "{slug}");
        assert_eq!(control_cache_file_count(&cache_root), 1, "{slug}");
        assert_eq!(poly_cache_file_count(&cache_root), 1, "{slug}");

        let _ = fs::remove_dir_all(&root);
    }
}

#[test]
fn public_contract_manifest_cli_cases_hold() {
    let cases = public_contract_manifest_cases();
    assert!(!cases.is_empty());

    let mut names = BTreeSet::new();
    for case in cases {
        assert!(
            names.insert(case.name.clone()),
            "duplicate contract manifest case name {}",
            case.name
        );
        assert!(
            !case.contracts.is_empty(),
            "contract manifest case {} should list contracts",
            case.name
        );
        assert_contract_manifest_tags_are_canonical(&case);
        assert_contract_manifest_tags_match_kind(&case);
        assert_contract_manifest_tags_match_shape(&case);
        assert_contract_manifest_case_has_expectation(&case);
        assert_contract_manifest_diagnostic_shape(&case);
        assert!(
            public_contract_case_entry(&case).exists(),
            "contract manifest case {} points at missing fixture {}",
            case.name,
            case.file
        );

        match case.kind.as_str() {
            "run" => run_contract_manifest_case(&case),
            "check" => check_contract_manifest_case(&case),
            "public-signature" => public_signature_contract_manifest_case(&case),
            other => panic!(
                "unsupported contract manifest case kind `{other}`: {}",
                case.name
            ),
        }
    }
}

#[test]
fn contract_command_runs_filtered_runtime_case() {
    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("contract")
        .arg("--case")
        .arg("optional_record_defaults")
        .arg(repo_yulang_fixture("cases.toml"))
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "contract cases ok: 1\n");
    assert_eq!(stderr(&output), "");
}

#[test]
fn contract_command_runs_filtered_public_signature_case() {
    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("contract")
        .arg("--case")
        .arg("std_result_unwrap_or_public_signature")
        .arg(repo_yulang_fixture("cases.toml"))
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "contract cases ok: 1\n");
    assert_eq!(stderr(&output), "");
}

#[test]
fn contract_command_filters_by_contract_tag() {
    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("contract")
        .arg("--contract")
        .arg("stable-core")
        .arg("--case")
        .arg("optional_record_defaults")
        .arg(repo_yulang_fixture("cases.toml"))
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "contract cases ok: 1\n");
    assert_eq!(stderr(&output), "");
}

#[test]
fn contract_command_rejects_unknown_contract_tag() {
    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("contract")
        .arg("--contract")
        .arg("stablecore")
        .arg(repo_yulang_fixture("cases.toml"))
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    assert!(
        stderr(&output).contains("has no contract tag `stablecore`"),
        "{}",
        stderr(&output)
    );
}

#[test]
fn contract_command_rejects_unknown_manifest_contract_tag() {
    let root = temp_root("contract-rejects-unknown-manifest-tag");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let manifest = root.join("cases.toml");
    fs::write(
        &manifest,
        r#"
[[case]]
name = "bad_tag"
file = "support/unused.yu"
kind = "run"
contracts = ["runtime", "stablecore"]
"#,
    )
    .unwrap();

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("contract")
        .arg(&manifest)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    assert!(
        stderr(&output).contains("has unknown contract tag `stablecore`"),
        "{}",
        stderr(&output)
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn contract_command_rejects_file_resource_runtime_case_without_host_scope() {
    let root = temp_root("contract-rejects-file-resource-without-host-scope");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let manifest = root.join("cases.toml");
    fs::write(
        &manifest,
        r#"
[[case]]
name = "bad_file_resource"
file = "support/unused.yu"
kind = "run"
contracts = [
    "runtime",
    "standard-api",
    "migration-canary",
    "file",
    "file-resource",
    "resource-lifetime",
]
"#,
    )
    .unwrap();

    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("contract")
        .arg(&manifest)
        .output()
        .unwrap();

    assert!(
        !output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(&output),
        stderr(&output)
    );
    assert_eq!(stdout(&output), "");
    assert!(
        stderr(&output).contains(
            "file-resource runtime case `bad_file_resource` should carry exactly one host scope"
        ),
        "{}",
        stderr(&output)
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn public_contract_manifest_covers_status_spine_claims() {
    let status_path = repo_file("docs/status.md");
    let status = fs::read_to_string(&status_path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", status_path.display()));
    for claim in [
        "Public signatures",
        "Runtime behavior",
        "Diagnostics",
        "Release artifacts",
        "Standard API surface",
        "Yulang Contract v0",
        "stable-core",
        "std::data::result",
        "std::text::path",
        "std::io::file",
    ] {
        assert!(
            status.contains(claim),
            "docs/status.md should keep Public Contract Spine claim {claim:?}"
        );
    }

    let cases = public_contract_manifest_cases();
    for requirement in [
        StatusSpineManifestRequirement::new("public signatures", &["public-signature"]),
        StatusSpineManifestRequirement::new("stable core", &["stable-core"]),
        StatusSpineManifestRequirement::new("stable core runtime", &["stable-core", "runtime"]),
        StatusSpineManifestRequirement::new(
            "stable core diagnostics",
            &["stable-core", "diagnostics"],
        ),
        StatusSpineManifestRequirement::new(
            "stable core public signatures",
            &["stable-core", "public-signature"],
        ),
        StatusSpineManifestRequirement::new(
            "stable core public examples",
            &["stable-core", "public-example"],
        ),
        StatusSpineManifestRequirement::new("runtime behavior", &["runtime"]),
        StatusSpineManifestRequirement::new("public examples", &["public-example"]),
        StatusSpineManifestRequirement::new("runtime error behavior", &["runtime-error"]),
        StatusSpineManifestRequirement::new("diagnostics", &["diagnostics"]),
        StatusSpineManifestRequirement::new("standard API", &["standard-api"]),
        StatusSpineManifestRequirement::new("stable standard API", &["standard-api", "stable-api"]),
        StatusSpineManifestRequirement::new(
            "stable core standard API",
            &["stable-core", "standard-api", "stable-api"],
        ),
        StatusSpineManifestRequirement::new(
            "standard API migration canary",
            &["standard-api", "migration-canary"],
        ),
        StatusSpineManifestRequirement::new("result API", &["standard-api", "result"]),
        StatusSpineManifestRequirement::new("error API", &["standard-api", "errors"]),
        StatusSpineManifestRequirement::new("path API", &["standard-api", "path"]),
        StatusSpineManifestRequirement::new(
            "native file API host scope",
            &["standard-api", "file", "host.native"],
        ),
    ] {
        assert!(
            contract_manifest_has_case_with_tags(&cases, requirement.tags),
            "docs/status.md claims {}, but tests/yulang/cases.toml has no case tagged {:?}",
            requirement.label,
            requirement.tags
        );
    }
}

struct StatusSpineManifestRequirement<'a> {
    label: &'a str,
    tags: &'a [&'a str],
}

impl<'a> StatusSpineManifestRequirement<'a> {
    fn new(label: &'a str, tags: &'a [&'a str]) -> Self {
        Self { label, tags }
    }
}

fn contract_manifest_has_case_with_tags(cases: &[PublicContractCase], tags: &[&str]) -> bool {
    cases.iter().any(|case| {
        tags.iter()
            .all(|tag| contract_manifest_case_has_tag(case, tag))
    })
}

fn assert_contract_manifest_tags_are_canonical(case: &PublicContractCase) {
    for tag in &case.contracts {
        assert!(
            is_canonical_contract_tag(tag),
            "contract manifest case {} has non-canonical contract tag {:?}",
            case.name,
            tag
        );
        assert!(
            is_known_contract_tag(tag),
            "contract manifest case {} has unknown contract tag {:?}",
            case.name,
            tag
        );
    }
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
            | "host.native"
            | "host.unsupported"
            | "junction"
            | "lists"
            | "migration-canary"
            | "mock-host"
            | "names"
            | "parser-dsl"
            | "path"
            | "patterns"
            | "preview"
            | "public-example"
            | "public-signature"
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

fn assert_contract_manifest_diagnostic_shape(case: &PublicContractCase) {
    if case.kind != "check" {
        assert!(
            case.expect_diagnostic_start.is_none() && case.expect_diagnostic_end.is_none(),
            "non-check contract manifest case {} should not assert source diagnostic primary ranges",
            case.name
        );
        return;
    }

    assert!(
        case.expect_diagnostic_count.is_some(),
        "check contract manifest case {} should assert diagnostic count",
        case.name
    );
    assert!(
        case.expect_diagnostic_code.is_some(),
        "check contract manifest case {} should assert diagnostic code",
        case.name
    );
    assert!(
        case.expect_diagnostic_severity.is_some(),
        "check contract manifest case {} should assert diagnostic severity",
        case.name
    );
    assert!(
        case.expect_diagnostic_start.is_some() && case.expect_diagnostic_end.is_some(),
        "check contract manifest case {} should assert a complete diagnostic primary range",
        case.name
    );
    assert!(
        case.expect_diagnostic_related_count.is_some(),
        "check contract manifest case {} should assert related diagnostic count",
        case.name
    );
    if let Some(related_count) = case.expect_diagnostic_related_count {
        assert!(
            case.expect_diagnostic_related_origins.is_empty()
                || case.expect_diagnostic_related_origins.len() == related_count,
            "check contract manifest case {} should keep related origins aligned with related count",
            case.name
        );
    }
}

fn assert_contract_manifest_tags_match_shape(case: &PublicContractCase) {
    if contract_manifest_case_has_tag(case, "runtime-error") {
        let is_runtime_failure = contract_manifest_case_has_tag(case, "runtime-failure");
        let is_compile_error = contract_manifest_case_has_tag(case, "compile-error");
        assert_eq!(
            case.expect_success,
            Some(false),
            "runtime-error contract manifest case {} should set expect_success = false",
            case.name
        );
        assert!(
            is_runtime_failure ^ is_compile_error,
            "runtime-error contract manifest case {} should be tagged exactly one of runtime-failure or compile-error",
            case.name
        );
        if is_compile_error {
            assert_eq!(
                case.kind, "run",
                "compile-error contract manifest case {} should remain a run-only migration marker; add a separate check case for SourceDiagnostic coverage",
                case.name
            );
            assert!(
                contract_manifest_case_has_tag(case, "diagnostics"),
                "compile-error contract manifest case {} should be tagged diagnostics",
                case.name
            );
            assert!(
                contract_manifest_case_expects_stderr_prefix(case, "compile error ["),
                "compile-error contract manifest case {} should assert a compile error prefix",
                case.name
            );
        }
        if is_runtime_failure {
            assert!(
                contract_manifest_case_expects_stderr_prefix(case, "runtime error ["),
                "runtime-failure contract manifest case {} should assert a runtime error prefix",
                case.name
            );
        }
    } else {
        assert!(
            !contract_manifest_case_has_any_tag(case, &["runtime-failure", "compile-error"]),
            "non-runtime-error contract manifest case {} should not use runtime-failure or compile-error tags",
            case.name
        );
    }

    if contract_manifest_case_has_tag(case, "public-example") {
        assert_eq!(
            case.root.as_deref(),
            Some("repo"),
            "public-example contract manifest case {} should read from repo root",
            case.name
        );
        assert!(
            case.file.starts_with("examples/"),
            "public-example contract manifest case {} should point at examples/, got {}",
            case.name,
            case.file
        );
    }

    if contract_manifest_case_has_tag(case, "standard-api") {
        let is_stable_api = contract_manifest_case_has_tag(case, "stable-api");
        let is_migration_canary = contract_manifest_case_has_tag(case, "migration-canary");
        assert!(
            is_stable_api ^ is_migration_canary,
            "standard-api contract manifest case {} should be tagged exactly one of stable-api or migration-canary",
            case.name
        );
        assert!(
            contract_manifest_case_has_any_tag(case, &["result", "errors", "path", "file"]),
            "standard-api contract manifest case {} should include a narrower API area tag",
            case.name
        );
        if contract_manifest_case_has_tag(case, "file") {
            assert!(
                contract_manifest_case_has_any_tag(case, &["host.native", "host.unsupported"]),
                "standard-api file contract manifest case {} should declare host scope",
                case.name
            );
        }
    }
    if !case.temp_files.is_empty() {
        assert_eq!(
            case.kind, "run",
            "contract manifest case {} should only use temp_files for run cases",
            case.name
        );
        let mut placeholders = BTreeSet::new();
        for temp_file in &case.temp_files {
            assert!(
                !temp_file.placeholder.is_empty(),
                "contract manifest case {} has an empty temp file placeholder",
                case.name
            );
            assert!(
                placeholders.insert(temp_file.placeholder.as_str()),
                "contract manifest case {} reuses temp file placeholder {:?}",
                case.name,
                temp_file.placeholder
            );
        }
    }
    if contract_manifest_case_has_tag(case, "file-resource") {
        assert!(
            !contract_manifest_case_has_tag(case, "stable-core"),
            "file-resource contract manifest case {} should not be stable-core",
            case.name
        );
        if case.kind == "run" {
            let host_scope_count = ["mock-host", "host.native", "host.unsupported"]
                .into_iter()
                .filter(|tag| contract_manifest_case_has_tag(case, tag))
                .count();
            assert_eq!(
                host_scope_count, 1,
                "file-resource runtime case {} should declare exactly one host scope",
                case.name
            );
            assert!(
                contract_manifest_case_has_tag(case, "resource-lifetime"),
                "file-resource runtime case {} should declare resource-lifetime",
                case.name
            );
        }
    }
    if contract_manifest_case_has_any_tag(case, &["stable-api", "migration-canary"]) {
        assert!(
            contract_manifest_case_has_tag(case, "standard-api"),
            "contract manifest case {} should only use stable-api or migration-canary with standard-api",
            case.name
        );
    }
    if contract_manifest_case_has_tag(case, "stable-core") {
        assert!(
            !contract_manifest_case_has_any_tag(
                case,
                &["preview", "migration-canary", "compile-error"]
            ),
            "stable-core contract manifest case {} should not be preview, migration-canary, or compile-error",
            case.name
        );
    }

    if case.kind == "public-signature" {
        assert!(
            case.expect_type.is_some(),
            "public-signature contract manifest case {} should assert an exact expected type",
            case.name
        );
    }
}

fn assert_contract_manifest_tags_match_kind(case: &PublicContractCase) {
    match case.kind.as_str() {
        "run" => assert!(
            contract_manifest_case_has_any_tag(
                case,
                &["runtime", "runtime-error", "public-example"]
            ),
            "run contract manifest case {} should be tagged runtime, runtime-error, or public-example",
            case.name
        ),
        "check" => assert!(
            contract_manifest_case_has_tag(case, "diagnostics"),
            "check contract manifest case {} should be tagged diagnostics",
            case.name
        ),
        "public-signature" => assert!(
            contract_manifest_case_has_tag(case, "public-signature"),
            "public-signature contract manifest case {} should be tagged public-signature",
            case.name
        ),
        other => panic!(
            "unsupported contract manifest case kind `{other}`: {}",
            case.name
        ),
    }
}

fn contract_manifest_case_has_any_tag(case: &PublicContractCase, tags: &[&str]) -> bool {
    tags.iter()
        .any(|tag| contract_manifest_case_has_tag(case, tag))
}

fn contract_manifest_case_has_tag(case: &PublicContractCase, tag: &str) -> bool {
    case.contracts
        .iter()
        .any(|contract| contract.as_str() == tag)
}

fn contract_manifest_case_expects_stderr_prefix(case: &PublicContractCase, prefix: &str) -> bool {
    case.expect_stderr
        .as_deref()
        .map_or(false, |stderr| stderr.starts_with(prefix))
        || case
            .expect_stderr_contains
            .iter()
            .any(|fragment| fragment.starts_with(prefix))
}

fn assert_contract_manifest_case_has_expectation(case: &PublicContractCase) {
    let has_output_expectation = case.expect_stdout.is_some()
        || case.expect_stderr.is_some()
        || !case.expect_stdout_contains.is_empty()
        || !case.expect_stderr_contains.is_empty()
        || case.expect_type.is_some()
        || !case.expect_type_contains.is_empty()
        || !case.deny_type_contains.is_empty()
        || case.expect_diagnostic_count.is_some()
        || case.expect_diagnostic_code.is_some()
        || case.expect_diagnostic_severity.is_some()
        || case.expect_diagnostic_label.is_some()
        || case.expect_diagnostic_start.is_some()
        || case.expect_diagnostic_end.is_some()
        || case.expect_diagnostic_related_count.is_some()
        || !case.expect_diagnostic_related_origins.is_empty();
    assert!(
        has_output_expectation,
        "contract manifest case {} should assert output or public type",
        case.name
    );
}

#[test]
fn public_regression_ref_update_loop_runs_on_cli_vm_stack() {
    let root = temp_root("public-regression-ref-update-loop");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let cache_root = root.join("cache-root");
    let entry = root.join("main.yu");
    fs::write(
        &entry,
        r#"{
    my $x = 0
    for i in 0..:
        if i == 100: last
        &x = $x + 1
    $x
}
"#,
    )
    .unwrap();

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [100]\n");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn realm_freeze_writes_versioned_snapshot() {
    let root = temp_root("realm-freeze");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("realm.toml"),
        r#"[realm]
identity = "app"
"#,
    )
    .unwrap();
    fs::write(root.join("main.yu"), "my main = 1\n").unwrap();

    let output = yulang_command()
        .arg("realm")
        .arg("freeze")
        .arg(&root)
        .arg("--version")
        .arg("1.0.0")
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("realm freeze: frozen "), "{stdout}");
    assert!(stdout.contains(" files=2\n"), "{stdout}");
    assert!(
        root.join(".yulang")
            .join("versions")
            .join("1.0.0")
            .join("snapshot.json")
            .is_file()
    );
    let frozen_manifest = fs::read_to_string(
        root.join(".yulang")
            .join("versions")
            .join("1.0.0")
            .join("realm.toml"),
    )
    .unwrap();
    assert!(!frozen_manifest.contains("version = "));
    assert!(!frozen_manifest.contains("[dependencies]"));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn realm_install_installs_local_snapshot_for_import() {
    let root = temp_root("realm-install");
    let _ = fs::remove_dir_all(&root);
    let lib_root = root.join("lib");
    let realm_root = root.join("theme");
    let app_root = root.join("app");
    fs::create_dir_all(&realm_root).unwrap();
    fs::create_dir_all(&app_root).unwrap();
    fs::write(
        realm_root.join("realm.toml"),
        r#"[realm]
name = "theme"
version = "1.0.0"
"#,
    )
    .unwrap();
    fs::write(realm_root.join("colors.yu"), "pub value = 7\n").unwrap();
    let main_path = app_root.join("main.yu");
    fs::write(&main_path, "use local/theme/colors::value v1.0.0\nvalue\n").unwrap();

    let install = yulang_command()
        .env("YULANG_LIB_DIR", &lib_root)
        .arg("realm")
        .arg("install")
        .arg(&realm_root)
        .output()
        .unwrap();

    assert_success(&install);
    let install_stdout = stdout(&install);
    assert!(
        install_stdout.contains("realm install: installed "),
        "{install_stdout}"
    );
    assert!(install_stdout.contains(" files=2\n"), "{install_stdout}");
    assert!(
        lib_root
            .join("realms")
            .join("local")
            .join("theme")
            .join("1.0.0")
            .join("snapshot.json")
            .is_file()
    );

    let run = yulang_command()
        .env("YULANG_LIB_DIR", &lib_root)
        .arg("--no-prelude")
        .arg("run")
        .arg("--print-roots")
        .arg(&main_path)
        .output()
        .unwrap();

    assert_success(&run);
    assert_eq!(stdout(&run), "run roots [7]\n");

    let _ = fs::remove_dir_all(&root);
}

fn yulang_command() -> Command {
    Command::new(env!("CARGO_BIN_EXE_yulang"))
}

fn yulang_command_with_stdin<const N: usize>(args: [&str; N], stdin: &str) -> Output {
    let mut child = yulang_command()
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn write_fixture(name: &str, source: &str) -> (PathBuf, PathBuf) {
    let root = temp_root(name);
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let std_root = write_minimal_std(&root);
    let entry = root.join("main.yu");
    fs::write(&entry, source).unwrap();
    (entry, std_root)
}

fn write_entry(name: &str, source: &str) -> PathBuf {
    let root = temp_root(name);
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let entry = root.join("main.yu");
    fs::write(&entry, source).unwrap();
    entry
}

fn write_minimal_std(root: &Path) -> PathBuf {
    let std_root = root.join("lib");
    fs::create_dir_all(std_root.join("std")).unwrap();
    fs::write(std_root.join("std.yu"), "mod prelude;\n").unwrap();
    fs::write(std_root.join("std").join("prelude.yu"), "").unwrap();
    std_root
}

fn repo_lib_root() -> PathBuf {
    repo_file("lib")
}

fn repo_yulang_fixture(path: &str) -> PathBuf {
    repo_file("tests").join("yulang").join(path)
}

#[derive(Debug, Deserialize)]
struct PublicContractManifest {
    case: Vec<PublicContractCase>,
}

#[derive(Debug, Deserialize)]
struct PublicContractCase {
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
    temp_files: Vec<PublicContractTempFile>,
    #[serde(default)]
    contracts: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct PublicContractTempFile {
    placeholder: String,
    contents: String,
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

fn public_contract_manifest_cases() -> Vec<PublicContractCase> {
    let manifest_path = repo_yulang_fixture("cases.toml");
    let manifest = fs::read_to_string(&manifest_path).unwrap_or_else(|error| {
        panic!(
            "failed to read public contract manifest {}: {error}",
            manifest_path.display()
        )
    });
    toml::from_str::<PublicContractManifest>(&manifest)
        .unwrap_or_else(|error| panic!("failed to parse {}: {error}", manifest_path.display()))
        .case
}

fn run_contract_manifest_case(case: &PublicContractCase) {
    let root = temp_root(&format!("public-contract-{}", case.name));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let cache_root = root.join("cache-root");
    let source_entry = public_contract_case_entry(case);
    let materialized = materialize_contract_run_case(case, &source_entry, &root);

    let mut command = yulang_command();
    push_contract_std_args(&mut command, case);
    command.env("YULANG_CACHE_DIR", &cache_root).arg("run");
    if case.print_roots.unwrap_or(true) {
        command.arg("--print-roots");
    }
    let output = command.arg(&materialized.entry).output().unwrap();

    assert_contract_status(case, &output);
    assert_contract_output(case, &output);
    assert_contract_temp_files(case, &materialized.temp_files);

    let _ = fs::remove_dir_all(&root);
}

fn materialize_contract_run_case(
    case: &PublicContractCase,
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
        panic!(
            "failed to read contract case source {} for {}: {error}",
            source_entry.display(),
            case.name
        )
    });
    let mut temp_files = Vec::new();
    for (index, temp_file) in case.temp_files.iter().enumerate() {
        assert!(
            source.contains(&temp_file.placeholder),
            "contract manifest case {} temp file placeholder {:?} is not present in {}",
            case.name,
            temp_file.placeholder,
            source_entry.display()
        );
        let path = root.join(format!("temp-{index}.txt"));
        fs::write(&path, &temp_file.contents).unwrap_or_else(|error| {
            panic!(
                "failed to write temp file {} for contract case {}: {error}",
                path.display(),
                case.name
            )
        });
        source = source.replace(&temp_file.placeholder, &yulang_string_literal(&path));
        temp_files.push(MaterializedContractTempFile {
            path,
            expect_contents: temp_file.expect_contents.clone(),
        });
    }

    let entry = root.join("main.yu");
    fs::write(&entry, source).unwrap_or_else(|error| {
        panic!(
            "failed to materialize contract case {} at {}: {error}",
            case.name,
            entry.display()
        )
    });

    MaterializedContractRunCase { entry, temp_files }
}

fn assert_contract_temp_files(
    case: &PublicContractCase,
    temp_files: &[MaterializedContractTempFile],
) {
    for temp_file in temp_files {
        if let Some(expected) = &temp_file.expect_contents {
            let actual = fs::read_to_string(&temp_file.path).unwrap_or_else(|error| {
                panic!(
                    "failed to read temp file {} for contract case {}: {error}",
                    temp_file.path.display(),
                    case.name
                )
            });
            assert_eq!(
                &actual,
                expected,
                "contract manifest case {} temp file {}",
                case.name,
                temp_file.path.display()
            );
        }
    }
}

fn check_contract_manifest_case(case: &PublicContractCase) {
    let entry = public_contract_case_entry(case);
    let mut command = yulang_command();
    push_contract_std_args(&mut command, case);
    command.arg("--no-cache").arg("check");
    let output = command.arg(&entry).output().unwrap();

    assert_contract_status(case, &output);
    assert_contract_output(case, &output);
    assert_contract_diagnostics(case, &entry);
}

fn public_signature_contract_manifest_case(case: &PublicContractCase) {
    let entry = public_contract_case_entry(case);
    let output = match (
        case.std.as_deref().unwrap_or("repo"),
        case.module.as_deref(),
    ) {
        ("repo", Some(module)) => {
            yulang::dump_poly_from_entry_with_std_in_module(&entry, module).unwrap()
        }
        ("repo", None) => yulang::dump_poly_from_entry_with_std(&entry).unwrap(),
        ("none", None) => yulang::dump_poly_from_entry(&entry).unwrap(),
        ("none", Some(module)) => {
            panic!(
                "contract case {} cannot request module `{module}` without std",
                case.name
            )
        }
        (other, _) => panic!(
            "unsupported std mode `{other}` in contract case {}",
            case.name
        ),
    };
    let ty = public_contract_signature_type(case, &output);
    assert_public_contract_signature_type_is_clean(case, &ty);

    if let Some(expected) = &case.expect_type {
        assert_eq!(&ty, expected, "{}", case.name);
    }
    for expected in &case.expect_type_contains {
        assert!(
            ty.contains(expected),
            "case {} missing type fragment {expected:?}:\n{ty}",
            case.name
        );
    }
    for denied in &case.deny_type_contains {
        assert!(
            !ty.contains(denied),
            "case {} leaked denied type fragment {denied:?}:\n{ty}",
            case.name
        );
    }
}

fn assert_public_contract_signature_type_is_clean(case: &PublicContractCase, ty: &str) {
    for denied in ["#", "AllExcept", "Unknown", "Any"] {
        assert!(
            !ty.contains(denied),
            "case {} leaked private public-signature fragment {denied:?}:\n{ty}",
            case.name
        );
    }
}

fn push_contract_std_args(command: &mut Command, case: &PublicContractCase) {
    match case.std.as_deref().unwrap_or("repo") {
        "repo" => {
            command.arg("--std-root").arg(repo_lib_root());
        }
        "none" => {
            command.arg("--no-prelude");
        }
        other => panic!(
            "unsupported std mode `{other}` in contract case {}",
            case.name
        ),
    }
}

fn public_contract_case_entry(case: &PublicContractCase) -> PathBuf {
    match case.root.as_deref().unwrap_or("tests/yulang") {
        "tests/yulang" => repo_yulang_fixture(&case.file),
        "repo" => repo_file(&case.file),
        other => panic!(
            "unsupported root mode `{other}` in contract case {}",
            case.name
        ),
    }
}

fn assert_contract_diagnostics(case: &PublicContractCase, entry: &Path) {
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

    let source = fs::read_to_string(entry).unwrap();
    let output = match case.std.as_deref().unwrap_or("repo") {
        "repo" => yulang::analyze_entry_source_with_std_options(
            entry,
            source,
            &yulang::StdSourceOptions {
                std_root: Some(repo_lib_root()),
            },
        )
        .unwrap(),
        "none" => yulang::analyze_entry_source(entry, source).unwrap(),
        other => panic!(
            "unsupported std mode `{other}` in contract case {}",
            case.name
        ),
    };
    let diagnostic = output.diagnostics.first().unwrap_or_else(|| {
        panic!(
            "contract manifest case {} expected a diagnostic payload",
            case.name
        )
    });

    if let Some(expected) = case.expect_diagnostic_count {
        assert_eq!(output.diagnostics.len(), expected, "{}", case.name);
    }
    if let Some(expected) = &case.expect_diagnostic_code {
        assert_eq!(diagnostic.code.as_ref(), Some(expected), "{}", case.name);
    }
    if let Some(expected) = &case.expect_diagnostic_severity {
        assert_eq!(
            public_contract_diagnostic_severity_name(diagnostic.severity),
            expected,
            "{}",
            case.name
        );
    }
    if let Some(expected) = &case.expect_diagnostic_label {
        assert_eq!(diagnostic.label.as_ref(), Some(expected), "{}", case.name);
    }
    if case.expect_diagnostic_start.is_some() || case.expect_diagnostic_end.is_some() {
        let range = diagnostic.range.unwrap_or_else(|| {
            panic!(
                "contract manifest case {} expected a diagnostic primary range",
                case.name
            )
        });
        if let Some(expected) = case.expect_diagnostic_start {
            assert_eq!(range.start, expected, "{}", case.name);
        }
        if let Some(expected) = case.expect_diagnostic_end {
            assert_eq!(range.end, expected, "{}", case.name);
        }
    }
    if let Some(expected) = case.expect_diagnostic_related_count {
        assert_eq!(diagnostic.related.len(), expected, "{}", case.name);
    }
    if !case.expect_diagnostic_related_origins.is_empty() {
        let origins = diagnostic
            .related
            .iter()
            .map(|related| public_contract_related_origin_name(related.origin.as_ref()))
            .collect::<Vec<_>>();
        assert_eq!(
            origins, case.expect_diagnostic_related_origins,
            "{}",
            case.name
        );
    }
}

fn public_contract_related_origin_name(
    origin: Option<&yulang::SourceDiagnosticRelatedOrigin>,
) -> &'static str {
    match origin {
        Some(yulang::SourceDiagnosticRelatedOrigin::TypeAnnotation) => "type-annotation",
        Some(yulang::SourceDiagnosticRelatedOrigin::Expression) => "expression",
        None => "none",
    }
}

fn public_contract_diagnostic_severity_name(
    severity: yulang::SourceDiagnosticSeverity,
) -> &'static str {
    match severity {
        yulang::SourceDiagnosticSeverity::Error => "error",
    }
}

fn public_contract_signature_type(
    case: &PublicContractCase,
    output: &yulang::DumpPolyOutput,
) -> String {
    match (&case.symbol, &case.symbol_contains) {
        (Some(symbol), None) => dump_public_signature_type(output, symbol).to_string(),
        (None, Some(needle)) => dump_public_signature_type_containing(output, needle).to_string(),
        _ => panic!(
            "public-signature case {} must set exactly one of symbol or symbol_contains",
            case.name
        ),
    }
}

fn dump_public_signature_type<'a>(output: &'a yulang::DumpPolyOutput, symbol: &str) -> &'a str {
    let signature = dump_public_signature(output, symbol);
    let quoted = format!("\"{symbol}\": ");
    if let Some(start) = signature.find(&quoted) {
        return &signature[start + quoted.len()..];
    }
    let simple = format!(":{symbol}: ");
    if let Some(start) = signature.find(&simple) {
        return &signature[start + simple.len()..];
    }
    panic!("public symbol {symbol:?} has an unexpected signature line:\n{signature}");
}

fn dump_public_signature<'a>(output: &'a yulang::DumpPolyOutput, symbol: &str) -> &'a str {
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
            panic!(
                "public symbol {symbol:?} should be dumped:\n{}",
                output.text
            )
        });
    trim_public_signature_body(line)
}

fn dump_public_signature_type_containing<'a>(
    output: &'a yulang::DumpPolyOutput,
    needle: &str,
) -> &'a str {
    let signature = dump_public_signature_containing(output, needle);
    let Some(start) = signature.find("\": ") else {
        panic!("public signature containing {needle:?} is not quoted:\n{signature}");
    };
    &signature[start + "\": ".len()..]
}

fn dump_public_signature_containing<'a>(
    output: &'a yulang::DumpPolyOutput,
    needle: &str,
) -> &'a str {
    let line = output
        .text
        .lines()
        .find(|line| line.trim_start().starts_with("pub ") && line.contains(needle))
        .unwrap_or_else(|| {
            panic!(
                "public signature containing {needle:?} should be dumped:\n{}",
                output.text
            )
        });
    trim_public_signature_body(line)
}

fn trim_public_signature_body(line: &str) -> &str {
    line.find(" = e")
        .or_else(|| line.find(" = <missing>"))
        .map(|body_start| &line[..body_start])
        .unwrap_or(line)
}

fn assert_contract_status(case: &PublicContractCase, output: &Output) {
    let expected_success = case.expect_success.unwrap_or(true);
    assert_eq!(
        output.status.success(),
        expected_success,
        "case {}\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        case.name,
        output.status,
        stdout(output),
        stderr(output)
    );
}

fn assert_contract_output(case: &PublicContractCase, output: &Output) {
    let stdout = stdout(output);
    let stderr = stderr(output);

    if let Some(expected_stdout) = &case.expect_stdout {
        assert_eq!(&stdout, expected_stdout, "{}", case.name);
    }
    if let Some(expected_stderr) = &case.expect_stderr {
        assert_eq!(&stderr, expected_stderr, "{}", case.name);
    }
    for expected in &case.expect_stdout_contains {
        assert!(
            stdout.contains(expected),
            "case {} missing stdout fragment {expected:?}:\n{stdout}",
            case.name
        );
    }
    for expected in &case.expect_stderr_contains {
        assert!(
            stderr.contains(expected),
            "case {} missing stderr fragment {expected:?}:\n{stderr}",
            case.name
        );
    }
}

fn repo_file(path: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(path)
}

fn yulang_string_literal(path: &Path) -> String {
    format!("{:?}", path.display().to_string())
}

fn temp_root(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "yulang-cli-{name}-{}",
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ))
}

fn control_cache_file_count(root: &Path) -> usize {
    artifact_cache_file_count(root, "control-vm")
}

fn poly_cache_file_count(root: &Path) -> usize {
    artifact_cache_file_count(root, "poly")
}

fn mono_cache_file_count(root: &Path) -> usize {
    artifact_cache_file_count(root, "mono")
}

fn compiled_unit_cache_file_count(root: &Path) -> usize {
    artifact_cache_file_count(root, "compiled-unit")
}

fn remove_cache_stage(root: &Path, stage: &str) {
    let _ = fs::remove_dir_all(root.join("artifacts").join(stage));
}

fn assert_cache_route(output: &Output, route: &str) {
    let stderr = stderr(output);
    assert!(stderr.contains(&format!("run.cache: {route}")), "{stderr}");
}

fn assert_cache_route_any(output: &Output, routes: &[&str]) {
    let stderr = stderr(output);
    assert!(
        routes
            .iter()
            .any(|route| stderr.contains(&format!("run.cache: {route}"))),
        "{stderr}"
    );
}

fn assert_run_backend(output: &Output, backend: &str) {
    let stderr = stderr(output);
    assert!(
        stderr.contains(&format!("run.backend: {backend}")),
        "{stderr}"
    );
}

fn artifact_cache_file_count(root: &Path, stage: &str) -> usize {
    let dir = root.join("artifacts").join(stage);
    match fs::read_dir(dir) {
        Ok(entries) => entries
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.is_file())
            .count(),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => 0,
        Err(error) => panic!("failed to read cache dir: {error}"),
    }
}

fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout(output),
        stderr(output)
    );
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}
