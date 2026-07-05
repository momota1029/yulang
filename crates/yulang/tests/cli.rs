use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{Shutdown, TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

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
fn compatible_run_std_file_text_with_host_contract() {
    let root = temp_root("run-std-file-text-with");
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
use std::control::var::*

my direct_result = {{
    std::io::file::text_with {direct}: \\text0 ->
        my $text = text0
        my before = $text
        &text = before + \" direct\"
        ((before, $text), $text)
}}

my direct_after = std::io::file::read_text {direct}

my scoped_result = std::io::file::text_with {scoped}: \\text0 ->
    my $text = text0
    my before = $text
    &text = before + \" scoped\"
    ((before, $text), $text)

my scoped_after = std::io::file::read_text {scoped}

(direct_result, direct_after, scoped_result, scoped_after)
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
        "run roots [((\"hello\", \"hello direct\"), \"hello direct\", (\"hi\", \"hi scoped\"), \"hi scoped\")]\n"
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
    let scoped = root.join("scoped.txt");
    let entry = root.join("main.yu");
    fs::write(&scoped, "hi").unwrap();
    fs::write(
        &entry,
        format!(
            "\
my scoped_result = {{
    my &txt = std::io::file::text_with({scoped}, do)
    my before = $txt
    &txt = before + \" scoped\"
    my buffer = $txt
    my backing_during_scope = std::io::file::read_text {scoped}
    (before, buffer, backing_during_scope)
}}

my scoped_after = std::io::file::read_text {scoped}

(scoped_result, scoped_after)
",
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
        "run roots [((\"hi\", \"hi scoped\", \"hi\"), \"hi scoped\")]\n"
    );
    assert_eq!(fs::read_to_string(&scoped).unwrap(), "hi scoped");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_std_file_unsupported_host_reports_capability_error() {
    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("run")
        .arg("--host")
        .arg("unsupported")
        .arg("--print-roots")
        .arg("-e")
        .arg("std::io::file::exists \"/tmp/yulang-unsupported-host\"")
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
        stderr.contains("runtime error [yulang.unsupported-host-capability]:"),
        "{stderr}"
    );
    assert!(
        stderr.contains("host capability std::io::file::file is not available"),
        "{stderr}"
    );
    assert!(
        stderr.contains(
            "hint: use a host that grants this capability or handle the capability with a mock effect handler"
        ),
        "{stderr}"
    );
    assert!(!stderr.contains("run roots [false]"), "{stderr}");
}

#[test]
fn compatible_run_custom_host_act_without_registration_reports_capability_error() {
    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("run")
        .arg("--print-roots")
        .arg("-e")
        .arg("pub host act stop:\n  our now: () -> int\n\nstop::now()\n")
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
        stderr.contains("runtime error [yulang.unsupported-host-capability]:"),
        "{stderr}"
    );
    assert!(
        stderr.contains("host capability stop is not available"),
        "{stderr}"
    );
    assert!(
        stderr.contains(
            "hint: use a host that grants this capability or handle the capability with a mock effect handler"
        ),
        "{stderr}"
    );
    assert!(
        !stderr.contains("runtime error [yulang.unhandled-effect]"),
        "{stderr}"
    );
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
fn compatible_run_native_tcp_server_echoes_two_connections() {
    if !localhost_tcp_bind_available() {
        eprintln!("skipping native TCP server echo test: localhost bind is not available");
        return;
    }

    let entry = write_entry(
        "run-native-tcp-server-echo",
        "\
{
    my listener = net::listen 0
    say listener.port
    my req = listener.accept()
    req.respond req.payload
}
",
    );

    let mut child = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("run")
        .arg("--host")
        .arg("native")
        .arg(&entry)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();

    let (port_rx, stdout_reader) =
        read_first_child_stdout_line(child.stdout.take().expect("child stdout should be piped"));
    let stderr_reader =
        read_child_pipe_to_string(child.stderr.take().expect("child stderr should be piped"));

    let port_line = match port_rx.recv_timeout(Duration::from_secs(10)) {
        Ok(line) => line,
        Err(error) => {
            kill_child(&mut child);
            let stdout_text = stdout_reader.join().unwrap();
            let stderr_text = stderr_reader.join().unwrap();
            panic!(
                "native tcp server did not print a port before timeout: {error}\nstdout:\n{stdout_text}\nstderr:\n{stderr_text}"
            );
        }
    };
    let port = port_line.trim().parse::<u16>().unwrap_or_else(|error| {
        panic!("native tcp server printed invalid port {port_line:?}: {error}")
    });

    assert_native_tcp_echo(port, b"alpha");
    assert_native_tcp_echo(port, b"second");

    kill_child(&mut child);
    let stdout_text = stdout_reader.join().unwrap();
    let stderr_text = stderr_reader.join().unwrap();
    assert!(
        stdout_text.starts_with(&port_line),
        "stdout reader should retain the port line:\n{stdout_text}"
    );
    assert_eq!(stderr_text, "");
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
            .contains("hint: try the interpreter oracle or reduce this source to a smaller report"),
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
fn compatible_run_rejects_syntax_diagnostics_before_execution() {
    let entry = repo_yulang_fixture("regressions/diagnostics/run_invalid_ref_assignment_syntax.yu");

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
    let stdout = stdout(&output);
    assert!(
        stdout.contains("diagnostics:\n  error [yulang.syntax]: syntax error: unexpected token\n"),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "    --> line 6, column 1\n    6 | &(&doc.lines.each) = \"done: fixed\"\n      | ^\n"
        ),
        "{stdout}"
    );
    assert!(!stdout.contains("run roots"), "{stdout}");
    assert_eq!(stderr(&output), "");
}

#[test]
fn public_diagnostics_check_reports_missing_local_binding_body() {
    let entry = write_entry("diagnostics-missing-local-binding-body", "my x =\n");

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
        stdout.contains(
            "  error [yulang.missing-local-binding-body]: x: binding `x` is missing a body expression\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains("    hint: write a body expression after `=`\n"),
        "{stdout}"
    );
    assert!(
        stdout.contains("    --> line 1, column 4\n    1 | my x =\n      |    ^\n"),
        "{stdout}"
    );
    assert!(stdout.contains("check-poly\n"), "{stdout}");
    assert!(stdout.contains("lowering errors:\n"), "{stdout}");
    assert!(
        stdout.contains("  x: binding `x` is missing a body expression\n"),
        "{stdout}"
    );
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
fn compatible_build_writes_control_ir_artifact() {
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
        artifact_source.starts_with("YULANG-CONTROL-IR 1\n"),
        "{artifact_source}"
    );
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
fn compatible_dump_control_evidence_memoizes_repeated_known_callees() {
    let entry = write_entry(
        "dump-control-evidence-cache-stats",
        "my id x = x\n(id 1, id 2, id 3)\n",
    );

    let output = yulang_command()
        .env("YULANG_CONTROL_EVIDENCE_CACHE_STATS", "1")
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("dump")
        .arg("--control-evidence")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stderr = stderr(&output);
    assert!(stderr.contains("control_evidence_cache_stats:"), "{stderr}");
    assert_cache_stat_has_hits(&stderr, "instance_entry");
    assert_cache_stat_has_hits(&stderr, "known_callee");
}

fn assert_cache_stat_has_hits(stderr: &str, label: &str) {
    let line = stderr
        .lines()
        .find(|line| line.trim_start().starts_with(label))
        .unwrap_or_else(|| panic!("missing {label} cache stats line:\n{stderr}"));
    let hits = line
        .split_whitespace()
        .find_map(|part| part.strip_prefix("hits="))
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or_else(|| panic!("missing hits count in {label} cache stats line: {line}"));
    assert!(
        hits > 0,
        "{label} cache should hit repeated known-callee walks:\n{stderr}"
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
        stdout.contains("static_route "),
        "operation evidence objects should show static route classification:\n{stdout}"
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
fn debug_evidence_vm_plan_prints_host_escape_static_route() {
    let entry = write_entry(
        "debug-evidence-vm-plan-host-escape-static-route",
        "pub host act stop:\n  our now: () -> int\n\nstop::now()\n",
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
        stdout.contains(
            "static_route_dynamic: open_row 0 multiple_candidates 0 hygiene_barrier 0 provider_env 0 delayed_boundary 0 host_escape 1 unclassified 0"
        ),
        "host escape should be counted in the static route summary:\n{stdout}"
    );
    assert!(
        stdout.contains("static_route dynamic-host-escape"),
        "operation evidence objects should expose host escape routes:\n{stdout}"
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
fn debug_runtime_evidence_run_matches_control_ir_on_pure_lambda_subset() {
    let entry = write_entry("debug-runtime-evidence-run", "my id x = x\nid 3\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("runtime evidence run:"), "{stdout}");
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
    assert!(stdout.contains("evidence.tasks: 2"), "{stdout}");
    assert!(stdout.contains("run roots [3]\n"), "{stdout}");
}

#[test]
fn debug_evidence_vm_run_alias_matches_control_ir_on_pure_lambda_subset() {
    let entry = write_entry("debug-evidence-vm-run", "my id x = x\nid 3\n");

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("evidence-vm-run")
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("runtime evidence run:"), "{stdout}");
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
    assert!(stdout.contains("run roots [3]\n"), "{stdout}");
}

#[test]
fn debug_host_act_manifest_prints_runtime_registry_view() {
    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("debug")
        .arg("host-act-manifest")
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.starts_with("compiler host manifest:\n"), "{stdout}");
    let hash_line = stdout
        .lines()
        .nth(1)
        .expect("debug manifest should print a manifest hash line");
    let hash = hash_line
        .strip_prefix("  hash=")
        .expect("debug manifest should expose hash= on the second line");
    assert!(
        hash.len() == 16 && hash.bytes().all(|byte| byte.is_ascii_hexdigit()),
        "debug manifest hash should be fixed-width hex: {hash_line:?}"
    );
    assert_eq!(
        stdout.matches(" surface=contract column=").count(),
        12,
        "debug manifest should expose console, file protocol/ambient, net/server, listener port, and clock ops as contract surface:\n{stdout}"
    );
    assert_eq!(
        stdout.matches(" surface=raw-compat column=").count(),
        2,
        "debug manifest should keep only provisional range file ops isolated as raw-compat:\n{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.io.console.out op=write tier=sync path=std.io.console.out.write sig=std::text::str::str -> [std::io::console::out] () surface=contract column=0 symbol=yu_host_3std2io7console3out_5write\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.time.clock op=now tier=sync path=std.time.clock.now sig=() -> [std::time::clock] std::time::instant surface=contract column=13 symbol=yu_host_3std4time5clock_3now\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout
            .contains("  act=std.io.file.file op=load tier=sync path=std.io.file.file.load sig=std::text::path::path -> [std::io::file::file] std::data::result::result std::text::str::str std::io::file::io_err surface=contract column=4 symbol=yu_host_3std2io4file4file_4load\n"),
        "{stdout}"
    );
    assert!(
        stdout
            .contains("  act=std.io.file.file op=store tier=sync path=std.io.file.file.store sig=(std::text::path::path, std::text::str::str) -> [std::io::file::file] std::data::result::result () std::io::file::io_err surface=contract column=7 symbol=yu_host_3std2io4file4file_5store\n"),
        "{stdout}"
    );
    assert!(
        stdout
            .contains("  act=std.io.file.file op=meta tier=sync path=std.io.file.file.meta sig=std::text::path::path -> [std::io::file::file] std::io::file::file_meta surface=contract column=5 symbol=yu_host_3std2io4file4file_4meta\n"),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.io.file.file op=read_at tier=sync path=std.io.file.file.read_at sig=(std::text::path::path, std::data::range::range) -> [std::io::file::file] std::data::result::result (std::text::str::str, std::data::range::range) std::io::file::io_err surface=raw-compat column=6 symbol=yu_host_3std2io4file4file_7read_at\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.io.file.file op=write_at tier=sync path=std.io.file.file.write_at sig=(std::text::path::path, std::data::range::range, std::text::str::str) -> [std::io::file::file] std::data::result::result () std::io::file::io_err surface=raw-compat column=8 symbol=yu_host_3std2io4file4file_8write_at\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.io.file.file op=ambient_touch tier=sync path=std.io.file.file.ambient_touch sig=std::text::path::path -> [std::io::file::file] std::data::result::result () std::io::file::io_err surface=contract column=3 symbol=yu_host_3std2io4file4file_13ambient_touch\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.io.file.file op=ambient_get tier=sync path=std.io.file.file.ambient_get sig=std::text::path::path -> [std::io::file::file] std::text::str::str surface=contract column=1 symbol=yu_host_3std2io4file4file_11ambient_get\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.io.file.file op=ambient_set tier=sync path=std.io.file.file.ambient_set sig=(std::text::path::path, std::text::str::str) -> [std::io::file::file] () surface=contract column=2 symbol=yu_host_3std2io4file4file_11ambient_set\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.io.net.net op=listen tier=sync path=std.io.net.net.listen sig=int -> [std::io::net::net] std::data::result::result std::io::net::listener std::io::net::net_err surface=contract column=9 symbol=yu_host_3std2io3net3net_6listen\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.io.net.net op=port tier=sync path=std.io.net.net.port sig=std::io::net::listener -> [std::io::net::net] int surface=contract column=10 symbol=yu_host_3std2io3net3net_4port\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.io.net.server op=accept tier=suspend-multi-shot path=std.io.net.server.accept sig=std::io::net::listener -> [std::io::net::server] std::io::net::request surface=contract column=11 symbol=yu_host_3std2io3net6server_6accept\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "  act=std.io.net.server op=respond tier=sync path=std.io.net.server.respond sig=(std::io::net::respond_slot, std::text::bytes::bytes) -> [std::io::net::server] std::data::result::result () std::io::net::net_err surface=contract column=12 symbol=yu_host_3std2io3net6server_7respond\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "runtime host tiers:\n  tier=sync\n  tier=suspend-one-shot\n  tier=suspend-multi-shot\n"
        ),
        "{stdout}"
    );
}

#[test]
fn compiler_generated_host_manifest_reaches_runtime_evidence_surface() {
    let root = temp_root("compiler-host-manifest-stage1");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let entry = root.join("main.yu");
    fs::write(&entry, "1\n").unwrap();

    let files = yulang::collect_local_sources_with_std_options(
        &entry,
        &yulang::StdSourceOptions {
            std_root: Some(repo_lib_root()),
        },
    )
    .unwrap();
    let output = yulang::build_poly_and_compiled_unit_from_collected_sources(files).unwrap();
    let manifest = infer::host_acts::host_act_manifest_from_compiled(
        &output.compiled_unit.namespace,
        &output.compiled_unit.lowering,
        &output.compiled_unit.typed,
    )
    .unwrap();
    let control = yulang::build_control_from_poly_output(&output.poly).unwrap();
    assert_eq!(
        control.runtime_evidence.host_manifest.as_ref(),
        Some(&manifest)
    );

    let operation_keys = manifest
        .operations
        .iter()
        .map(|op| {
            (
                op.act_id.as_str(),
                op.operation_id.as_str(),
                op.path.join("."),
            )
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        operation_keys,
        BTreeSet::from([
            (
                "std.io.console.out",
                "write",
                "std.io.console.out.write".to_string()
            ),
            (
                "std.io.file.file",
                "ambient_get",
                "std.io.file.file.ambient_get".to_string()
            ),
            (
                "std.io.file.file",
                "ambient_set",
                "std.io.file.file.ambient_set".to_string()
            ),
            (
                "std.io.file.file",
                "ambient_touch",
                "std.io.file.file.ambient_touch".to_string()
            ),
            (
                "std.io.file.file",
                "load",
                "std.io.file.file.load".to_string()
            ),
            (
                "std.io.file.file",
                "meta",
                "std.io.file.file.meta".to_string()
            ),
            (
                "std.io.file.file",
                "read_at",
                "std.io.file.file.read_at".to_string()
            ),
            (
                "std.io.file.file",
                "store",
                "std.io.file.file.store".to_string()
            ),
            (
                "std.io.file.file",
                "write_at",
                "std.io.file.file.write_at".to_string()
            ),
            (
                "std.io.net.net",
                "listen",
                "std.io.net.net.listen".to_string()
            ),
            ("std.io.net.net", "port", "std.io.net.net.port".to_string()),
            (
                "std.io.net.server",
                "accept",
                "std.io.net.server.accept".to_string()
            ),
            (
                "std.io.net.server",
                "respond",
                "std.io.net.server.respond".to_string()
            ),
            ("std.time.clock", "now", "std.time.clock.now".to_string()),
        ])
    );

    let raw_compat_paths = manifest
        .operations
        .iter()
        .filter(|op| op.surface == poly::host_manifest::HostOperationSurface::RawCompat)
        .map(|op| op.path.join("."))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        raw_compat_paths,
        BTreeSet::from([
            "std.io.file.file.read_at".to_string(),
            "std.io.file.file.write_at".to_string(),
        ])
    );
    let tiers = manifest
        .operations
        .iter()
        .map(|op| (op.path.join("."), op.tier))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        tiers.get("std.io.net.server.accept"),
        Some(&poly::host_manifest::HostOperationTier::SuspendMultiShot)
    );
    assert!(
        tiers
            .iter()
            .filter(|(path, _)| path.as_str() != "std.io.net.server.accept")
            .all(|(_, tier)| *tier == poly::host_manifest::HostOperationTier::Sync)
    );

    let _ = fs::remove_dir_all(&root);
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
        .arg("--compare-mono")
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
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
fn debug_runtime_evidence_run_matches_control_ir_on_std_int_primitives() {
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
    assert!(stdout.contains("run roots [25]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_matches_control_ir_on_record_pattern_defaults() {
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
    assert!(stdout.contains("run roots [[3, 2, 1]]\n"), "{stdout}");
}

#[test]
fn debug_runtime_evidence_run_matches_control_ir_on_text_and_bytes_primitives() {
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
    assert!(stdout.contains("run roots [(11, 21)]\n"), "{stdout}");
    assert!(
        stdout.contains("runtime_evidence.known_state_direct_gets: 6"),
        "compiler local refs should use direct state get handling:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_direct_sets: 2"),
        "compiler local refs should use direct state set handling:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_entries: 2"),
        "known state catch should push a runtime state frame:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_state_frame_exits: 2"),
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
        stdout.contains("evidence.plan_known_operation_state_get_candidates: 4"),
        "known operation plan should classify the four static get call sites:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_set_candidates: 2"),
        "known operation plan should classify the two static set call sites:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_state_operation_route_proofs: 6"),
        "known operation plan should build plan-only route proofs for local refs:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_direct_gets: 4"),
        "D3 should enable direct get for the four static local ref get sites:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_state_direct_sets: 2"),
        "D4 should enable direct set for the two static local ref set sites:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence.plan_known_operation_reject_direct_execution_disabled: 0"),
        "D4 should not leave route-proven local refs on the disabled direct path:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_get_candidate_hits: 6"),
        "known operation runtime hits should count forced get requests:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_set_candidate_hits: 2"),
        "known operation runtime hits should count forced set requests:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_get_active_frame_hits: 6"),
        "known get operations should see the active state frame at force time:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_state_set_active_frame_hits: 2"),
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
        stdout.contains("runtime_evidence.known_operation_route_shadow_hits: 8"),
        "route proof shadow guard should hit for every dynamic local ref operation:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_get_hits: 6"),
        "route proof shadow guard should count dynamic local ref gets:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_shadow_set_hits: 2"),
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
        stdout.contains("runtime_evidence.known_operation_route_direct_get_attempts: 6"),
        "route proof direct get guard should run for every dynamic local ref get:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_get_hits: 6"),
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
        stdout.contains("runtime_evidence.known_operation_route_direct_set_attempts: 2"),
        "route proof direct set guard should run for every dynamic local ref set:\n{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.known_operation_route_direct_set_hits: 2"),
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
fn debug_runtime_evidence_run_handles_marked_force_tail_reentry() {
    let cases = [
        (
            "debug-runtime-evidence-run-marked-force-for-ref",
            "use std::control::var::*\n\n\
             {\n\
             \x20 my $sum = 0\n\
             \x20 for i in 0..<64:\n\
             \x20\x20 &sum = $sum + i\n\
             \x20 $sum\n\
             }\n",
            "run roots [2016]\n",
        ),
        (
            "debug-runtime-evidence-run-marked-force-fold-ref",
            "use std::control::var::*\n\n\
             {\n\
             \x20 my $sum = 0\n\
             \x20 (0..<64).fold (): \\_ i ->\n\
             \x20\x20 &sum = $sum + i\n\
             \x20 $sum\n\
             }\n",
            "run roots [2016]\n",
        ),
        (
            "debug-runtime-evidence-run-marked-force-for-no-ref",
            "{\n\
             \x20 for i in 0..<64:\n\
             \x20\x20 i\n\
             \x20 ()\n\
             }\n",
            "run roots [()]\n",
        ),
    ];

    // mono-runtime still overflows the stack on these marked-force stress cases.
    // Keep the evidence-vm regression assertions here until mono-runtime is trampolined.
    for (name, source, expected_roots) in cases {
        let entry = write_entry(name, source);
        let output = yulang_command()
            .arg("--std-root")
            .arg(repo_lib_root())
            .arg("--no-cache")
            .arg("debug")
            .arg("runtime-evidence-run")
            .arg(&entry)
            .output()
            .unwrap();

        assert_success(&output);
        let stdout = stdout(&output);
        assert!(stdout.contains(expected_roots), "{stdout}");
    }

    let adversarial =
        repo_yulang_fixture("regressions/runtime/marked_force_nondet_materialized_tail_reentry.yu");
    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg(&adversarial)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("run roots [()]\n"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
fn debug_runtime_evidence_run_classifies_thunk_argument_as_delayed_boundary() {
    let entry = write_entry(
        "debug-runtime-evidence-run-delayed-boundary",
        "act stop:\n  our now: () -> int\n\n\
         my action() = stop::now()\n\n\
         my run(x: [_] int): int = catch x:\n\
         \x20 stop::now(), _ -> 1\n\
         \x20 v -> v\n\n\
         run action()\n",
    );

    let output = yulang_command()
        .arg("--no-prelude")
        .arg("--no-cache")
        .arg("debug")
        .arg("runtime-evidence-run")
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
    assert!(
        stdout.contains("evidence.static_route_sites_total: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.static_route_dynamic_delayed_boundary: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("evidence.static_route_dynamic_unclassified: 0"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.static_route_runtime_hits_dynamic_delayed_boundary: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("runtime_evidence.static_route_runtime_hits_dynamic_unclassified: 0"),
        "{stdout}"
    );
    assert!(stdout.contains("run roots [1]\n"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
        .arg("--compare-mono")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    let stdout = stdout(&output);
    assert!(stdout.contains("compare.mono: match"), "{stdout}");
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
    assert!(std_root.join("std").join("io").join("net.yu").is_file());
    assert!(std_root.join("std").join("time.yu").is_file());
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn cache_path_and_clear_use_yulang_cache_dir() {
    let root = temp_root("cache");
    let cache_root = root.join("cache-root");
    fs::create_dir_all(&cache_root).unwrap();
    fs::write(cache_root.join("entry"), "cached").unwrap();
    fs::create_dir_all(cache_root.join("artifacts").join("control-ir")).unwrap();
    fs::create_dir_all(cache_root.join("artifacts").join("poly")).unwrap();
    fs::create_dir_all(cache_root.join("artifacts").join("compiled-unit")).unwrap();
    fs::write(
        cache_root
            .join("artifacts")
            .join("control-ir")
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
            "cache: {}\ncontrol-ir: 1\nmono: 0\npoly: 2\ncompiled-unit: 0\nrealm-resolution: 0\n",
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
fn compatible_build_populates_control_ir_cache_unless_disabled() {
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
fn compatible_run_populates_control_ir_cache() {
    let entry = write_entry("run-evidence-cache", "1\n");
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

    remove_cache_stage(&cache_root, "control-ir");
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

    remove_cache_stage(&cache_root, "control-ir");
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
fn compatible_run_with_std_prefix_cache_matches_full_build_for_mock_ref_view() {
    let root = temp_root("run-std-prefix-mock-ref-view");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let cache_root = root.join("cache-root");
    let entry = repo_file("notes/bugs/file_text_with_mock_function_boundary_blocker.yu");

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--host")
        .arg("unsupported")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(
        stdout(&output),
        "run roots [((\"start\", \"start!\"), \"start!\")]\n"
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn compatible_run_with_std_prefix_cache_matches_full_build_for_direct_ref_update() {
    let root = temp_root("run-std-prefix-direct-ref-update");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let cache_root = root.join("cache-root");
    let entry = root.join("main.yu");
    fs::write(
        &entry,
        r#"use std::control::var::*

my update_local_ref(backing) = {
    my $buffer = backing
    my r: std::control::var::ref _ str = ref {
        get: \() -> $buffer,
        update_effect: \() -> &buffer = ref_update::update $buffer
    }
    r.update (\old -> old + "!")
    r.get()
}

update_local_ref "start"
"#,
    )
    .unwrap();

    let output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("--runtime-phase-timings")
        .arg("run")
        .arg("--print-roots")
        .arg(&entry)
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "run roots [\"start!\"]\n");

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

    remove_cache_stage(&cache_root, "control-ir");
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

    remove_cache_stage(&cache_root, "control-ir");
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

    remove_cache_stage(&cache_root, "control-ir");
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
fn public_regression_parser_pattern_rest_runs_without_cache() {
    let entry = repo_yulang_fixture("regressions/runtime/parser_pattern_case.yu");

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
    let stdout = stdout(&output);
    assert!(stdout.contains("\"run:alpha beta\""), "{stdout}");
    assert!(stdout.contains("\"rest-discard:run\""), "{stdout}");
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
    let mut smoke_cases = public_contract_manifest_cli_smoke_cases();
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

        if smoke_cases.remove(case.name.as_str()) {
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
    assert!(
        smoke_cases.is_empty(),
        "missing public contract CLI smoke cases: {smoke_cases:?}"
    );
}

fn public_contract_manifest_cli_smoke_cases() -> BTreeSet<&'static str> {
    [
        "nondet_once_triple",
        "type_annotation_mismatch",
        "std_result_unwrap_or_public_signature",
        "file_text_with_commit_do",
        "file_unsupported_host",
    ]
    .into_iter()
    .collect()
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
fn contract_command_runs_multiple_filtered_cases() {
    let output = yulang_command()
        .arg("--std-root")
        .arg(repo_lib_root())
        .arg("contract")
        .arg("--case")
        .arg("file_text_with_commit")
        .arg("--case")
        .arg("file_text_with_rollback_on_error")
        .arg("--contract")
        .arg("file-resource")
        .arg(repo_yulang_fixture("cases.toml"))
        .output()
        .unwrap();

    assert_success(&output);
    assert_eq!(stdout(&output), "contract cases ok: 2\n");
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
fn contract_command_rejects_file_resource_without_standard_file_tags() {
    let root = temp_root("contract-rejects-file-resource-area-tags");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let manifest = root.join("cases.toml");
    fs::write(
        &manifest,
        r#"
[[case]]
name = "bad_file_resource_area"
file = "support/unused.yu"
kind = "run"
contracts = [
    "runtime",
    "file-resource",
    "resource-lifetime",
    "host.native",
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
        stderr(&output)
            .contains("file-resource contract case `bad_file_resource_area` should carry standard-api and file"),
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
            "file-resource runtime case `bad_file_resource` should carry exactly one native or unsupported host scope"
        ),
        "{}",
        stderr(&output)
    );

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn contract_command_rejects_unsupported_host_with_non_evidence_backend() {
    let root = temp_root("contract-rejects-host-backend-mismatch");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let manifest = root.join("cases.toml");
    fs::write(
        &manifest,
        r#"
[[case]]
name = "bad_host_backend"
file = "support/unused.yu"
kind = "run"
backend = "interpreter"
host = "unsupported"
expect_success = false
expect_stderr_contains = ["runtime error ["]
contracts = [
    "runtime-error",
    "runtime-failure",
    "backend.interpreter",
    "host.unsupported",
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
            "contract case `bad_host_backend` should only combine non-native host mode with backend = \"evidence-vm\""
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
        "Server Resource Contract",
        "Yulang Contract v0",
        "stable-core",
        "std::data::result",
        "std::text::path",
        "std::io::file",
        "std::io::net",
    ] {
        assert!(
            status.contains(claim),
            "docs/status.md should keep Public Contract Spine claim {claim:?}"
        );
    }

    let cases = public_contract_manifest_cases();
    for requirement in [
        ManifestTagRequirement::new("public signatures", &["public-signature"]),
        ManifestTagRequirement::new("stable core", &["stable-core"]),
        ManifestTagRequirement::new("stable core runtime", &["stable-core", "runtime"]),
        ManifestTagRequirement::new("stable core diagnostics", &["stable-core", "diagnostics"]),
        ManifestTagRequirement::new(
            "stable core public signatures",
            &["stable-core", "public-signature"],
        ),
        ManifestTagRequirement::new(
            "stable core public examples",
            &["stable-core", "public-example"],
        ),
        ManifestTagRequirement::new("runtime behavior", &["runtime"]),
        ManifestTagRequirement::new("public examples", &["public-example"]),
        ManifestTagRequirement::new("runtime error behavior", &["runtime-error"]),
        ManifestTagRequirement::new("diagnostics", &["diagnostics"]),
        ManifestTagRequirement::new("runtime diagnostics", &["diagnostics", "runtime-failure"]),
        ManifestTagRequirement::new(
            "runtime call diagnostics",
            &["diagnostics", "runtime-failure", "calls"],
        ),
        ManifestTagRequirement::new(
            "runtime effect diagnostics",
            &["diagnostics", "runtime-failure", "effects"],
        ),
        ManifestTagRequirement::new(
            "runtime pattern diagnostics",
            &["diagnostics", "runtime-failure", "patterns"],
        ),
        ManifestTagRequirement::new(
            "unsupported host diagnostics",
            &["diagnostics", "runtime-failure", "host.unsupported"],
        ),
        ManifestTagRequirement::new(
            "time unsupported host diagnostics",
            &["diagnostics", "host.unsupported", "time"],
        ),
        ManifestTagRequirement::new(
            "file unsupported host diagnostics",
            &["diagnostics", "host.unsupported", "file-resource"],
        ),
        ManifestTagRequirement::new(
            "console unsupported host diagnostics",
            &["diagnostics", "host.unsupported", "console"],
        ),
        ManifestTagRequirement::new("diagnostics syntax", &["diagnostics", "syntax"]),
        ManifestTagRequirement::new("diagnostics names", &["diagnostics", "names"]),
        ManifestTagRequirement::new("diagnostics typechecker", &["diagnostics", "typechecker"]),
        ManifestTagRequirement::new(
            "diagnostics related ranges",
            &["diagnostics", "related-ranges"],
        ),
        ManifestTagRequirement::new("diagnostics roles", &["diagnostics", "roles"]),
        ManifestTagRequirement::new("standard API", &["standard-api"]),
        ManifestTagRequirement::new("stable standard API", &["standard-api", "stable-api"]),
        ManifestTagRequirement::new(
            "stable core standard API",
            &["stable-core", "standard-api", "stable-api"],
        ),
        ManifestTagRequirement::new(
            "standard API migration canary",
            &["standard-api", "migration-canary"],
        ),
        ManifestTagRequirement::new("result API", &["standard-api", "result"]),
        ManifestTagRequirement::new("error API", &["standard-api", "errors"]),
        ManifestTagRequirement::new("path API", &["standard-api", "path"]),
        ManifestTagRequirement::new("config API", &["standard-api", "config"]),
        ManifestTagRequirement::new(
            "native file API host scope",
            &["standard-api", "file", "host.native"],
        ),
        ManifestTagRequirement::new("time API", &["standard-api", "time"]),
        ManifestTagRequirement::new(
            "time host act native scope",
            &["time", "host-act", "host.native"],
        ),
        ManifestTagRequirement::new(
            "time host act unsupported scope",
            &["time", "host-act", "host.unsupported"],
        ),
        ManifestTagRequirement::new(
            "time host act mock scope",
            &["time", "host-act", "mock-host"],
        ),
        ManifestTagRequirement::new("host act contract", &["host-act"]),
        ManifestTagRequirement::new("server resource", &["server-resource"]),
        ManifestTagRequirement::new(
            "server resource mock host",
            &["server-resource", "host.mock-server"],
        ),
        ManifestTagRequirement::new(
            "server resource typed failure",
            &["server-resource", "typed-failure"],
        ),
        ManifestTagRequirement::new(
            "server resource public signatures",
            &["server-resource", "public-signature"],
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

#[test]
fn public_contract_manifest_covers_contract_v1_server_evidence_claims() {
    let evidence_path = repo_file("docs/language/contract-v1-server-evidence.md");
    let evidence = fs::read_to_string(&evidence_path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", evidence_path.display()));
    for claim in [
        "server-resource",
        "mock-server first slice",
        "server_double_respond_typed_failure",
        "std_io_net_serve_public_signature",
    ] {
        assert!(
            evidence.contains(claim),
            "contract-v1-server-evidence.md should keep evidence claim {claim:?}"
        );
    }

    let cases = public_contract_manifest_cases();
    for requirement in [
        ManifestTagRequirement::new("server resource", &["server-resource"]),
        ManifestTagRequirement::new(
            "server resource mock host",
            &["server-resource", "host.mock-server"],
        ),
        ManifestTagRequirement::new(
            "server resource typed failure",
            &["server-resource", "typed-failure"],
        ),
        ManifestTagRequirement::new(
            "server resource public signatures",
            &["server-resource", "public-signature"],
        ),
    ] {
        assert!(
            contract_manifest_has_case_with_tags(&cases, requirement.tags),
            "contract-v1-server-evidence.md claims {}, but tests/yulang/cases.toml has no case tagged {:?}",
            requirement.label,
            requirement.tags
        );
    }
}

#[test]
fn public_contract_manifest_covers_contract_v1_config_evidence_claims() {
    let evidence_path = repo_file("docs/language/contract-v1-config-evidence.md");
    let evidence = fs::read_to_string(&evidence_path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", evidence_path.display()));
    for claim in [
        "std::text::config",
        "config_parse_basic",
        "config_missing_lookup",
        "config_load_native",
        "c.sections",
    ] {
        assert!(
            evidence.contains(claim),
            "contract-v1-config-evidence.md should keep evidence claim {claim:?}"
        );
    }

    let cases = public_contract_manifest_cases();
    for requirement in [
        ManifestTagRequirement::new("config API", &["standard-api", "config"]),
        ManifestTagRequirement::new("config preview", &["config", "preview"]),
        ManifestTagRequirement::new("config native load", &["config", "file", "host.native"]),
    ] {
        assert!(
            contract_manifest_has_case_with_tags(&cases, requirement.tags),
            "contract-v1-config-evidence.md claims {}, but tests/yulang/cases.toml has no case tagged {:?}",
            requirement.label,
            requirement.tags
        );
    }
}

#[test]
fn public_contract_manifest_covers_contract_v1_file_evidence_claims() {
    let evidence_path = repo_file("docs/language/contract-v1-file-evidence.md");
    let evidence = fs::read_to_string(&evidence_path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", evidence_path.display()));
    for claim in [
        "file-resource",
        "protocol-sugar",
        "lambda_my_binder_state_protocol",
        "do_binding_state_protocol",
        "raw-compat",
        "typed-failure",
    ] {
        assert!(
            evidence.contains(claim),
            "contract-v1-file-evidence.md should keep evidence claim {claim:?}"
        );
    }

    let cases = public_contract_manifest_cases();
    for requirement in [
        ManifestTagRequirement::new("file resource", &["file-resource"]),
        ManifestTagRequirement::new(
            "file lambda protocol sugar",
            &["file-resource", "protocol-sugar", "lambda-my"],
        ),
        ManifestTagRequirement::new(
            "file do-binding protocol sugar",
            &["file-resource", "protocol-sugar", "do-binding"],
        ),
        ManifestTagRequirement::new(
            "pure lambda protocol sugar",
            &["runtime", "refs", "protocol-sugar", "lambda-my"],
        ),
        ManifestTagRequirement::new(
            "pure do-binding protocol sugar",
            &["runtime", "refs", "protocol-sugar", "do-binding"],
        ),
        ManifestTagRequirement::new("file raw compat", &["file-resource", "raw-compat"]),
        ManifestTagRequirement::new("file typed failure", &["file-resource", "typed-failure"]),
    ] {
        assert!(
            contract_manifest_has_case_with_tags(&cases, requirement.tags),
            "contract-v1-file-evidence.md claims {}, but tests/yulang/cases.toml has no case tagged {:?}",
            requirement.label,
            requirement.tags
        );
    }
}

struct ManifestTagRequirement<'a> {
    label: &'a str,
    tags: &'a [&'a str],
}

impl<'a> ManifestTagRequirement<'a> {
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
            | "backend.evidence-vm"
            | "backend.interpreter"
            | "bindings"
            | "bundled-std"
            | "callback-residual"
            | "calls"
            | "casts"
            | "compile-error"
            | "config"
            | "console"
            | "data-position-effect"
            | "deep-handler"
            | "defaults"
            | "diagnostics"
            | "display"
            | "do-binding"
            | "effect-hygiene"
            | "effects"
            | "errors"
            | "file"
            | "file-resource"
            | "filesystem"
            | "from"
            | "handler-syntax"
            | "host-act"
            | "host.mock-server"
            | "host.native"
            | "host.unsupported"
            | "junction"
            | "lambda-my"
            | "lists"
            | "metadata"
            | "migration-canary"
            | "mock-host"
            | "names"
            | "network"
            | "parser-dsl"
            | "path"
            | "patterns"
            | "preview"
            | "protocol-sugar"
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
            | "server"
            | "server-resource"
            | "showcase"
            | "stable-core"
            | "stable-api"
            | "standard-api"
            | "str"
            | "std.flow"
            | "std.nondet"
            | "std.parse"
            | "std.ref"
            | "sub-return"
            | "syntax"
            | "time"
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
    let backend = case.backend.as_deref().unwrap_or("evidence-vm");
    assert!(
        matches!(backend, "evidence-vm" | "interpreter"),
        "contract manifest case {} has unsupported backend mode {backend:?}",
        case.name
    );
    if backend != "evidence-vm" {
        assert_eq!(
            case.kind, "run",
            "contract manifest case {} should only set backend mode on run cases",
            case.name
        );
    }
    if case.host.as_deref().unwrap_or("native") != "native" && backend != "evidence-vm" {
        panic!(
            "contract manifest case {} should only combine non-native host mode with backend = \"evidence-vm\"",
            case.name
        );
    }
    for (tag, expected) in [
        ("backend.evidence-vm", "evidence-vm"),
        ("backend.interpreter", "interpreter"),
    ] {
        if contract_manifest_case_has_tag(case, tag) {
            assert_eq!(
                backend, expected,
                "contract manifest case {} uses {tag} with backend {:?}",
                case.name, case.backend
            );
        }
    }
    if backend == "interpreter" {
        assert!(
            contract_manifest_case_has_tag(case, "backend.interpreter"),
            "interpreter contract manifest case {} should carry backend.interpreter",
            case.name
        );
    }

    let host = case.host.as_deref().unwrap_or("native");
    assert!(
        matches!(host, "native" | "unsupported" | "mock-server"),
        "contract manifest case {} has unsupported host mode {host:?}",
        case.name
    );
    if host != "native" {
        assert_eq!(
            case.kind, "run",
            "contract manifest case {} should only set host mode on run cases",
            case.name
        );
    }
    if host == "unsupported" {
        assert!(
            contract_manifest_case_has_tag(case, "host.unsupported"),
            "unsupported-host contract manifest case {} should carry host.unsupported",
            case.name
        );
    }
    if contract_manifest_case_has_tag(case, "host.unsupported") {
        assert_eq!(
            host, "unsupported",
            "host.unsupported contract manifest case {} should set host = \"unsupported\"",
            case.name
        );
    }
    if host == "mock-server" {
        assert!(
            contract_manifest_case_has_tag(case, "host.mock-server"),
            "mock-server contract manifest case {} should carry host.mock-server",
            case.name
        );
    }
    if contract_manifest_case_has_tag(case, "host.mock-server") {
        assert_eq!(
            host, "mock-server",
            "host.mock-server contract manifest case {} should set host = \"mock-server\"",
            case.name
        );
    }

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
            contract_manifest_case_has_any_tag(
                case,
                &[
                    "result", "errors", "path", "time", "file", "str", "config", "network",
                ]
            ),
            "standard-api contract manifest case {} should include a narrower API area tag",
            case.name
        );
        if contract_manifest_case_has_tag(case, "file") {
            assert!(
                contract_manifest_case_has_any_tag(
                    case,
                    &["host.native", "host.unsupported", "mock-host"]
                ),
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
                !(temp_file.missing && temp_file.directory),
                "temp file placeholder {:?} in contract manifest case {} should not be both missing and directory",
                temp_file.placeholder,
                case.name
            );
            if temp_file.missing {
                assert!(
                    temp_file.contents.is_none() && temp_file.expect_contents.is_none(),
                    "missing temp file placeholder {:?} in contract manifest case {} should not set contents or expect_contents",
                    temp_file.placeholder,
                    case.name
                );
            } else if temp_file.directory {
                assert!(
                    temp_file.contents.is_none() && temp_file.expect_contents.is_none(),
                    "directory temp placeholder {:?} in contract manifest case {} should not set contents or expect_contents",
                    temp_file.placeholder,
                    case.name
                );
            } else {
                assert!(
                    temp_file.contents.is_some(),
                    "temp file placeholder {:?} in contract manifest case {} should set contents, missing = true, or directory = true",
                    temp_file.placeholder,
                    case.name
                );
            }
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
        assert!(
            contract_manifest_case_has_tag(case, "standard-api")
                && contract_manifest_case_has_tag(case, "file"),
            "file-resource contract manifest case {} should carry standard-api and file",
            case.name
        );
        if case.kind == "run" {
            let has_mock_host = contract_manifest_case_has_tag(case, "mock-host");
            let has_native_host = contract_manifest_case_has_tag(case, "host.native");
            let has_unsupported_host = contract_manifest_case_has_tag(case, "host.unsupported");
            if has_mock_host {
                assert!(
                    !has_native_host,
                    "file-resource mock-host runtime case {} should not also carry host.native",
                    case.name
                );
                assert!(
                    has_unsupported_host,
                    "file-resource mock-host runtime case {} should also run with host.unsupported",
                    case.name
                );
            } else {
                assert_eq!(
                    [has_native_host, has_unsupported_host]
                        .into_iter()
                        .filter(|present| *present)
                        .count(),
                    1,
                    "file-resource runtime case {} should declare exactly one native or unsupported host scope",
                    case.name
                );
            }
            if !has_unsupported_host {
                assert!(
                    contract_manifest_case_has_any_tag(
                        case,
                        &["resource-lifetime", "metadata", "host-act"],
                    ),
                    "file-resource runtime case {} should declare resource-lifetime, metadata, or host-act",
                    case.name
                );
            }
            if has_mock_host {
                assert!(
                    contract_manifest_case_has_any_tag(case, &["host-act", "resource-lifetime"]),
                    "file-resource mock-host runtime case {} should declare host-act or resource-lifetime",
                    case.name
                );
            }
        }
        let is_raw_compat = contract_manifest_case_has_tag(case, "raw-compat");
        let is_stable_api = contract_manifest_case_has_tag(case, "stable-api");
        let is_migration_canary = contract_manifest_case_has_tag(case, "migration-canary");
        if is_raw_compat {
            assert!(
                is_migration_canary && !is_stable_api,
                "file-resource raw-compat case {} should remain migration-canary",
                case.name
            );
        } else {
            assert!(
                is_stable_api && !is_migration_canary,
                "file-resource protocol-center case {} should be stable-api",
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

fn read_first_child_stdout_line(
    stdout: std::process::ChildStdout,
) -> (mpsc::Receiver<String>, thread::JoinHandle<String>) {
    let (tx, rx) = mpsc::channel();
    let handle = thread::spawn(move || {
        let mut reader = BufReader::new(stdout);
        let mut first_line = String::new();
        let read_result = reader.read_line(&mut first_line);
        if read_result.is_ok() {
            let _ = tx.send(first_line.clone());
        } else {
            let _ = tx.send(String::new());
        }
        let mut rest = String::new();
        let _ = reader.read_to_string(&mut rest);
        first_line.push_str(&rest);
        first_line
    });
    (rx, handle)
}

fn read_child_pipe_to_string<R>(mut pipe: R) -> thread::JoinHandle<String>
where
    R: Read + Send + 'static,
{
    thread::spawn(move || {
        let mut text = String::new();
        let _ = pipe.read_to_string(&mut text);
        text
    })
}

fn assert_native_tcp_echo(port: u16, payload: &[u8]) {
    let mut stream = TcpStream::connect(("127.0.0.1", port)).unwrap_or_else(|error| {
        panic!("failed to connect to native tcp server on port {port}: {error}")
    });
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    stream
        .set_write_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    stream.write_all(payload).unwrap();
    stream.shutdown(Shutdown::Write).unwrap();

    let mut response = Vec::new();
    stream.read_to_end(&mut response).unwrap();
    assert_eq!(response, payload);
}

fn localhost_tcp_bind_available() -> bool {
    TcpListener::bind(("127.0.0.1", 0)).is_ok()
}

fn kill_child(child: &mut Child) {
    match child.try_wait() {
        Ok(Some(_)) => {}
        Ok(None) => {
            let _ = child.kill();
            let _ = child.wait();
        }
        Err(_) => {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
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
    temp_files: Vec<PublicContractTempFile>,
    #[serde(default)]
    contracts: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct PublicContractTempFile {
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
    push_contract_backend_args(&mut command, case);
    push_contract_host_args(&mut command, case);
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
        let path = root.join(if temp_file.directory {
            format!("temp-{index}.dir")
        } else {
            format!("temp-{index}.txt")
        });
        if temp_file.directory {
            fs::create_dir_all(&path).unwrap_or_else(|error| {
                panic!(
                    "failed to create temp directory {} for contract case {}: {error}",
                    path.display(),
                    case.name
                )
            });
        } else if let Some(contents) = &temp_file.contents {
            fs::write(&path, contents).unwrap_or_else(|error| {
                panic!(
                    "failed to write temp file {} for contract case {}: {error}",
                    path.display(),
                    case.name
                )
            });
        }
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

fn push_contract_backend_args(command: &mut Command, case: &PublicContractCase) {
    match case.backend.as_deref().unwrap_or("evidence-vm") {
        "evidence-vm" => {}
        "interpreter" => {
            command.arg("--interpreter");
        }
        other => panic!(
            "unsupported backend mode `{other}` in contract case {}",
            case.name
        ),
    }
}

fn push_contract_host_args(command: &mut Command, case: &PublicContractCase) {
    match case.host.as_deref().unwrap_or("native") {
        "native" => {}
        "unsupported" => {
            command.arg("--host").arg("unsupported");
        }
        "mock-server" => {
            command.arg("--host").arg("mock-server");
        }
        other => panic!(
            "unsupported host mode `{other}` in contract case {}",
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
        Some(yulang::SourceDiagnosticRelatedOrigin::ImplCandidate) => "impl-candidate",
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
    artifact_cache_file_count(root, "control-ir")
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
