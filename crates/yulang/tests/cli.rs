use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

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

    let path_output = yulang_command()
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("cache")
        .arg("path")
        .output()
        .unwrap();
    assert_success(&path_output);
    assert_eq!(stdout(&path_output), format!("{}\n", cache_root.display()));

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

    let _ = fs::remove_dir_all(&root);
}

fn yulang_command() -> Command {
    Command::new(env!("CARGO_BIN_EXE_yulang"))
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
    let dir = root.join("artifacts").join("control-vm");
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
