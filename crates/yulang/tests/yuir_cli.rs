use std::{fs, process::Command};

#[test]
fn build_writes_yuir_and_run_loads_it() {
    let source_path = std::env::temp_dir().join(format!(
        "yulang-yuir-cli-{}-{}.yu",
        std::process::id(),
        unique_suffix()
    ));
    let artifact_path = source_path.with_extension("yuir");
    fs::write(&source_path, "1 + 2\n").expect("write test source");

    let build_output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .arg("build")
        .arg("--out")
        .arg(&artifact_path)
        .arg(&source_path)
        .output()
        .expect("run yulang build");
    assert!(
        build_output.status.success(),
        "build failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&build_output.stdout),
        String::from_utf8_lossy(&build_output.stderr)
    );
    assert!(artifact_path.exists());

    let artifact_output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .arg("run")
        .arg("--print-roots")
        .arg(&artifact_path)
        .output()
        .expect("run yulang yuir artifact");
    assert!(
        artifact_output.status.success(),
        "artifact run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&artifact_output.stdout),
        String::from_utf8_lossy(&artifact_output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&artifact_output.stdout), "[0] 3\n");

    let source_output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .arg("run")
        .arg("--print-roots")
        .arg(&source_path)
        .output()
        .expect("run yulang source");
    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_file(&artifact_path);
    assert!(
        source_output.status.success(),
        "source run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&source_output.stdout),
        String::from_utf8_lossy(&source_output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&source_output.stdout), "[0] 3\n");
}

#[test]
fn run_uses_basic_host_output_without_status_line() {
    let source_path = std::env::temp_dir().join(format!(
        "yulang-yuir-cli-host-{}-{}.yu",
        std::process::id(),
        unique_suffix()
    ));
    fs::write(&source_path, "[1, 2, 3].say\n").expect("write test source");

    let source_output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .arg("run")
        .arg(&source_path)
        .output()
        .expect("run yulang source");
    let _ = fs::remove_file(&source_path);
    assert!(
        source_output.status.success(),
        "source run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&source_output.stdout),
        String::from_utf8_lossy(&source_output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&source_output.stdout),
        "[1, 2, 3]\n"
    );
}

fn unique_suffix() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos()
}
