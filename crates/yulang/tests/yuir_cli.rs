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

#[test]
fn run_reuses_compiled_std_cache_for_mixed_numeric_calls() {
    let suffix = unique_suffix();
    let cache_root =
        std::env::temp_dir().join(format!("yulang-cli-cache-{}-{suffix}", std::process::id()));
    let warmup_path = std::env::temp_dir().join(format!(
        "yulang-cli-cache-warmup-{}-{suffix}.yu",
        std::process::id()
    ));
    let mixed_path = std::env::temp_dir().join(format!(
        "yulang-cli-cache-mixed-{}-{suffix}.yu",
        std::process::id()
    ));
    let std_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib/std");
    fs::write(&warmup_path, "(7/3).say\n").expect("write warmup source");
    fs::write(
        &mixed_path,
        "(1 + 1.2).say\n(7/3 + 1.2).say\n(1 / 3.0).say\n(2 * 3.0).say\n",
    )
    .expect("write mixed source");

    let warmup_output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(&std_root)
        .arg("run")
        .arg(&warmup_path)
        .output()
        .expect("run yulang cache warmup");
    assert!(
        warmup_output.status.success(),
        "warmup run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&warmup_output.stdout),
        String::from_utf8_lossy(&warmup_output.stderr)
    );

    let mixed_output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(&std_root)
        .arg("run")
        .arg(&mixed_path)
        .output()
        .expect("run yulang with compiled std cache");
    let _ = fs::remove_file(&warmup_path);
    let _ = fs::remove_file(&mixed_path);
    let _ = fs::remove_dir_all(&cache_root);
    assert!(
        mixed_output.status.success(),
        "cached mixed run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&mixed_output.stdout),
        String::from_utf8_lossy(&mixed_output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&mixed_output.stdout),
        "2.2\n3.533333333333333\n0.3333333333333333\n6.0\n"
    );
}

#[test]
fn run_reuses_compiled_std_cache_for_undet_role_add() {
    let suffix = unique_suffix();
    let cache_root = std::env::temp_dir().join(format!(
        "yulang-cli-undet-cache-{}-{suffix}",
        std::process::id()
    ));
    let warmup_path = std::env::temp_dir().join(format!(
        "yulang-cli-undet-cache-warmup-{}-{suffix}.yu",
        std::process::id()
    ));
    let undet_path = std::env::temp_dir().join(format!(
        "yulang-cli-undet-cache-run-{}-{suffix}.yu",
        std::process::id()
    ));
    let std_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib/std");
    fs::write(&warmup_path, "(7/3).say\n").expect("write warmup source");
    fs::write(&undet_path, "(each 1..3 + each 1..3).list\n").expect("write undet source");

    let warmup_output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(&std_root)
        .arg("run")
        .arg(&warmup_path)
        .output()
        .expect("run yulang cache warmup");
    assert!(
        warmup_output.status.success(),
        "warmup run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&warmup_output.stdout),
        String::from_utf8_lossy(&warmup_output.stderr)
    );

    let undet_output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .env("YULANG_CACHE_DIR", &cache_root)
        .arg("--std-root")
        .arg(&std_root)
        .arg("run")
        .arg("--print-roots")
        .arg(&undet_path)
        .output()
        .expect("run yulang with compiled std cache");
    let _ = fs::remove_file(&warmup_path);
    let _ = fs::remove_file(&undet_path);
    let _ = fs::remove_dir_all(&cache_root);
    assert!(
        undet_output.status.success(),
        "cached undet run failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&undet_output.stdout),
        String::from_utf8_lossy(&undet_output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&undet_output.stdout),
        "[0] [2, 3, 4, 3, 4, 5, 4, 5, 6]\n"
    );
}

fn unique_suffix() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos()
}
