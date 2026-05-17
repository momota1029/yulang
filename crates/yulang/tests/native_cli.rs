use std::{fs, process::Command};

#[test]
fn native_range_for_with_console_effect_continues_past_first_iteration() {
    let source = r#"
use std::flow::*

sub:
    for x in 0..<3:
        say x.show
        if x == 2:
            return 42
        else:
            ()
    0
"#;
    let path = std::env::temp_dir().join(format!(
        "yulang-native-range-console-{}-{}.yu",
        std::process::id(),
        unique_suffix()
    ));
    fs::write(&path, source).expect("write test source");

    let output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .arg("run")
        .arg("--native")
        .arg(&path)
        .arg("--print-roots")
        .output()
        .expect("run yulang native CLI");
    let _ = fs::remove_file(&path);

    assert!(
        output.status.success(),
        "native CLI failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "0\n1\n2\n42\n");
}

#[test]
fn native_effect_handler_guard_unit_root_prints_unit() {
    let source = r#"
act log:
    pub put: int -> ()

my run(a: [log] 'r): 'r = catch a:
    log::put n, k if n > 0 -> run (k ())
    log::put _, k -> run (k ())
    v -> v

run: log::put 5
"#;
    let path = std::env::temp_dir().join(format!(
        "yulang-native-handler-guard-unit-{}-{}.yu",
        std::process::id(),
        unique_suffix()
    ));
    fs::write(&path, source).expect("write test source");

    let output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .arg("run")
        .arg("--native")
        .arg(&path)
        .arg("--print-roots")
        .output()
        .expect("run yulang native CLI");
    let _ = fs::remove_file(&path);

    assert!(
        output.status.success(),
        "native CLI failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "()\n");
}

#[test]
fn native_undet_branch_list_prints_collected_list() {
    let source = r#"
use std::undet::*

(branch()).list
"#;
    let path = std::env::temp_dir().join(format!(
        "yulang-native-undet-branch-list-{}-{}.yu",
        std::process::id(),
        unique_suffix()
    ));
    fs::write(&path, source).expect("write test source");

    let output = Command::new(env!("CARGO_BIN_EXE_yulang"))
        .arg("run")
        .arg("--native")
        .arg(&path)
        .arg("--print-roots")
        .output()
        .expect("run yulang native CLI");
    let _ = fs::remove_file(&path);

    assert!(
        output.status.success(),
        "native CLI failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "[1, 0]\n");
}

fn unique_suffix() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after unix epoch")
        .as_nanos()
}
