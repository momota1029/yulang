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

fn unique_suffix() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after unix epoch")
        .as_nanos()
}
