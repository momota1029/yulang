use super::*;

fn temp_root(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "yulang-{name}-{}",
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ))
}

#[cfg(unix)]
fn symlink_repo_lib(root: &FsPath) {
    let repo_lib = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib");
    std::os::unix::fs::symlink(repo_lib, root.join("lib")).unwrap();
}

fn write_main(name: &str, source: &str) -> PathBuf {
    let root = temp_root(name);
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let entry = root.join("main.yu");
    fs::write(&entry, source).unwrap();
    entry
}

#[cfg(unix)]
fn write_main_with_std(name: &str, source: &str) -> PathBuf {
    let root = temp_root(name);
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    symlink_repo_lib(&root);
    let entry = root.join("main.yu");
    fs::write(&entry, source).unwrap();
    entry
}

#[cfg(unix)]
fn run_with_std_main(name: &str, source: &str) -> (RunMonoOutput, RunControlOutput) {
    let entry = write_main_with_std(name, source);
    let mono = run_mono_from_entry_with_std(&entry).unwrap();
    let control = run_control_from_entry_with_std(&entry).unwrap();
    (mono, control)
}

fn assert_dump_has_line_starting_with(output: &DumpPolyOutput, expected: &str) {
    assert!(
        output.text.lines().any(|line| line.starts_with(expected)),
        "missing line starting with {expected:?} in:\n{}",
        output.text
    );
}

fn assert_dump_contains(output: &DumpPolyOutput, expected: &str) {
    assert!(
        output.text.contains(expected),
        "missing {expected:?} in:\n{}",
        output.text
    );
}

fn assert_mono_dump_contains(output: &DumpMonoOutput, expected: &str) {
    assert!(
        output.text.contains(expected),
        "missing {expected:?} in:\n{}",
        output.text
    );
}

fn assert_check_contains(output: &CheckPolyOutput, expected: &str) {
    assert!(
        output.text.contains(expected),
        "missing {expected:?} in:\n{}",
        output.text
    );
}

fn assert_unsatisfied_subtype_contains(err: RouteError, lower: &str, upper: &str) {
    let text = err.to_string();
    assert!(
        matches!(
            &err,
            RouteError::Specialize(specialize::SpecializeError::UnsatisfiedSubtype { .. })
        ),
        "expected UnsatisfiedSubtype, got {err:?}"
    );
    assert!(
        text.contains(lower),
        "missing lower type fragment {lower:?} in:\n{text}"
    );
    assert!(
        text.contains(upper),
        "missing upper type fragment {upper:?} in:\n{text}"
    );
    assert!(
        !text.contains("unsupported VM boundary"),
        "subtype mismatch leaked to VM boundary:\n{text}"
    );
}

mod case_01;
mod case_02;
