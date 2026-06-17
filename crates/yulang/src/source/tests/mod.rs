use super::*;
use std::sync::{Mutex, MutexGuard, OnceLock};

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

fn yulang_fixture(path: &str) -> String {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests")
        .join("yulang");
    let full_path = root.join(path);
    fs::read_to_string(&full_path)
        .unwrap_or_else(|error| panic!("failed to read fixture {}: {error}", full_path.display()))
}

fn write_fixture_with_fake_std(name: &str, fake_std: &str, fixture: &str) -> PathBuf {
    let source = format!("{}\n{}", yulang_fixture(fake_std), yulang_fixture(fixture));
    write_main(name, &source)
}

fn write_source_with_fake_std(name: &str, fake_std: &str, source: &str) -> PathBuf {
    let source = format!("{}\n{}", yulang_fixture(fake_std), source);
    write_main(name, &source)
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

struct EnvVarGuard {
    key: &'static str,
    previous: Option<std::ffi::OsString>,
    _lock: MutexGuard<'static, ()>,
}

impl EnvVarGuard {
    fn set_path(key: &'static str, value: &FsPath) -> Self {
        static ENV_LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        let lock = ENV_LOCK.get_or_init(|| Mutex::new(()));
        let guard = lock.lock().expect("env var test lock");
        let previous = std::env::var_os(key);
        // Rust 2024 marks process environment mutation unsafe because it is
        // global. Tests that use this helper serialize the mutation.
        unsafe {
            std::env::set_var(key, value);
        }
        Self {
            key,
            previous,
            _lock: guard,
        }
    }
}

impl Drop for EnvVarGuard {
    fn drop(&mut self) {
        unsafe {
            match &self.previous {
                Some(value) => std::env::set_var(self.key, value),
                None => std::env::remove_var(self.key),
            }
        }
    }
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
