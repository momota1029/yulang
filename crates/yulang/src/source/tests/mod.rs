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

fn run_with_vm_test_stack<T: Send + 'static>(run: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap()
}

fn run_built_control_on_vm_test_stack(build: BuildControlOutput) -> (String, String) {
    run_with_vm_test_stack(move || {
        let output = run_built_control_program_with_labels(
            &build.program,
            build.file_count,
            build.errors,
            Some(&build.labels),
        )
        .expect("control VM program should run");
        (output.text, output.stdout)
    })
}

struct EnvVarGuard {
    key: &'static str,
    previous: Option<std::ffi::OsString>,
    _lock: MutexGuard<'static, ()>,
}

impl EnvVarGuard {
    fn unset(key: &'static str) -> Self {
        static ENV_LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        let lock = ENV_LOCK.get_or_init(|| Mutex::new(()));
        let guard = lock.lock().expect("env var test lock");
        let previous = std::env::var_os(key);
        unsafe {
            std::env::remove_var(key);
        }
        Self {
            key,
            previous,
            _lock: guard,
        }
    }

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

fn compiled_unit_artifact_count(cache_root: &FsPath) -> usize {
    artifact_stage_count(cache_root, "compiled-unit")
}

fn artifact_stage_count(cache_root: &FsPath, stage: &str) -> usize {
    let dir = cache_root.join("artifacts").join(stage);
    match fs::read_dir(dir) {
        Ok(entries) => entries
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.is_file())
            .count(),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => 0,
        Err(error) => panic!("failed to read artifact stage {stage}: {error}"),
    }
}

fn dump_public_signature<'a>(output: &'a DumpPolyOutput, symbol: &str) -> &'a str {
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

fn dump_public_signature_type<'a>(output: &'a DumpPolyOutput, symbol: &str) -> &'a str {
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

fn dump_public_signature_containing<'a>(output: &'a DumpPolyOutput, needle: &str) -> &'a str {
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

fn public_signature_type_from_dump_line(line: &str) -> Option<&str> {
    if !line.trim_start().starts_with("pub ") {
        return None;
    }
    let signature = trim_public_signature_body(line);
    let (_, ty) = signature.split_once(": ")?;
    Some(ty)
}

fn dump_public_signature_type_containing<'a>(output: &'a DumpPolyOutput, needle: &str) -> &'a str {
    let signature = dump_public_signature_containing(output, needle);
    let Some(start) = signature.find("\": ") else {
        panic!("public signature containing {needle:?} is not quoted:\n{signature}");
    };
    &signature[start + "\": ".len()..]
}

fn assert_public_signature_type_eq<'a>(
    output: &'a DumpPolyOutput,
    symbol: &str,
    expected: &str,
) -> &'a str {
    let ty = dump_public_signature_type(output, symbol);
    assert_eq!(ty, expected, "unexpected public type for {symbol}");
    ty
}

fn assert_public_signature_type_hides_stack_evidence<'a>(
    output: &'a DumpPolyOutput,
    symbol: &str,
) -> &'a str {
    let ty = dump_public_signature_type(output, symbol);
    assert_public_signature_type_has_no_private_stack_evidence(ty, symbol);
    ty
}

fn assert_public_signature_type_containing_hides_stack_evidence<'a>(
    output: &'a DumpPolyOutput,
    needle: &str,
) -> &'a str {
    let ty = dump_public_signature_type_containing(output, needle);
    assert_public_signature_type_has_no_private_stack_evidence(
        ty,
        &format!("public signature containing {needle:?}"),
    );
    ty
}

fn assert_all_public_signature_types_hide_stack_evidence(output: &DumpPolyOutput, context: &str) {
    for line in output.text.lines() {
        let Some(ty) = public_signature_type_from_dump_line(line) else {
            continue;
        };
        assert_public_signature_type_has_no_private_stack_evidence(
            ty,
            &format!("{context} public signature line `{line}`"),
        );
    }
}

fn assert_public_signature_type_has_no_private_stack_evidence(ty: &str, context: &str) {
    assert!(
        !ty.contains('#') && !ty.contains("AllExcept"),
        "private stack evidence escaped into {context}:\n{ty}"
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
