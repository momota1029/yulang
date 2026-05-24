use std::path::{Path, PathBuf};
use std::{fs, process::Command};

#[test]
fn runtime_finalize_runs_range_each_sum_with_cold_std_cache() {
    let fixture = RuntimeFinalizeCliFixture::new("runtime-finalize-cold-range-each");
    fixture.write_temp_source(
        "range_each.yu",
        "use std::undet::*\n((1..3).each + (1..3).each).list\n",
    );

    let stdout = fixture.run_file_stdout(
        "cold range each",
        &fixture.temp_source_path("range_each.yu"),
    );
    assert_eq!(stdout, "[0] [2, 3, 4, 3, 4, 5, 4, 5, 6]\n");
}

#[test]
fn runtime_finalize_runs_examples_and_playground_samples_with_shared_std_cache() {
    let fixture = RuntimeFinalizeCliFixture::new("runtime-finalize-smoke");
    fixture.write_temp_source("warmup.yu", "1 + 2\n");
    fixture.run_file("warmup", &fixture.temp_source_path("warmup.yu"));

    for (name, path) in [
        ("01_struct_with", example_path("01_struct_with.yu")),
        ("02_refs", example_path("02_refs.yu")),
        ("03_for_last", example_path("03_for_last.yu")),
        ("04_sub_return", example_path("04_sub_return.yu")),
        ("05_undet_all", example_path("05_undet_all.yu")),
        ("06_undet_once", example_path("06_undet_once.yu")),
        ("07_junction", example_path("07_junction.yu")),
        ("08_types", example_path("08_types.yu")),
        (
            "09_optional_record_args",
            example_path("09_optional_record_args.yu"),
        ),
        ("10_effect_handler", example_path("10_effect_handler.yu")),
        ("11_attached_impl", example_path("11_attached_impl.yu")),
        ("12_cast", example_path("12_cast.yu")),
        ("13_console", example_path("13_console.yu")),
        ("showcase", example_path("showcase.yu")),
    ] {
        fixture.run_file(name, &path);
    }

    fixture.write_temp_source(
        "callback_hygiene.yu",
        r#"use std::*
use std::flow::*

our g h = sub:
    for i in 0..3:
        h i
    return 1

sub:
    my b = g \i -> if i == 0: return i
    println b.show
    2
"#,
    );
    fixture.run_file(
        "playground callback hygiene",
        &fixture.temp_source_path("callback_hygiene.yu"),
    );
}

struct RuntimeFinalizeCliFixture {
    root: PathBuf,
    cache_root: PathBuf,
    std_root: PathBuf,
}

impl RuntimeFinalizeCliFixture {
    fn new(name: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "yulang-{name}-{}-{}",
            std::process::id(),
            unique_suffix()
        ));
        fs::create_dir_all(&root).expect("create temp fixture root");
        Self {
            cache_root: root.join("cache"),
            std_root: manifest_root().join("../../lib/std"),
            root,
        }
    }

    fn write_temp_source(&self, name: &str, source: &str) {
        fs::write(self.temp_source_path(name), source).expect("write temp source");
    }

    fn temp_source_path(&self, name: &str) -> PathBuf {
        self.root.join(name)
    }

    fn run_file(&self, name: &str, source_path: &Path) {
        self.run_file_stdout(name, source_path);
    }

    fn run_file_stdout(&self, name: &str, source_path: &Path) -> String {
        let output = Command::new(env!("CARGO_BIN_EXE_yulang"))
            .env("YULANG_RUNTIME_FINALIZE", "1")
            .env("YULANG_CACHE_DIR", &self.cache_root)
            .arg("--std-root")
            .arg(&self.std_root)
            .arg("run")
            .arg("--print-roots")
            .arg(source_path)
            .output()
            .unwrap_or_else(|error| panic!("{name}: run yulang failed: {error}"));
        assert!(
            output.status.success(),
            "{name} failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).expect("yulang stdout should be UTF-8")
    }
}

impl Drop for RuntimeFinalizeCliFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn example_path(name: &str) -> PathBuf {
    manifest_root().join("../../examples").join(name)
}

fn manifest_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn unique_suffix() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos()
}
