//! Resource-limited real-literal-scale oracle for production Yumark lowering.
//!
//! Algebra passing is now the only production route. This test retains the
//! Shadow Stage 1 fixture and its hard process limits to ensure that a named,
//! let-generalized real document compiles, specializes, and renders in both
//! formats without recreating the retired recursive-role memory failure. It
//! does not claim that the underlying role solver bug is fixed.

#![cfg(unix)]

use mono_runtime::Value;
use std::fs;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path as FsPath, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};
use yulang::collect_local_sources_with_std;

const TEST_ADDRESS_SPACE_LIMIT_BYTES: libc::rlim_t = 3 * 1024 * 1024 * 1024;
const RESOURCE_LIMIT_WORKER_ENV: &str = "YULANG_YUMARK_RESOURCE_LIMIT_WORKER";
const ADDRESS_SPACE_SAFETY_FAILURE: &str = "hit the enforced 3 GiB address-space safety limit";
const KNOWN_MEMORY_BUG_REPORT: &str =
    "notes/bugs/2026-07-17-yumark-generalization-memory-exhaustion.md";

#[test]
fn real_literal_production_route_compiles_and_renders_successfully() {
    enforce_yumark_test_resource_limits();
    if run_in_resource_limited_worker(
        "real_literal_production_route_compiles_and_renders_successfully",
    ) {
        return;
    }

    let html_entry = write_fixture_entry("production-html", RenderFormat::Html);
    let markdown_entry = write_fixture_entry("production-markdown", RenderFormat::Markdown);
    let (html, markdown) =
        run_with_large_stack(move || (run_route(&html_entry), run_route(&markdown_entry)));

    assert!(html.contains("<h1>"));
    assert!(html.contains("Shadow lowering at real literal scale"));
    assert!(html.contains("<blockquote>"));
    assert!(html.contains("<pre>"));
    assert!(markdown.contains("# Shadow lowering at real literal scale"));
    assert!(markdown.contains("```yulang"));
}

#[derive(Clone, Copy)]
enum RenderFormat {
    Html,
    Markdown,
}

fn run_route(entry: &FsPath) -> String {
    let files = collect_local_sources_with_std(entry).expect("collect repository std");
    let build =
        yulang::build_poly_from_collected_sources(files).expect("compile real Yumark literal");
    build.ensure_runtime_ready().expect("lowering diagnostics");

    let program = specialize::specialize(&build.arena).expect("specialize real Yumark literal");
    let mut values = mono_runtime::run_program(&program).expect("run real Yumark literal");
    assert_eq!(values.len(), 1, "expected one rendered root");
    match values.pop().expect("rendered root") {
        Value::Str(value) => value.to_string(),
        other => panic!("expected rendered string, got {other:?}"),
    }
}

fn write_fixture_entry(label: &str, format: RenderFormat) -> PathBuf {
    let root = std::env::temp_dir().join(format!(
        "yulang-yumark-literal-{label}-{}",
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos()
    ));
    fs::create_dir_all(&root).expect("create fixture root");
    std::os::unix::fs::symlink(repository_root().join("lib"), root.join("lib"))
        .expect("link repository std");
    let literal = fs::read_to_string(fixture_path()).expect("read real-literal fixture");
    let (render_prefix, render_suffix) = match format {
        RenderFormat::Html => (
            "std::text::yumark::html_tag (std::text::yumark::render_html_doc (",
            "))",
        ),
        RenderFormat::Markdown => ("std::text::yumark::render_markdown_doc (", ")"),
    };
    let source = format!("my proof() = {render_prefix}\n{literal}\n{render_suffix}\nproof()\n");
    let entry = root.join("main.yu");
    fs::write(&entry, source).expect("write fixture entry");
    entry
}

fn fixture_path() -> PathBuf {
    repository_root()
        .join("tests/yulang/regressions/cache/yumark_shadow_literal_performance_workload.yu")
}

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn run_with_large_stack<T: Send + 'static>(run: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(run)
        .expect("spawn Yumark test thread")
        .join()
        .expect("Yumark test thread")
}

fn enforce_yumark_test_resource_limits() {
    let mut current = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    // SAFETY: `current` and `bounded` are valid `rlimit` values for the whole
    // duration of each call. Lowering both values only narrows this test
    // process's existing limits.
    unsafe {
        if libc::getrlimit(libc::RLIMIT_AS, &mut current) != 0 {
            panic!(
                "failed to read the address-space limit before compiling the Yumark fixture: {}",
                std::io::Error::last_os_error()
            );
        }
        let bounded_hard = current.rlim_max.min(TEST_ADDRESS_SPACE_LIMIT_BYTES);
        let bounded = libc::rlimit {
            rlim_cur: current.rlim_cur.min(bounded_hard),
            rlim_max: bounded_hard,
        };
        if libc::setrlimit(libc::RLIMIT_AS, &bounded) != 0 {
            panic!(
                "failed to enforce the 3 GiB address-space safety limit before compiling the Yumark fixture: {}",
                std::io::Error::last_os_error()
            );
        }

        let no_core_dump = libc::rlimit {
            rlim_cur: 0,
            rlim_max: 0,
        };
        if libc::setrlimit(libc::RLIMIT_CORE, &no_core_dump) != 0 {
            panic!(
                "failed to disable core dumps for the resource-limited Yumark fixture test: {}",
                std::io::Error::last_os_error()
            );
        }
    }
}

/// Returns `true` in the harness process after the worker succeeded and
/// `false` in the worker process, where the caller performs the compile/run.
fn run_in_resource_limited_worker(test_name: &str) -> bool {
    if std::env::var_os(RESOURCE_LIMIT_WORKER_ENV).is_some() {
        return false;
    }

    let output = Command::new(std::env::current_exe().expect("locate Yumark integration test"))
        .arg("--exact")
        .arg(test_name)
        .arg("--include-ignored")
        .arg("--nocapture")
        .arg("--test-threads=1")
        .env(RESOURCE_LIMIT_WORKER_ENV, "1")
        .output()
        .expect("spawn resource-limited Yumark integration-test worker");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("running 1 test"),
        "resource-limited Yumark worker did not select {test_name}:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    if output.status.success() {
        return true;
    }
    if output.status.signal() == Some(libc::SIGABRT) {
        panic!(
            "{ADDRESS_SPACE_SAFETY_FAILURE} while compiling the production algebra-passing route; {KNOWN_MEMORY_BUG_REPORT} only documents the retired recursive-role path, so this is a new regression\nworker stderr:\n{stderr}"
        );
    }
    panic!(
        "resource-limited Yumark worker failed with {} while running {test_name}:\nstdout:\n{stdout}\nstderr:\n{stderr}",
        output.status
    );
}
