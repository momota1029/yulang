//! Opt-in process telemetry for the RCPF-F and CPK-8 quarantine soak gates.
//!
//! Ordinary compilation pays one cached environment lookup per constraint-machine construction.
//! Counters and the file sink are touched only on terminal failure/read-error/retry paths.

use std::fs::{File, OpenOptions};
use std::io::Write;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

use super::proof::ProofOperation;
use super::{ProofFailure, ReplayFactoredShadowFailure};

pub(crate) const RCPF_SOAK_TELEMETRY_VERSION: u32 = 1;
pub(crate) const CPK_SOAK_TELEMETRY_VERSION: u32 = 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(debug_assertions), allow(dead_code))]
pub(crate) enum ReplayFactoredFailureOperation {
    Write,
    Read,
    Oracle,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) enum ReplaySoakEventOrigin {
    Organic,
    IntentionalTestInjection,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct ReplaySoakTelemetrySnapshot {
    terminal_failures: [u64; 6],
    legacy_rollback_entries: [u64; 2],
    factored_read_errors: [u64; 2],
    proof_terminal_failures: [u64; 12],
}

impl ReplaySoakTelemetrySnapshot {
    #[cfg(test)]
    pub(crate) fn terminal_failures(
        self,
        origin: ReplaySoakEventOrigin,
        operation: ReplayFactoredFailureOperation,
    ) -> u64 {
        self.terminal_failures[terminal_index(origin, operation)]
    }

    #[cfg(test)]
    pub(crate) fn legacy_rollback_entries(self, origin: ReplaySoakEventOrigin) -> u64 {
        self.legacy_rollback_entries[origin_index(origin)]
    }

    #[cfg(test)]
    pub(crate) fn factored_read_errors(self, origin: ReplaySoakEventOrigin) -> u64 {
        self.factored_read_errors[origin_index(origin)]
    }

    #[cfg(test)]
    pub(crate) fn proof_terminal_failures(
        self,
        origin: ReplaySoakEventOrigin,
        operation: ProofOperation,
    ) -> u64 {
        self.proof_terminal_failures[proof_terminal_index(origin, operation)]
    }

    #[cfg(test)]
    pub(crate) fn total_for_origin(self, origin: ReplaySoakEventOrigin) -> u64 {
        let start = origin_index(origin) * 3;
        self.terminal_failures[start..start + 3].iter().sum::<u64>()
            + self.legacy_rollback_entries[origin_index(origin)]
            + self.factored_read_errors[origin_index(origin)]
            + self.proof_terminal_failures[origin_index(origin) * 6..origin_index(origin) * 6 + 6]
                .iter()
                .sum::<u64>()
    }
}

static TERMINAL_FAILURES: [AtomicU64; 6] = [const { AtomicU64::new(0) }; 6];
static LEGACY_ROLLBACK_ENTRIES: [AtomicU64; 2] = [const { AtomicU64::new(0) }; 2];
static FACTORED_READ_ERRORS: [AtomicU64; 2] = [const { AtomicU64::new(0) }; 2];
static PROOF_TERMINAL_FAILURES: [AtomicU64; 12] = [const { AtomicU64::new(0) }; 12];
static TELEMETRY_SINK: OnceLock<Option<Mutex<File>>> = OnceLock::new();
static PROOF_TELEMETRY_SINK: OnceLock<Option<Mutex<File>>> = OnceLock::new();

#[cfg(test)]
std::thread_local! {
    static INTENTIONAL_TEST_INJECTION_DEPTH: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static TEST_CAPTURE: std::cell::RefCell<Option<ReplaySoakTelemetrySnapshot>> = const {
        std::cell::RefCell::new(None)
    };
    static NEXT_FAILURE_IS_INTENTIONAL: std::cell::Cell<bool> = const {
        std::cell::Cell::new(false)
    };
}

pub(crate) fn ensure_replay_soak_telemetry_header() {
    let _ = telemetry_sink();
    let _ = proof_telemetry_sink();
}

pub(crate) fn record_replay_factored_failure(
    failure: ReplayFactoredShadowFailure,
    operation: ReplayFactoredFailureOperation,
    first_terminal_failure: bool,
) {
    let origin = current_event_origin();
    if operation == ReplayFactoredFailureOperation::Read {
        FACTORED_READ_ERRORS[origin_index(origin)].fetch_add(1, Ordering::Relaxed);
        update_test_capture(|snapshot| {
            snapshot.factored_read_errors[origin_index(origin)] += 1;
        });
    }
    if first_terminal_failure {
        TERMINAL_FAILURES[terminal_index(origin, operation)].fetch_add(1, Ordering::Relaxed);
        update_test_capture(|snapshot| {
            snapshot.terminal_failures[terminal_index(origin, operation)] += 1;
        });
        emit_event("terminal_failure", origin, Some(operation), Some(failure));
    }
    if operation == ReplayFactoredFailureOperation::Read {
        emit_event(
            "factored_read_error",
            origin,
            Some(operation),
            Some(failure),
        );
    }
}

pub(crate) fn record_legacy_rollback_entry(failure: ReplayFactoredShadowFailure) {
    let origin = current_event_origin();
    LEGACY_ROLLBACK_ENTRIES[origin_index(origin)].fetch_add(1, Ordering::Relaxed);
    update_test_capture(|snapshot| {
        snapshot.legacy_rollback_entries[origin_index(origin)] += 1;
    });
    emit_event("legacy_rollback_entry", origin, None, Some(failure));
}

/// Record the first sticky CPK terminal failure for one compilation attempt.
/// The caller owns the first-failure check so repeated reads after the machine has already
/// failed cannot inflate the organic soak census.
pub(crate) fn record_proof_terminal_failure(operation: ProofOperation, failure: &ProofFailure) {
    let origin = current_event_origin();
    PROOF_TERMINAL_FAILURES[proof_terminal_index(origin, operation)].fetch_add(1, Ordering::Relaxed);
    update_test_capture(|snapshot| {
        snapshot.proof_terminal_failures[proof_terminal_index(origin, operation)] += 1;
    });
    emit_proof_event("proof_terminal_failure", origin, Some(operation), Some(failure));
}

pub(crate) fn replay_soak_telemetry_snapshot() -> ReplaySoakTelemetrySnapshot {
    ReplaySoakTelemetrySnapshot {
        terminal_failures: std::array::from_fn(|index| {
            TERMINAL_FAILURES[index].load(Ordering::Relaxed)
        }),
        legacy_rollback_entries: std::array::from_fn(|index| {
            LEGACY_ROLLBACK_ENTRIES[index].load(Ordering::Relaxed)
        }),
        factored_read_errors: std::array::from_fn(|index| {
            FACTORED_READ_ERRORS[index].load(Ordering::Relaxed)
        }),
        proof_terminal_failures: std::array::from_fn(|index| {
            PROOF_TERMINAL_FAILURES[index].load(Ordering::Relaxed)
        }),
    }
}

#[cfg(test)]
pub(crate) fn with_intentional_replay_soak_test_injection<T>(run: impl FnOnce() -> T) -> T {
    struct Guard;

    impl Drop for Guard {
        fn drop(&mut self) {
            INTENTIONAL_TEST_INJECTION_DEPTH.with(|depth| depth.set(depth.get() - 1));
        }
    }

    INTENTIONAL_TEST_INJECTION_DEPTH.with(|depth| depth.set(depth.get() + 1));
    let _guard = Guard;
    run()
}

#[cfg(test)]
pub(crate) fn mark_next_replay_soak_failure_as_intentional() {
    NEXT_FAILURE_IS_INTENTIONAL.with(|next| next.set(true));
}

#[cfg(test)]
pub(crate) fn capture_replay_soak_test_events<T>(
    run: impl FnOnce() -> T,
) -> (T, ReplaySoakTelemetrySnapshot) {
    TEST_CAPTURE.with(|capture| {
        assert!(capture.borrow().is_none(), "nested RCPF soak capture");
        *capture.borrow_mut() = Some(ReplaySoakTelemetrySnapshot::default());
    });
    let output = run();
    let snapshot = TEST_CAPTURE.with(|capture| {
        capture
            .borrow_mut()
            .take()
            .expect("RCPF soak capture must remain installed")
    });
    (output, snapshot)
}

fn current_event_origin() -> ReplaySoakEventOrigin {
    #[cfg(test)]
    {
        if INTENTIONAL_TEST_INJECTION_DEPTH.with(|depth| depth.get() > 0)
            || NEXT_FAILURE_IS_INTENTIONAL.with(|next| next.replace(false))
        {
            return ReplaySoakEventOrigin::IntentionalTestInjection;
        }
    }
    ReplaySoakEventOrigin::Organic
}

fn origin_index(origin: ReplaySoakEventOrigin) -> usize {
    match origin {
        ReplaySoakEventOrigin::Organic => 0,
        ReplaySoakEventOrigin::IntentionalTestInjection => 1,
    }
}

fn operation_index(operation: ReplayFactoredFailureOperation) -> usize {
    match operation {
        ReplayFactoredFailureOperation::Write => 0,
        ReplayFactoredFailureOperation::Read => 1,
        ReplayFactoredFailureOperation::Oracle => 2,
    }
}

fn terminal_index(
    origin: ReplaySoakEventOrigin,
    operation: ReplayFactoredFailureOperation,
) -> usize {
    origin_index(origin) * 3 + operation_index(operation)
}

fn proof_operation_index(operation: ProofOperation) -> usize {
    match operation {
        ProofOperation::ProjectLowerPreflight => 0,
        ProofOperation::ProjectLowerSupportCollection => 1,
        ProofOperation::ProjectLowerEvaluation => 2,
        ProofOperation::PrepareReplayRoutePreflight => 3,
        ProofOperation::PrepareReplayRouteParentCollection => 4,
        ProofOperation::PrepareReplayRouteBatch => 5,
    }
}

fn proof_terminal_index(origin: ReplaySoakEventOrigin, operation: ProofOperation) -> usize {
    origin_index(origin) * 6 + proof_operation_index(operation)
}

fn update_test_capture(update: impl FnOnce(&mut ReplaySoakTelemetrySnapshot)) {
    #[cfg(test)]
    TEST_CAPTURE.with(|capture| {
        if let Some(snapshot) = capture.borrow_mut().as_mut() {
            update(snapshot);
        }
    });
    #[cfg(not(test))]
    let _ = update;
}

fn telemetry_sink() -> Option<&'static Mutex<File>> {
    TELEMETRY_SINK
        .get_or_init(|| {
            let path = std::env::var_os("YULANG_RCPF_SOAK_TELEMETRY_PATH")?;
            match OpenOptions::new().create(true).append(true).open(&path) {
                Ok(mut file) => {
                    let _ = writeln!(
                        file,
                        "RCPF_SOAK_HEADER version={} pid={} commit={} workload={} generalize_compact_cache={} source_cache={}",
                        RCPF_SOAK_TELEMETRY_VERSION,
                        std::process::id(),
                        metadata("YULANG_RCPF_SOAK_COMMIT"),
                        metadata("YULANG_RCPF_SOAK_WORKLOAD"),
                        generalize_compact_cache_mode(),
                        metadata("YULANG_RCPF_SOAK_SOURCE_CACHE_MODE"),
                    );
                    write_tally(&mut file, replay_soak_telemetry_snapshot());
                    Some(Mutex::new(file))
                }
                Err(error) => {
                    eprintln!(
                        "RCPF_SOAK_ERROR telemetry_path={} error={error}",
                        path.to_string_lossy()
                    );
                    None
                }
            }
        })
        .as_ref()
}

fn proof_telemetry_sink() -> Option<&'static Mutex<File>> {
    PROOF_TELEMETRY_SINK
        .get_or_init(|| {
            let path = std::env::var_os("YULANG_CPK_SOAK_TELEMETRY_PATH")?;
            match OpenOptions::new().create(true).append(true).open(&path) {
                Ok(mut file) => {
                    let _ = writeln!(
                        file,
                        "CPK_SOAK_HEADER version={} pid={} commit={} build_profile={} workload={} generalize_compact_cache={} source_cache={}",
                        CPK_SOAK_TELEMETRY_VERSION,
                        std::process::id(),
                        metadata("YULANG_CPK_SOAK_COMMIT"),
                        build_profile(),
                        metadata("YULANG_CPK_SOAK_WORKLOAD"),
                        generalize_compact_cache_mode(),
                        metadata("YULANG_CPK_SOAK_SOURCE_CACHE_MODE"),
                    );
                    write_proof_tally(&mut file, replay_soak_telemetry_snapshot());
                    Some(Mutex::new(file))
                }
                Err(error) => {
                    eprintln!(
                        "CPK_SOAK_ERROR telemetry_path={} error={error}",
                        path.to_string_lossy()
                    );
                    None
                }
            }
        })
        .as_ref()
}

fn emit_event(
    event: &str,
    origin: ReplaySoakEventOrigin,
    operation: Option<ReplayFactoredFailureOperation>,
    failure: Option<ReplayFactoredShadowFailure>,
) {
    let Some(sink) = telemetry_sink() else {
        return;
    };
    let Ok(mut file) = sink.lock() else {
        return;
    };
    let _ = writeln!(
        file,
        "RCPF_SOAK_EVENT event={event} origin={origin:?} operation={operation:?} failure={failure:?}"
    );
    write_tally(&mut file, replay_soak_telemetry_snapshot());
}

fn emit_proof_event(
    event: &str,
    origin: ReplaySoakEventOrigin,
    operation: Option<ProofOperation>,
    failure: Option<&ProofFailure>,
) {
    let Some(sink) = proof_telemetry_sink() else {
        return;
    };
    let Ok(mut file) = sink.lock() else {
        return;
    };
    let _ = writeln!(
        file,
        "CPK_SOAK_EVENT event={event} origin={origin:?} operation={operation:?} failure={failure:?}"
    );
    write_proof_tally(&mut file, replay_soak_telemetry_snapshot());
}

fn write_tally(file: &mut File, snapshot: ReplaySoakTelemetrySnapshot) {
    let _ = writeln!(
        file,
        concat!(
            "RCPF_SOAK_TALLY version={} ",
            "terminal_organic_write={} terminal_organic_read={} terminal_organic_oracle={} ",
            "terminal_injected_write={} terminal_injected_read={} terminal_injected_oracle={} ",
            "rollback_organic={} rollback_injected={} ",
            "read_error_organic={} read_error_injected={}"
        ),
        RCPF_SOAK_TELEMETRY_VERSION,
        snapshot.terminal_failures[0],
        snapshot.terminal_failures[1],
        snapshot.terminal_failures[2],
        snapshot.terminal_failures[3],
        snapshot.terminal_failures[4],
        snapshot.terminal_failures[5],
        snapshot.legacy_rollback_entries[0],
        snapshot.legacy_rollback_entries[1],
        snapshot.factored_read_errors[0],
        snapshot.factored_read_errors[1],
    );
}

fn write_proof_tally(file: &mut File, snapshot: ReplaySoakTelemetrySnapshot) {
    let _ = writeln!(
        file,
        concat!(
            "CPK_SOAK_TALLY version={} ",
            "terminal_organic_project_preflight={} ",
            "terminal_organic_project_supports={} ",
            "terminal_organic_project_evaluation={} ",
            "terminal_organic_route_preflight={} ",
            "terminal_organic_route_parents={} ",
            "terminal_organic_route_batch={} ",
            "terminal_injected_project_preflight={} ",
            "terminal_injected_project_supports={} ",
            "terminal_injected_project_evaluation={} ",
            "terminal_injected_route_preflight={} ",
            "terminal_injected_route_parents={} ",
            "terminal_injected_route_batch={}"
        ),
        CPK_SOAK_TELEMETRY_VERSION,
        snapshot.proof_terminal_failures[0],
        snapshot.proof_terminal_failures[1],
        snapshot.proof_terminal_failures[2],
        snapshot.proof_terminal_failures[3],
        snapshot.proof_terminal_failures[4],
        snapshot.proof_terminal_failures[5],
        snapshot.proof_terminal_failures[6],
        snapshot.proof_terminal_failures[7],
        snapshot.proof_terminal_failures[8],
        snapshot.proof_terminal_failures[9],
        snapshot.proof_terminal_failures[10],
        snapshot.proof_terminal_failures[11],
    );
}

fn metadata(name: &str) -> String {
    std::env::var(name)
        .unwrap_or_else(|_| "missing".to_string())
        .split_whitespace()
        .collect::<Vec<_>>()
        .join("_")
}

fn build_profile() -> &'static str {
    if cfg!(debug_assertions) { "debug" } else { "release" }
}

fn generalize_compact_cache_mode() -> &'static str {
    match std::env::var("YULANG_GENERALIZE_COMPACT_CACHE") {
        Ok(value) if value.is_empty() || value == "0" => "off",
        Ok(_) => "on",
        Err(_) => "default-on",
    }
}
