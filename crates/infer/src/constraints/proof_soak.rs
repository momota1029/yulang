//! Opt-in process telemetry for the CPK proof-kernel soak gate.
//!
//! Ordinary compilation pays one cached environment lookup per constraint-machine construction.
//! Counters and the file sink are touched only on terminal proof-failure paths.

use std::fs::{File, OpenOptions};
use std::io::Write;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

use super::proof::ProofOperation;
use super::ProofFailure;

pub(crate) const CPK_SOAK_TELEMETRY_VERSION: u32 = 6;
const CPK_SOAK_TELEMETRY_SCHEMA: &str = "cpk-only";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(any(test, feature = "test-support")), allow(dead_code))]
pub(crate) enum ProofSoakEventOrigin {
    Organic,
    IntentionalTestInjection,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct ProofSoakTelemetrySnapshot {
    proof_terminal_failures: [u64; 18],
}

impl ProofSoakTelemetrySnapshot {
    #[cfg(any(test, feature = "test-support"))]
    pub(crate) fn proof_terminal_failures(
        self,
        origin: ProofSoakEventOrigin,
        operation: ProofOperation,
    ) -> u64 {
        self.proof_terminal_failures[proof_terminal_index(origin, operation)]
    }

    #[cfg(any(test, feature = "test-support"))]
    pub(crate) fn total_for_origin(self, origin: ProofSoakEventOrigin) -> u64 {
        self.proof_terminal_failures[origin_index(origin) * 9..origin_index(origin) * 9 + 9]
            .iter()
            .sum::<u64>()
    }
}

static PROOF_TERMINAL_FAILURES: [AtomicU64; 18] = [const { AtomicU64::new(0) }; 18];
static PROOF_TELEMETRY_SINK: OnceLock<Option<Mutex<File>>> = OnceLock::new();

#[cfg(any(test, feature = "test-support"))]
std::thread_local! {
    static INTENTIONAL_TEST_INJECTION_DEPTH: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static TEST_CAPTURE: std::cell::RefCell<Option<ProofSoakTelemetrySnapshot>> = const {
        std::cell::RefCell::new(None)
    };
}

pub(crate) fn ensure_proof_soak_telemetry_header() {
    let _ = proof_telemetry_sink();
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

pub(crate) fn proof_soak_telemetry_snapshot() -> ProofSoakTelemetrySnapshot {
    ProofSoakTelemetrySnapshot {
        proof_terminal_failures: std::array::from_fn(|index| {
            PROOF_TERMINAL_FAILURES[index].load(Ordering::Relaxed)
        }),
    }
}

#[cfg(any(test, feature = "test-support"))]
pub(crate) fn with_intentional_proof_soak_test_injection<T>(run: impl FnOnce() -> T) -> T {
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

#[cfg(any(test, feature = "test-support"))]
pub(crate) fn capture_proof_soak_test_events<T>(
    run: impl FnOnce() -> T,
) -> (T, ProofSoakTelemetrySnapshot) {
    TEST_CAPTURE.with(|capture| {
        assert!(capture.borrow().is_none(), "nested CPK proof-soak capture");
        *capture.borrow_mut() = Some(ProofSoakTelemetrySnapshot::default());
    });
    let output = run();
    let snapshot = TEST_CAPTURE.with(|capture| {
        capture
            .borrow_mut()
            .take()
            .expect("CPK proof-soak capture must remain installed")
    });
    (output, snapshot)
}

fn current_event_origin() -> ProofSoakEventOrigin {
    #[cfg(any(test, feature = "test-support"))]
    {
        if INTENTIONAL_TEST_INJECTION_DEPTH.with(|depth| depth.get() > 0) {
            return ProofSoakEventOrigin::IntentionalTestInjection;
        }
    }
    ProofSoakEventOrigin::Organic
}

fn origin_index(origin: ProofSoakEventOrigin) -> usize {
    match origin {
        ProofSoakEventOrigin::Organic => 0,
        ProofSoakEventOrigin::IntentionalTestInjection => 1,
    }
}

fn proof_operation_index(operation: ProofOperation) -> usize {
    match operation {
        ProofOperation::AdmitOriginalClaim => 6,
        ProofOperation::AdmitDerivedClaim => 7,
        ProofOperation::UpdateClaimLifecycle => 8,
        ProofOperation::ProjectLowerPreflight => 0,
        ProofOperation::ProjectLowerSupportCollection => 1,
        ProofOperation::ProjectLowerEvaluation => 2,
        ProofOperation::PrepareReplayRoutePreflight => 3,
        ProofOperation::PrepareReplayRouteParentCollection => 4,
        ProofOperation::PrepareReplayRouteBatch => 5,
    }
}

fn proof_terminal_index(origin: ProofSoakEventOrigin, operation: ProofOperation) -> usize {
    origin_index(origin) * 9 + proof_operation_index(operation)
}

fn update_test_capture(update: impl FnOnce(&mut ProofSoakTelemetrySnapshot)) {
    #[cfg(any(test, feature = "test-support"))]
    TEST_CAPTURE.with(|capture| {
        if let Some(snapshot) = capture.borrow_mut().as_mut() {
            update(snapshot);
        }
    });
    #[cfg(not(any(test, feature = "test-support")))]
    let _ = update;
}

fn proof_telemetry_sink() -> Option<&'static Mutex<File>> {
    PROOF_TELEMETRY_SINK
        .get_or_init(|| {
            let path = std::env::var_os("YULANG_CPK_SOAK_TELEMETRY_PATH")?;
            match OpenOptions::new().create(true).append(true).open(&path) {
                Ok(mut file) => {
                    let _ = writeln!(
                        file,
                        "CPK_SOAK_HEADER version={} schema={} pid={} commit={} build_profile={} workload={} generalize_compact_cache={} source_cache={}",
                        CPK_SOAK_TELEMETRY_VERSION,
                        CPK_SOAK_TELEMETRY_SCHEMA,
                        std::process::id(),
                        metadata("YULANG_CPK_SOAK_COMMIT"),
                        build_profile(),
                        metadata("YULANG_CPK_SOAK_WORKLOAD"),
                        generalize_compact_cache_mode(),
                        metadata("YULANG_CPK_SOAK_SOURCE_CACHE_MODE"),
                    );
                    write_proof_tally(&mut file, proof_soak_telemetry_snapshot());
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

fn emit_proof_event(
    event: &str,
    origin: ProofSoakEventOrigin,
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
    write_proof_tally(&mut file, proof_soak_telemetry_snapshot());
}

fn write_proof_tally(file: &mut File, snapshot: ProofSoakTelemetrySnapshot) {
    let _ = writeln!(
        file,
        concat!(
            "CPK_SOAK_TALLY version={} schema={} ",
            "terminal_organic_project_preflight={} ",
            "terminal_organic_project_supports={} ",
            "terminal_organic_project_evaluation={} ",
            "terminal_organic_route_preflight={} ",
            "terminal_organic_route_parents={} ",
            "terminal_organic_route_batch={} ",
            "terminal_organic_claim_admission={} ",
            "terminal_organic_derived_claim_admission={} ",
            "terminal_organic_claim_lifecycle={} ",
            "terminal_injected_project_preflight={} ",
            "terminal_injected_project_supports={} ",
            "terminal_injected_project_evaluation={} ",
            "terminal_injected_route_preflight={} ",
            "terminal_injected_route_parents={} ",
            "terminal_injected_route_batch={} ",
            "terminal_injected_claim_admission={} ",
            "terminal_injected_derived_claim_admission={} ",
            "terminal_injected_claim_lifecycle={}"
        ),
        CPK_SOAK_TELEMETRY_VERSION,
        CPK_SOAK_TELEMETRY_SCHEMA,
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
        snapshot.proof_terminal_failures[12],
        snapshot.proof_terminal_failures[13],
        snapshot.proof_terminal_failures[14],
        snapshot.proof_terminal_failures[15],
        snapshot.proof_terminal_failures[16],
        snapshot.proof_terminal_failures[17],
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
