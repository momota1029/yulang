use std::collections::BTreeMap;

use chrono::{DateTime, Utc};
use serde::Serialize;

use crate::corpus::{OracleIdentity, StdMode};

#[derive(Debug, Serialize)]
pub struct BenchmarkReport {
    pub run: RunInfo,
    pub suite: SuiteInfo,
    pub runner: RunnerIdentity,
    pub subject: SubjectIdentity,
    pub machine: MachineIdentity,
    pub protocol: ProtocolInfo,
    pub results: Vec<WorkloadResult>,
    pub aggregates: Aggregates,
}

#[derive(Debug, Serialize)]
pub struct RunInfo {
    pub id: String,
    pub started_at: DateTime<Utc>,
    pub finished_at: DateTime<Utc>,
    pub status: &'static str,
}

#[derive(Debug, Serialize)]
pub struct SuiteInfo {
    pub result_schema_version: u32,
    pub benchmark: String,
    pub benchmark_version: u32,
    pub corpus_revision: u32,
    pub frozen_at: String,
    pub corpus_path: String,
    pub corpus_sha256: String,
    pub corpus_hash_algorithm: &'static str,
    pub workload_count: usize,
    pub selected_workload_count: usize,
    pub oracle: OracleIdentity,
}

#[derive(Debug, Serialize)]
pub struct RunnerIdentity {
    pub name: &'static str,
    pub version: &'static str,
    pub binary_path: Availability<String>,
    pub binary_sha256: Availability<String>,
    pub git_commit: Availability<String>,
}

#[derive(Debug, Serialize)]
pub struct SubjectIdentity {
    pub kind: &'static str,
    pub binary_path: String,
    pub binary_sha256: String,
    pub binary_size_bytes: u64,
    pub std_root: Availability<String>,
}

#[derive(Debug, Serialize)]
pub struct MachineIdentity {
    pub collected_at: DateTime<Utc>,
    pub hostname: Availability<String>,
    pub operating_system: Availability<String>,
    pub kernel_release: Availability<String>,
    pub architecture: Availability<String>,
    pub cpu_model: Availability<String>,
    pub logical_cpus: Availability<usize>,
    pub memory_total_bytes: Availability<u64>,
    pub rustc_version: Availability<String>,
}

#[derive(Debug, Serialize)]
pub struct ProtocolInfo {
    pub correctness_preflight_iterations: u32,
    pub warmup_iterations: u32,
    pub measurement_iterations: u32,
    pub process_isolation: &'static str,
    pub workload_order: &'static str,
    pub stdout_comparison: &'static str,
    pub subject_cache: &'static str,
    pub subject_command: Vec<String>,
    pub working_directory: Availability<String>,
}

#[derive(Debug, Serialize)]
pub struct WorkloadResult {
    pub workload_id: String,
    pub category: String,
    pub subsets: Vec<String>,
    pub std: StdMode,
    pub parameters: BTreeMap<String, serde_json::Value>,
    pub source: SourceIdentity,
    pub correctness: CorrectnessResult,
    pub samples: Vec<MeasurementSample>,
    pub summary: WorkloadSummary,
    pub work_counts: WorkCounts,
}

#[derive(Debug, Serialize)]
pub struct SourceIdentity {
    pub path: String,
    pub sha256: String,
    pub verification: &'static str,
}

#[derive(Debug, Serialize)]
pub struct CorrectnessResult {
    pub status: &'static str,
    pub expected_root: String,
    pub actual_root: String,
}

#[derive(Debug, Serialize)]
pub struct MeasurementSample {
    pub iteration: u32,
    pub wall_time_ns: u64,
    pub user_cpu_time_ns: Availability<u64>,
    pub system_cpu_time_ns: Availability<u64>,
    pub peak_rss_bytes: Availability<u64>,
}

#[derive(Debug, Serialize)]
pub struct WorkloadSummary {
    pub wall_time_ns: DistributionSummary,
    pub user_cpu_time_ns: Availability<DistributionSummary>,
    pub system_cpu_time_ns: Availability<DistributionSummary>,
    pub peak_rss_bytes: Availability<DistributionSummary>,
}

#[derive(Debug, Clone, Serialize)]
pub struct DistributionSummary {
    pub sample_count: usize,
    pub min: u64,
    pub median: f64,
    pub mad: f64,
    pub p95: u64,
    pub max: u64,
}

#[derive(Debug, Serialize)]
pub struct WorkCounts {
    pub canonical_instructions: Availability<u64>,
    pub allocation_bytes: Availability<u64>,
    pub continuation_capture_bytes: Availability<u64>,
    pub continuation_clone_bytes: Availability<u64>,
}

impl WorkCounts {
    pub fn yulang2_unsupported() -> Self {
        const REASON: &str = "yulang2 does not expose a canonical instruction/allocation counter";
        Self {
            canonical_instructions: Availability::unsupported(REASON),
            allocation_bytes: Availability::unsupported(REASON),
            continuation_capture_bytes: Availability::unsupported(REASON),
            continuation_clone_bytes: Availability::unsupported(REASON),
        }
    }
}

#[derive(Debug, Serialize)]
pub struct Aggregates {
    pub workload_count: usize,
    pub wall_time: AggregateWallTime,
    pub categories: BTreeMap<String, AggregateGroup>,
    pub subsets: BTreeMap<String, AggregateGroup>,
}

#[derive(Debug, Serialize)]
pub struct AggregateWallTime {
    pub median_of_workload_medians_ns: f64,
    pub geometric_mean_of_workload_medians_ns: f64,
}

#[derive(Debug, Serialize)]
pub struct AggregateGroup {
    pub workload_count: usize,
    pub geometric_mean_of_medians_ns: f64,
}

#[derive(Debug, Clone, Serialize)]
pub struct Availability<T> {
    pub status: &'static str,
    pub value: Option<T>,
    pub reason: Option<String>,
}

impl<T> Availability<T> {
    pub fn available(value: T) -> Self {
        Self {
            status: "available",
            value: Some(value),
            reason: None,
        }
    }

    pub fn unavailable(reason: impl Into<String>) -> Self {
        Self {
            status: "unavailable",
            value: None,
            reason: Some(reason.into()),
        }
    }

    pub fn unsupported(reason: impl Into<String>) -> Self {
        Self {
            status: "unsupported",
            value: None,
            reason: Some(reason.into()),
        }
    }
}
