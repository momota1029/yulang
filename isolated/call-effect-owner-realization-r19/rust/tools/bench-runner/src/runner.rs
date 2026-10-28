use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail, ensure};
use chrono::Utc;

use crate::cli::Cli;
use crate::corpus::{Corpus, StdMode, Workload};
use crate::identity::{Identities, canonical_directory, canonical_file};
use crate::measurement::{
    Execution, SubjectCommand, ensure_success, infer_std_root, normalized_stdout,
};
use crate::report::{
    Availability, BenchmarkReport, CorrectnessResult, MeasurementSample, ProtocolInfo, RunInfo,
    SourceIdentity, SuiteInfo, WorkCounts, WorkloadResult, WorkloadSummary,
};
use crate::statistics::{aggregate, summarize, summarize_available};

pub fn run(cli: &Cli) -> Result<BenchmarkReport> {
    let started_at = Utc::now();
    let subject_binary = canonical_file(&cli.subject_binary, "subject binary")?;
    let corpus = Corpus::load(&cli.corpus, &cli.only)?;
    let needs_std = corpus
        .workloads
        .iter()
        .any(|workload| workload.case.std == StdMode::Repo);
    let std_root = resolve_std_root(cli.subject_std_root.as_deref(), &subject_binary, needs_std)?;
    let identities = Identities::collect(&subject_binary, std_root.as_deref())?;
    let working_directory = current_directory();
    let cache = TemporaryDirectory::create("yulang-bench-cache")?;
    let subject = SubjectCommand::new(subject_binary, std_root, cache.path().to_path_buf());

    let mut results = Vec::with_capacity(corpus.workloads.len());
    for workload in &corpus.workloads {
        eprintln!("preflight: {}", workload.case.workload_id);
        let preflight = subject.execute(workload)?;
        validate_output(workload, "correctness preflight", &preflight)?;
        let actual_root = normalized_stdout(&preflight).to_owned();

        eprintln!(
            "benchmark: {} ({} warmup, {} measurement)",
            workload.case.workload_id, cli.warmup_iterations, cli.measurement_iterations
        );
        for iteration in 1..=cli.warmup_iterations {
            let execution = subject.execute(workload)?;
            validate_output(
                workload,
                &format!("warmup iteration {iteration}"),
                &execution,
            )?;
        }

        let mut samples = Vec::with_capacity(cli.measurement_iterations as usize);
        for iteration in 1..=cli.measurement_iterations {
            let execution = subject.execute(workload)?;
            validate_output(
                workload,
                &format!("measurement iteration {iteration}"),
                &execution,
            )?;
            samples.push(sample(iteration, &execution));
        }
        results.push(workload_result(&corpus, workload, actual_root, samples)?);
    }

    let aggregates = aggregate(&results);
    let finished_at = Utc::now();
    Ok(BenchmarkReport {
        run: RunInfo {
            id: format!(
                "{}-{}",
                started_at.format("%Y%m%dT%H%M%S%.9fZ"),
                std::process::id()
            ),
            started_at,
            finished_at,
            status: "complete",
        },
        suite: SuiteInfo {
            result_schema_version: 1,
            benchmark: corpus.manifest.benchmark,
            benchmark_version: corpus.manifest.benchmark_version,
            corpus_revision: corpus.manifest.corpus_revision,
            frozen_at: corpus.manifest.frozen_at,
            corpus_path: corpus.root.display().to_string(),
            corpus_sha256: corpus.sha256,
            corpus_hash_algorithm: "sha256(length-prefixed relative path and bytes, lexicographic)",
            workload_count: corpus.manifest.workload_count,
            selected_workload_count: results.len(),
            oracle: corpus.manifest.oracle,
        },
        runner: identities.runner,
        subject: identities.subject,
        machine: identities.machine,
        protocol: ProtocolInfo {
            correctness_preflight_iterations: 1,
            warmup_iterations: cli.warmup_iterations,
            measurement_iterations: cli.measurement_iterations,
            process_isolation: "fresh subject process per iteration",
            workload_order: "lexicographic workload_id",
            stdout_comparison: "UTF-8 lossy decode, strip `run roots [...]` envelope, trim, exact match",
            subject_cache: "isolated per runner invocation; preflight and warmup populate cache",
            subject_command: vec![
                "<subject-binary>".to_owned(),
                "<--no-prelude | --std-root PATH>".to_owned(),
                "run".to_owned(),
                "--print-roots".to_owned(),
                "<main.yu>".to_owned(),
            ],
            working_directory,
        },
        results,
        aggregates,
    })
}

fn resolve_std_root(
    explicit: Option<&Path>,
    subject_binary: &Path,
    required: bool,
) -> Result<Option<PathBuf>> {
    if let Some(path) = explicit {
        return canonical_directory(path, "subject standard-library root").map(Some);
    }
    if !required {
        return Ok(None);
    }
    if let Some(path) = infer_std_root(subject_binary) {
        return canonical_directory(&path, "inferred subject standard-library root").map(Some);
    }
    bail!(
        "selected workloads include std = \"repo\", but no standard-library root could be inferred from {}; pass --subject-std-root",
        subject_binary.display()
    )
}

fn validate_output(workload: &Workload, phase: &str, execution: &Execution) -> Result<()> {
    ensure_success(&workload.case.workload_id, phase, execution)?;
    let actual = normalized_stdout(execution);
    ensure!(
        actual == workload.case.expected_root,
        "{phase} output mismatch for {}: expected {:?}, got {:?}; stderr: {:?}",
        workload.case.workload_id,
        workload.case.expected_root,
        actual,
        execution.stderr.trim()
    );
    Ok(())
}

fn sample(iteration: u32, execution: &Execution) -> MeasurementSample {
    const UNAVAILABLE: &str = "per-process resource usage is unavailable on this platform";
    MeasurementSample {
        iteration,
        wall_time_ns: execution.wall_time_ns,
        user_cpu_time_ns: match &execution.resources {
            Some(usage) => Availability::available(usage.user_cpu_time_ns),
            None => Availability::unavailable(UNAVAILABLE),
        },
        system_cpu_time_ns: match &execution.resources {
            Some(usage) => Availability::available(usage.system_cpu_time_ns),
            None => Availability::unavailable(UNAVAILABLE),
        },
        peak_rss_bytes: match &execution.resources {
            Some(usage) => Availability::available(usage.peak_rss_bytes),
            None => Availability::unavailable(UNAVAILABLE),
        },
    }
}

fn workload_result(
    corpus: &Corpus,
    workload: &Workload,
    actual_root: String,
    samples: Vec<MeasurementSample>,
) -> Result<WorkloadResult> {
    let wall_times: Vec<_> = samples.iter().map(|sample| sample.wall_time_ns).collect();
    let parameters = workload
        .case
        .parameters
        .iter()
        .map(|(name, value)| {
            serde_json::to_value(value)
                .map(|value| (name.clone(), value))
                .with_context(|| format!("failed to serialize parameter {name}"))
        })
        .collect::<Result<BTreeMap<_, _>>>()?;
    let source_path = workload
        .source_path
        .strip_prefix(&corpus.root)
        .context("workload source escaped corpus root")?;

    Ok(WorkloadResult {
        workload_id: workload.case.workload_id.clone(),
        category: workload.case.category.clone(),
        subsets: workload.case.subsets.clone(),
        std: workload.case.std,
        parameters,
        source: SourceIdentity {
            path: slash_path(source_path),
            sha256: workload.source_sha256.clone(),
            verification: "matched corpus.toml source_sha256",
        },
        correctness: CorrectnessResult {
            status: "passed",
            expected_root: workload.case.expected_root.clone(),
            actual_root,
        },
        summary: WorkloadSummary {
            wall_time_ns: summarize(&wall_times),
            user_cpu_time_ns: summarize_available(
                samples.iter().map(|sample| sample.user_cpu_time_ns.value),
            ),
            system_cpu_time_ns: summarize_available(
                samples.iter().map(|sample| sample.system_cpu_time_ns.value),
            ),
            peak_rss_bytes: summarize_available(
                samples.iter().map(|sample| sample.peak_rss_bytes.value),
            ),
        },
        samples,
        work_counts: WorkCounts::yulang2_unsupported(),
    })
}

fn current_directory() -> Availability<String> {
    match std::env::current_dir().and_then(|path| path.canonicalize()) {
        Ok(path) => Availability::available(path.display().to_string()),
        Err(error) => Availability::unavailable(error.to_string()),
    }
}

fn slash_path(path: &Path) -> String {
    path.iter()
        .map(|component| component.to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

struct TemporaryDirectory {
    path: PathBuf,
}

impl TemporaryDirectory {
    fn create(prefix: &str) -> Result<Self> {
        let base = std::env::temp_dir();
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .context("system clock is before the Unix epoch")?
            .as_nanos();
        for attempt in 0..100u32 {
            let path = base.join(format!("{prefix}-{}-{nonce}-{attempt}", std::process::id()));
            match std::fs::create_dir(&path) {
                Ok(()) => return Ok(Self { path }),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(error)
                        .with_context(|| format!("failed to create {}", path.display()));
                }
            }
        }
        bail!("failed to choose a unique temporary cache directory");
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TemporaryDirectory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}
