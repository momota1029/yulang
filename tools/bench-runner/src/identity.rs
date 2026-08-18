use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, ensure};
use chrono::Utc;

use crate::digest::sha256_file;
use crate::report::{Availability, MachineIdentity, RunnerIdentity, SubjectIdentity};

pub struct Identities {
    pub runner: RunnerIdentity,
    pub subject: SubjectIdentity,
    pub machine: MachineIdentity,
}

impl Identities {
    pub fn collect(subject_binary: &Path, std_root: Option<&Path>) -> Result<Self> {
        Ok(Self {
            runner: collect_runner_identity(),
            subject: collect_subject_identity(subject_binary, std_root)?,
            machine: collect_machine_identity(),
        })
    }
}

pub fn canonical_file(path: &Path, label: &str) -> Result<PathBuf> {
    let path = path
        .canonicalize()
        .with_context(|| format!("failed to resolve {label} {}", path.display()))?;
    ensure!(path.is_file(), "{label} is not a file: {}", path.display());
    Ok(path)
}

pub fn canonical_directory(path: &Path, label: &str) -> Result<PathBuf> {
    let path = path
        .canonicalize()
        .with_context(|| format!("failed to resolve {label} {}", path.display()))?;
    ensure!(
        path.is_dir(),
        "{label} is not a directory: {}",
        path.display()
    );
    Ok(path)
}

fn collect_runner_identity() -> RunnerIdentity {
    let current_exe = std::env::current_exe()
        .and_then(|path| path.canonicalize())
        .map_err(|error| error.to_string());
    let binary_path = match &current_exe {
        Ok(path) => Availability::available(path.display().to_string()),
        Err(reason) => Availability::unavailable(reason.clone()),
    };
    let binary_sha256 = match &current_exe {
        Ok(path) => match sha256_file(path) {
            Ok(hash) => Availability::available(hash),
            Err(error) => Availability::unavailable(error.to_string()),
        },
        Err(reason) => Availability::unavailable(reason.clone()),
    };

    RunnerIdentity {
        name: "bench-runner",
        version: env!("CARGO_PKG_VERSION"),
        binary_path,
        binary_sha256,
        git_commit: command_value("git", &["rev-parse", "HEAD"]),
    }
}

fn collect_subject_identity(binary: &Path, std_root: Option<&Path>) -> Result<SubjectIdentity> {
    let metadata = fs::metadata(binary)
        .with_context(|| format!("failed to inspect subject binary {}", binary.display()))?;
    Ok(SubjectIdentity {
        kind: "yulang_cli",
        binary_path: binary.display().to_string(),
        binary_sha256: sha256_file(binary)?,
        binary_size_bytes: metadata.len(),
        std_root: match std_root {
            Some(path) => Availability::available(path.display().to_string()),
            None => Availability::unavailable("not configured for the selected workloads"),
        },
    })
}

fn collect_machine_identity() -> MachineIdentity {
    MachineIdentity {
        collected_at: Utc::now(),
        hostname: read_trimmed("/proc/sys/kernel/hostname"),
        operating_system: command_value("uname", &["-s"]),
        kernel_release: command_value("uname", &["-r"]),
        architecture: command_value("uname", &["-m"]),
        cpu_model: cpu_model(),
        logical_cpus: match std::thread::available_parallelism() {
            Ok(value) => Availability::available(value.get()),
            Err(error) => Availability::unavailable(error.to_string()),
        },
        memory_total_bytes: memory_total_bytes(),
        rustc_version: command_value("rustc", &["--version", "--verbose"]),
    }
}

fn command_value(program: &str, arguments: &[&str]) -> Availability<String> {
    match Command::new(program).args(arguments).output() {
        Ok(output) if output.status.success() => {
            let value = String::from_utf8_lossy(&output.stdout).trim().to_owned();
            if value.is_empty() {
                Availability::unavailable(format!("{program} returned empty output"))
            } else {
                Availability::available(value)
            }
        }
        Ok(output) => Availability::unavailable(format!(
            "{program} exited with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        )),
        Err(error) => Availability::unavailable(format!("failed to run {program}: {error}")),
    }
}

fn read_trimmed(path: &str) -> Availability<String> {
    match fs::read_to_string(path) {
        Ok(value) if !value.trim().is_empty() => Availability::available(value.trim().to_owned()),
        Ok(_) => Availability::unavailable(format!("{path} was empty")),
        Err(error) => Availability::unavailable(format!("failed to read {path}: {error}")),
    }
}

fn cpu_model() -> Availability<String> {
    let cpuinfo = match fs::read_to_string("/proc/cpuinfo") {
        Ok(value) => value,
        Err(error) => {
            return Availability::unavailable(format!("failed to read /proc/cpuinfo: {error}"));
        }
    };
    for key in ["model name", "Hardware", "Processor"] {
        if let Some(value) = cpuinfo.lines().find_map(|line| {
            let (candidate, value) = line.split_once(':')?;
            (candidate.trim() == key && !value.trim().is_empty()).then(|| value.trim().to_owned())
        }) {
            return Availability::available(value);
        }
    }
    Availability::unavailable("/proc/cpuinfo has no recognized CPU model field")
}

fn memory_total_bytes() -> Availability<u64> {
    let meminfo = match fs::read_to_string("/proc/meminfo") {
        Ok(value) => value,
        Err(error) => {
            return Availability::unavailable(format!("failed to read /proc/meminfo: {error}"));
        }
    };
    let Some(line) = meminfo.lines().find(|line| line.starts_with("MemTotal:")) else {
        return Availability::unavailable("/proc/meminfo has no MemTotal field");
    };
    let Some(kibibytes) = line.split_whitespace().nth(1) else {
        return Availability::unavailable("MemTotal has no numeric value");
    };
    match kibibytes
        .parse::<u64>()
        .ok()
        .and_then(|value| value.checked_mul(1024))
    {
        Some(bytes) => Availability::available(bytes),
        None => Availability::unavailable("MemTotal is not a valid KiB value"),
    }
}
