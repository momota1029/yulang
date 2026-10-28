use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::Instant;

use anyhow::{Context, Result, bail};

use crate::corpus::{StdMode, Workload};

pub struct SubjectCommand {
    binary: PathBuf,
    std_root: Option<PathBuf>,
    cache_root: PathBuf,
}

impl SubjectCommand {
    pub fn new(binary: PathBuf, std_root: Option<PathBuf>, cache_root: PathBuf) -> Self {
        Self {
            binary,
            std_root,
            cache_root,
        }
    }

    pub fn execute(&self, workload: &Workload) -> Result<Execution> {
        let mut command = Command::new(&self.binary);
        match workload.case.std {
            StdMode::None => {
                command.arg("--no-prelude");
            }
            StdMode::Repo => {
                let Some(std_root) = &self.std_root else {
                    bail!(
                        "workload {} requires std = \"repo\"; pass --subject-std-root",
                        workload.case.workload_id
                    );
                };
                command.arg("--std-root").arg(std_root);
            }
        }
        command
            .args(["run", "--print-roots"])
            .arg(&workload.source_path)
            .env("YULANG_CACHE_DIR", &self.cache_root)
            .stdin(Stdio::null());
        execute_command(&mut command)
            .with_context(|| format!("failed to execute workload {}", workload.case.workload_id))
    }
}

pub struct Execution {
    pub status: ExitStatus,
    pub stdout: String,
    pub stderr: String,
    pub wall_time_ns: u64,
    pub resources: Option<ResourceUsage>,
}

pub struct ResourceUsage {
    pub user_cpu_time_ns: u64,
    pub system_cpu_time_ns: u64,
    pub peak_rss_bytes: u64,
}

#[cfg(target_os = "linux")]
fn execute_command(command: &mut Command) -> Result<Execution> {
    use std::mem::MaybeUninit;
    use std::os::unix::process::ExitStatusExt;

    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    let started = Instant::now();
    let mut child = command.spawn().context("failed to spawn subject process")?;
    let stdout = child
        .stdout
        .take()
        .context("failed to capture subject stdout")?;
    let stderr = child
        .stderr
        .take()
        .context("failed to capture subject stderr")?;
    let stdout_reader = std::thread::spawn(move || read_all(stdout));
    let stderr_reader = std::thread::spawn(move || read_all(stderr));

    let mut raw_status = 0;
    let mut raw_usage = MaybeUninit::<libc::rusage>::zeroed();
    loop {
        // SAFETY: pid belongs to the live child, status and rusage point to valid writable memory,
        // and EINTR is retried. The child pipes are drained concurrently to avoid blocking it.
        let result = unsafe {
            libc::wait4(
                child.id() as libc::pid_t,
                &mut raw_status,
                0,
                raw_usage.as_mut_ptr(),
            )
        };
        if result >= 0 {
            break;
        }
        let error = io::Error::last_os_error();
        if error.raw_os_error() == Some(libc::EINTR) {
            continue;
        }
        let _ = child.kill();
        let _ = child.wait();
        return Err(error).context("wait4 failed for subject process");
    }
    let wall_time_ns = nanos_u64(started.elapsed().as_nanos());
    // SAFETY: wait4 returned successfully and initialized rusage.
    let usage = unsafe { raw_usage.assume_init() };
    let stdout = join_reader(stdout_reader, "stdout")?;
    let stderr = join_reader(stderr_reader, "stderr")?;

    Ok(Execution {
        status: ExitStatus::from_raw(raw_status),
        stdout: String::from_utf8_lossy(&stdout).into_owned(),
        stderr: String::from_utf8_lossy(&stderr).into_owned(),
        wall_time_ns,
        resources: Some(ResourceUsage {
            user_cpu_time_ns: timeval_ns(usage.ru_utime),
            system_cpu_time_ns: timeval_ns(usage.ru_stime),
            peak_rss_bytes: (usage.ru_maxrss.max(0) as u64).saturating_mul(1024),
        }),
    })
}

#[cfg(not(target_os = "linux"))]
fn execute_command(command: &mut Command) -> Result<Execution> {
    let started = Instant::now();
    let output = command
        .output()
        .context("failed to execute subject process")?;
    Ok(Execution {
        status: output.status,
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        wall_time_ns: nanos_u64(started.elapsed().as_nanos()),
        resources: None,
    })
}

fn read_all(mut input: impl Read) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    input.read_to_end(&mut bytes)?;
    Ok(bytes)
}

fn join_reader(
    reader: std::thread::JoinHandle<io::Result<Vec<u8>>>,
    stream: &str,
) -> Result<Vec<u8>> {
    reader
        .join()
        .map_err(|_| anyhow::anyhow!("{stream} reader thread panicked"))?
        .with_context(|| format!("failed to read subject {stream}"))
}

#[cfg(target_os = "linux")]
fn timeval_ns(value: libc::timeval) -> u64 {
    let seconds = value.tv_sec.max(0) as u64;
    let microseconds = value.tv_usec.max(0) as u64;
    seconds
        .saturating_mul(1_000_000_000)
        .saturating_add(microseconds.saturating_mul(1_000))
}

fn nanos_u64(value: u128) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

pub fn normalized_stdout(execution: &Execution) -> &str {
    let stdout = execution.stdout.trim();
    stdout
        .strip_prefix("run roots [")
        .and_then(|roots| roots.strip_suffix(']'))
        .map(str::trim)
        .unwrap_or(stdout)
}

pub fn ensure_success(workload_id: &str, phase: &str, execution: &Execution) -> Result<()> {
    if execution.status.success() {
        return Ok(());
    }
    bail!(
        "{phase} failed for {workload_id} with {}\nstdout:\n{}\nstderr:\n{}",
        execution.status,
        execution.stdout.trim(),
        execution.stderr.trim()
    )
}

pub fn infer_std_root(subject_binary: &Path) -> Option<PathBuf> {
    subject_binary
        .ancestors()
        .skip(1)
        .take(5)
        .find_map(|ancestor| {
            let candidate = ancestor.join("lib");
            candidate.join("std.yu").is_file().then_some(candidate)
        })
}

#[cfg(test)]
mod tests {
    use std::os::unix::process::ExitStatusExt;

    use super::{Execution, normalized_stdout};

    #[test]
    fn extracts_yulang2_run_roots_envelope() {
        let execution = Execution {
            status: std::process::ExitStatus::from_raw(0),
            stdout: "run roots [(42, [1, 2])]\n".to_owned(),
            stderr: String::new(),
            wall_time_ns: 0,
            resources: None,
        };
        assert_eq!(normalized_stdout(&execution), "(42, [1, 2])");
    }
}
