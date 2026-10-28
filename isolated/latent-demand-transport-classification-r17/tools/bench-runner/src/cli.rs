use std::path::PathBuf;

use anyhow::{Result, bail};
use clap::Parser;

#[derive(Debug, Parser)]
#[command(
    name = "bench-runner",
    version,
    about = "Run the frozen Yulang runtime benchmark corpus"
)]
pub struct Cli {
    /// Yulang CLI executable under measurement.
    #[arg(long, value_name = "PATH")]
    pub subject_binary: PathBuf,

    /// Frozen runtime benchmark corpus.
    #[arg(long, value_name = "DIR", default_value = "tests/perf/runtime/v0")]
    pub corpus: PathBuf,

    /// Standard-library root used by workloads whose case.toml says std = "repo".
    #[arg(long, value_name = "DIR")]
    pub subject_std_root: Option<PathBuf>,

    /// Run only this workload id. May be repeated.
    #[arg(long, value_name = "WORKLOAD_ID", action = clap::ArgAction::Append)]
    pub only: Vec<String>,

    /// Warmup process executions per workload, after correctness preflight.
    #[arg(long, default_value_t = 3)]
    pub warmup_iterations: u32,

    /// Recorded process executions per workload.
    #[arg(long, default_value_t = 20)]
    pub measurement_iterations: u32,

    /// Write JSON to this file instead of standard output.
    #[arg(long, value_name = "PATH")]
    pub output: Option<PathBuf>,
}

impl Cli {
    pub fn validate(&self) -> Result<()> {
        if self.measurement_iterations == 0 {
            bail!("--measurement-iterations must be greater than zero");
        }
        Ok(())
    }
}
