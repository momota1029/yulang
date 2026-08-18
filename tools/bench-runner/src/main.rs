use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::process::ExitCode;

use anyhow::{Context, Result};
use clap::Parser;

use crate::cli::Cli;

fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("bench-runner: {error:#}");
            ExitCode::FAILURE
        }
    }
}

fn run(cli: Cli) -> Result<()> {
    cli.validate()?;
    let report = runner::run(&cli)?;

    match &cli.output {
        Some(path) => {
            let file = File::create(path)
                .with_context(|| format!("failed to create output file {}", path.display()))?;
            write_json(BufWriter::new(file), &report)
        }
        None => write_json(BufWriter::new(io::stdout().lock()), &report),
    }
}

fn write_json(mut writer: impl Write, report: &report::BenchmarkReport) -> Result<()> {
    serde_json::to_writer_pretty(&mut writer, report).context("failed to serialize report")?;
    writer.write_all(b"\n").context("failed to finish report")?;
    writer.flush().context("failed to flush report")
}

mod cli;
mod corpus;
mod digest;
mod identity;
mod measurement;
mod report;
mod runner;
mod statistics;
