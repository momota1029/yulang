use std::{fmt, sync::Arc};

use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const SOURCE: &str = include_str!("entry-computation-argument.yu");
const ROW_CAP: usize = 48;
const TEXT_CAP: usize = 360;

fn bounded_debug(record: &dyn std::fmt::Debug) -> String {
    struct Capped {
        text: String,
        truncated: bool,
    }
    impl fmt::Write for Capped {
        fn write_str(&mut self, value: &str) -> fmt::Result {
            if self.text.len() >= TEXT_CAP {
                self.truncated = true;
                return Ok(());
            }
            let remaining = TEXT_CAP - self.text.len();
            let mut end = value.len().min(remaining);
            while !value.is_char_boundary(end) { end -= 1; }
            self.text.push_str(&value[..end]);
            self.truncated |= end < value.len();
            Ok(())
        }
    }
    let mut output = Capped { text: String::new(), truncated: false };
    let _ = fmt::write(&mut output, format_args!("{record:?}"));
    if output.truncated { output.text.push_str("…[record truncated]"); }
    output.text
}

fn main() -> Result<(), String> {
    let source: Arc<SourceText> = Arc::from(SOURCE);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    if !parsed.structural_recoveries().is_empty() {
        return Err("fixture has structural recovery".to_owned());
    }
    let hir = Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new(
            "inference-playground-r170",
            "entry-computation-argument.yu",
        ))),
        &parsed,
        SemanticImports::empty(),
    ).map_err(|error| format!("fixture lowering unavailable: {error:?}"))?);
    let candidate = CandidateInference::solve(hir)
        .map_err(|error| format!("candidate inference unavailable: {error:?}"))?;
    let observation = candidate.ordinary_provider_observation(ROW_CAP)
        .map_err(|error| format!("provider observation unavailable: {error:?}"))?;
    println!("R170 retained ordinary provider rows (cap {ROW_CAP}):");
    for row in observation.rows() {
        println!(
            "provider graph={} fp={} q={} {:?}[{}] {}",
            row.graph_index,
            row.function_port_ordinal,
            row.relation,
            row.kind,
            row.ordinal,
            bounded_debug(row.record),
        );
    }
    println!("R170 retained Capture and fresh-use rows:");
    for row in observation.capture_rows() {
        println!(
            "capture graph={} owner={:?} route={} occurrence={:?} context_use={} q={:?} {:?}[{}] map={:?} {}",
            row.graph_index,
            row.route_owner,
            row.route,
            row.route_occurrence,
            row.context_use,
            row.relation,
            row.kind,
            row.ordinal,
            row.map_name,
            bounded_debug(row.record),
        );
    }
    println!(
        "lambda_slot2_source_join={:?}; provider-to-Capture incidence is not inferred from matching relation IDs",
        observation.lambda_slot2_source_join(),
    );
    println!("truncated={}", observation.truncated());
    Ok(())
}
