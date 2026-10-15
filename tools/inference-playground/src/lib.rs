//! Local experimental observations, not production admission or principal types.
mod output;
pub mod render;
pub mod runtime;
use output::{Output, cap};
use std::fmt::Write;
use std::{io::Read, ops::Range, sync::Arc};
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateError, CandidateInference};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

pub const INPUT_CAP: usize = 64 * 1024;

pub fn read_source(reader: impl Read) -> Result<String, String> {
    let mut bytes = Vec::new();
    reader
        .take((INPUT_CAP + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("source read failed: {error}"))?;
    if bytes.len() > INPUT_CAP {
        return Err(format!(
            "tool input cap exceeded: more than {INPUT_CAP} bytes"
        ));
    }
    String::from_utf8(bytes).map_err(|error| format!("source is not UTF-8: {error}"))
}

/// Columns count Unicode scalar values; byte ranges retain parser/HIR coordinates.
pub fn location(source: &str, range: &Range<usize>) -> String {
    let mut output = Output::new();
    match location_into(source, range, &mut output) {
        Ok(()) => output.finish().unwrap_or_else(|error| error),
        Err(error) => error,
    }
}

pub(crate) fn location_into(
    source: &str,
    range: &Range<usize>,
    output: &mut Output,
) -> Result<(), String> {
    let mut start = range.start.min(source.len());
    while !source.is_char_boundary(start) {
        start -= 1;
    }
    let prefix = &source[..start];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let line_start = prefix.rfind('\n').map_or(0, |index| index + 1);
    let column = source[line_start..start].chars().count() + 1;
    let line_end = source[start..]
        .find('\n')
        .map_or(source.len(), |index| start + index);
    write!(
        output,
        "{line}:{column} (bytes {}..{})\n  {}",
        range.start,
        range.end,
        &source[line_start..line_end]
    )
    .map_err(cap)
}

pub fn infer(source: &str, name: &str) -> Result<String, String> {
    infer_with_intrusion(source, name, false)
}

pub fn infer_with_intrusion(source: &str, name: &str, intrusion: bool) -> Result<String, String> {
    infer_with_scoped_experiment(source, name, intrusion, false)
}

pub fn infer_with_scoped_experiment(source: &str, name: &str, intrusion: bool, scoped: bool) -> Result<String, String> {
    let (hir, candidate) = prepare(source, name, scoped)?;
    let mut output = Output::new();
    output.write_str("Experimental candidate inference graph; no principal-type or production-admission claim.\nEffect operands with unavailable contents remain opaque.\n").map_err(cap)?;
    let mut definitions = 0;
    for item in hir.items() {
        if let HirItem::Binding(binding) = item {
            output.observe(1)?;
            definitions += 1;
            if definitions > render::OUTPUT_CAP {
                return Err("tool output cap exceeded: too many definitions".to_owned());
            }
            let graph = candidate
                .export(binding.definition_root())
                .map_err(|_| "candidate graph export unavailable".to_owned())?;
            write!(output, "\ndefinition {}:\n", binding.name().spelling()).map_err(cap)?;
            render::graph_into(&graph, &mut output)?;
        }
    }
    if definitions == 0 {
        output
            .write_str("No binding exports in this source.\n")
            .map_err(cap)?;
    }
    if scoped {
        output.write_str("Native scoped inference observations (experimental; Catch subtraction remains open):\nLimits: 4096 regions/scopes/inputs/flows/transformers/executed records; scoped work 65536.\n").map_err(cap)?;
        write!(output, "  inventory (regions,scopes,inputs,work,max recorded scoped scratch envelope bytes) = {:?}\n", candidate.scoped_resource_statistics()).map_err(cap)?;
        for statistics in candidate.scoped_copy_statistics() {
            output.observe(1)?; writeln!(output, "  fresh copy (regions,scopes,inputs,graph_nodes,graph_bounds)={statistics:?}").map_err(cap)?;
        }
        for (actual, original, occurrence) in candidate.scoped_scope_lineage() {
            output.observe(1)?; writeln!(output, "  scope {actual} original={original} source={occurrence:?}").map_err(cap)?;
        }
        for (actual, original, occurrence) in candidate.scoped_input_lineage() {
            output.observe(1)?; writeln!(output, "  input {actual} original={original} source={occurrence:?}").map_err(cap)?;
        }
        for (relation, pair, flow, non_default) in candidate.scoped_relation_flows() {
            output.observe(1)?;
            if non_default { writeln!(output, "  scoped relation {relation} pair={pair:?} flow={flow:?}").map_err(cap)?; }
        }
        if intrusion {
            for dependency in candidate.scoped_dependencies() {
                output.observe(1)?; writeln!(output, "  dependency {dependency:?}").map_err(cap)?;
            }
            for origin in candidate.scoped_origins() {
                output.observe(1)?; writeln!(output, "  source origin {origin:?}").map_err(cap)?;
            }
        }
        for observation in candidate.scoped_observations() {
            output.observe(1)?;
            let observation = observation.map_err(|error| bounded_message(format_args!("scoped observation unavailable: {error:?}")))?;
            writeln!(output, "  relation {} pair={:?} transformer={} {:?}", observation.relation_id(), observation.pair(), observation.transformer_id(), observation.transformer()).map_err(cap)?;
            for member in 0..observation.member_count() {
                output.observe(1)?;
                write!(output, "    {:?} inputs=[", observation.member_operand(member)).map_err(cap)?;
                for input in observation.input_routes() { write!(output, "{input},").map_err(cap)?; }
                output.write_str("] protections=[").map_err(cap)?;
                for scope in observation.protection_scopes() { write!(output, "{scope},").map_err(cap)?; }
                output.write_str("]\n").map_err(cap)?;
            }
        }
    }
    if intrusion {
        render::intrusion_into(&candidate, &hir, source, &mut output)?;
    }
    output.finish()
}

/// Execute the source machine after experimental inference accepts the module.
/// This tool entrypoint does not certify production admission or hygiene.
pub fn execute(
    source: &str,
    name: &str,
    definition: &str,
    step_budget: usize,
    scoped: bool,
) -> Result<String, String> {
    use runtime::{RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeValueKind};
    let (hir, _candidate) = prepare(source, name, scoped)?;
    let unavailable = |error| bounded_message(format_args!("runtime unavailable: {error:?}"));
    let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).map_err(unavailable)?;
    let selected = program.definition_named(definition).map_err(unavailable)?;
    let roots = program.execution_roots().map_err(unavailable)?;
    let mut machine = program.start(selected, &roots).map_err(unavailable)?;
    let value = match machine.run(step_budget) {
        RuntimeOutcome::Completed(handle) => machine.value(handle)
            .ok_or_else(|| "runtime completed value unavailable".to_owned())?,
        RuntimeOutcome::Unavailable(error) => return Err(unavailable(error)),
        RuntimeOutcome::ResourceExhausted { steps } => return Err(format!(
            "runtime step budget exhausted after {steps} steps; no completed result")),
        RuntimeOutcome::UnhandledRequest { source } => return Err(bounded_message(
            format_args!("unhandled runtime request at {:?}", source.range))),
        RuntimeOutcome::Running => return Err("runtime has no completed result".to_owned()),
    };
    let mut output = Output::new();
    match &value.kind {
        RuntimeValueKind::Unit => output.write_str("()"),
        RuntimeValueKind::Integer(value) => output.write_str(value),
        RuntimeValueKind::Boolean(value) => write!(output, "{value}"),
        RuntimeValueKind::String(value) => write!(output, "{value:?}"),
        RuntimeValueKind::Closure => output.write_str("<function>"),
        RuntimeValueKind::Computation => output.write_str("<computation>"),
        RuntimeValueKind::Operation(_) => output.write_str("<operation>"),
    }.map_err(cap)?;
    output.write_char('\n').map_err(cap)?;
    output.finish()
}

fn prepare(
    source: &str,
    name: &str,
    scoped: bool,
) -> Result<(Arc<HirModule>, CandidateInference), String> {
    if source.len() > INPUT_CAP {
        return Err(format!(
            "tool input cap exceeded: more than {INPUT_CAP} bytes"
        ));
    }
    let mut output = Output::new();
    let text: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        text.clone(),
        Arc::new(scan_header(text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let diagnostics = parsed.syntax_diagnostics().map_err(|error| {
        bounded_message(format_args!("syntax diagnostics unavailable: {error:?}"))
    })?;
    if !diagnostics.is_empty() {
        output.write_str("syntax diagnostics:\n").map_err(cap)?;
        for diagnostic in diagnostics {
            output.observe(1)?;
            write!(output, "  {:?} at ", diagnostic.cause()).map_err(cap)?;
            location_into(source, diagnostic.primary(), &mut output)?;
            output.write_char('\n').map_err(cap)?;
        }
        return Err(output.finish()?);
    }
    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("inference-playground", name))),
            &parsed,
            SemanticImports::empty(),
        )
        .map_err(|error| {
            bounded_message(format_args!("candidate lowering unavailable: {error:?}"))
        })?,
    );
    let solved = if scoped { CandidateInference::solve_scoped_experiment(hir.clone()) } else { CandidateInference::solve(hir.clone()) };
    let candidate = solved.map_err(|error| match error {
        CandidateError::Unsupported => {
            "unsupported source: current candidate lowering/inference cannot observe this program"
                .to_owned()
        }
        other => bounded_message(format_args!("candidate inference unavailable: {other:?}")),
    })?;
    if !candidate.candidate_conflicts().is_empty() {
        output
            .write_str("candidate type conflicts (experimental; graph export withheld):\n")
            .map_err(cap)?;
        for error in candidate.candidate_conflicts() {
            output.observe(1)?;
            let occurrence = error.occurrence().occurrence();
            let range = hir.items().iter().find_map(|item| {
                let HirItem::Binding(binding) = item else {
                    return None;
                };
                let local = hir.local_source(binding.definition_root()).ok().flatten()?;
                local
                    .expressions()
                    .iter()
                    .find(|expression| &expression.occurrence == occurrence)
                    .map(|expression| expression.range.clone())
            });
            write!(output, "  {:?} at ", error.kind()).map_err(cap)?;
            if let Some(range) = range {
                location_into(source, &range, &mut output)?;
            } else {
                output.write_str("source span unavailable").map_err(cap)?;
            }
            output.write_char('\n').map_err(cap)?;
        }
        return Err(output.finish()?);
    }
    Ok((hir, candidate))
}

fn bounded_message(arguments: std::fmt::Arguments<'_>) -> String {
    let mut output = Output::new();
    if output.write_fmt(arguments).is_err() {
        return output::CAP_ERROR.to_owned();
    }
    output.finish().unwrap_or_else(|error| error)
}
