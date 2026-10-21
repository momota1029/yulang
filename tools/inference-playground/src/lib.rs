//! Local experimental observations, not production admission or principal types.
mod output;
mod pinned_stdlib;
pub mod render;
pub mod runtime;
use output::{Output, cap};
use std::collections::HashMap;
use std::fmt::Write;
use std::{io::Read, ops::Range, sync::Arc};
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{FileId, FileKey, HirItem, HirModule, HirOccurrenceId, ModuleIdentity, SemanticImports, SourceRootId};
use yu_solver::shadow_apply::{CandidateError, CandidateInference};
use yu_syntax::{
    SourceRevision, SourceText, SyntaxDependencyProvenance, SyntaxDependencySlot,
    SyntaxEnvironment, SyntaxEnvironmentKey, parse_file, scan_header,
};

pub const INPUT_CAP: usize = 64 * 1024;

/// Completed Phase-R evidence for one source-linked FieldBoundV1 candidate.
/// Static HIR identities and dynamic runtime observations remain separate.
#[derive(Clone, Debug)]
pub struct OperationV1RuntimeReceipt {
    pub field_bound_id: u32,
    pub request: HirOccurrenceId,
    pub callback_apply: HirOccurrenceId,
    pub callback_operation: yu_hir::shadow::SourceOperationId,
    pub callback_operation_use: HirOccurrenceId,
    pub response_definition: yu_hir::HirLocalId,
    pub continuation_apply_source: runtime::SourceSite,
    pub response_argument_source: runtime::SourceSite,
    pub response_argument_read_source: runtime::SourceSite,
    pub response_argument_environment: usize,
    pub response_closure_source: runtime::SourceSite,
    pub response_closure_handle: usize,
    pub captured_environment: usize,
    pub callback_request_event: usize,
    pub callback_request_source: runtime::SourceSite,
    pub live_handler_source: runtime::SourceSite,
    pub selected_arm: yu_hir::shadow::SourceNodeKey,
    pub result: Box<str>,
}

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
    use runtime::{RuntimeEvidence, RuntimeOutcome, RuntimeProgram};
    let (hir, _candidate) = prepare(source, name, scoped)?;
    let unavailable = |error| bounded_message(format_args!("runtime unavailable: {error:?}"));
    let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).map_err(unavailable)?;
    let selected = program.definition_named(definition).map_err(unavailable)?;
    let mut machine = program.start_source_schedule(selected).map_err(unavailable)?;
    let value = match machine.run(step_budget) {
        RuntimeOutcome::Completed(handle) => handle,
        RuntimeOutcome::Unavailable(error) => return Err(unavailable(error)),
        RuntimeOutcome::ResourceExhausted { steps } => return Err(format!(
            "runtime step budget exhausted after {steps} steps; no completed result")),
        RuntimeOutcome::UnhandledRequest { source, payload, .. } => {
            let range = machine
                .value(payload)
                .map(|value| value.source.range.clone())
                .unwrap_or_else(|| source.range.clone());
            return Err(bounded_message(format_args!(
                "unhandled runtime request at {range:?}"
            )));
        }
        RuntimeOutcome::Running => return Err("runtime has no completed result".to_owned()),
    };
    let mut output = Output::new();
    render_runtime_value(&machine, value, &mut output).map_err(cap)?;
    output.write_char('\n').map_err(cap)?;
    output.finish()
}

fn render_runtime_value(
    machine: &runtime::Machine,
    root: runtime::ValueHandle,
    output: &mut Output,
) -> Result<(), std::fmt::Error> {
    enum Item {
        Value(runtime::ValueHandle),
        Text(&'static str),
    }
    let mut pending = vec![Item::Value(root)];
    while let Some(item) = pending.pop() {
        match item {
            Item::Text(text) => output.write_str(text)?,
            Item::Value(handle) => {
                let Some(value) = machine.value(handle) else {
                    return Err(std::fmt::Error);
                };
                match &value.kind {
                    runtime::RuntimeValueKind::Unit => output.write_str("()")?,
                    runtime::RuntimeValueKind::Integer(value) => output.write_str(value)?,
                    runtime::RuntimeValueKind::Boolean(value) => write!(output, "{value}")?,
                    runtime::RuntimeValueKind::String(value) => write!(output, "{value:?}")?,
                    runtime::RuntimeValueKind::Tuple(elements) => {
                        output.write_char('(')?;
                        if elements.is_empty() {
                            output.write_char(')')?;
                            continue;
                        }
                        pending.push(Item::Text(")"));
                        if elements.len() == 1 {
                            pending.push(Item::Text(","));
                        }
                        for (index, element) in elements.iter().enumerate().rev() {
                            pending.push(Item::Value(element.value()));
                            if index > 0 {
                                pending.push(Item::Text(", "));
                            }
                        }
                    }
                    runtime::RuntimeValueKind::Closure => output.write_str("<function>")?,
                    runtime::RuntimeValueKind::Computation => output.write_str("<computation>")?,
                    runtime::RuntimeValueKind::Operation(_) => output.write_str("<operation>")?,
                }
            }
        }
    }
    Ok(())
}

/// Explicit research-only Phase-R path. It solves the v1 candidate from one
/// HIR, carries that receipt into a runtime program built from the same HIR,
/// and returns only after the matching saved callback reaches the live outer
/// handler and completes with integer 42. Ordinary execute remains unchanged.
pub fn execute_operation_v1_runtime_research(
    source: &str,
    name: &str,
    step_budget: usize,
) -> Result<OperationV1RuntimeReceipt, String> {
    use runtime::{RuntimeOutcome, RuntimeProgram, RuntimeValueKind};
    let hir = prepare_operation_v1_hir(source, name)?;
    let candidate = CandidateInference::solve_operation_v1_research(hir.clone())
        .map_err(|error| bounded_message(format_args!("v1 candidate unavailable: {error:?}")))?;
    if !candidate.observes_hir(&hir) || !candidate.candidate_conflicts().is_empty() {
        return Err("v1 candidate conflicts; no runtime receipt".to_owned());
    }
    let evidence = RuntimeProgram::evidence_for_operation_v1(&hir, &candidate)
        .map_err(|error| bounded_message(format_args!("v1 static receipt unavailable: {error:?}")))?;
    let program = RuntimeProgram::from_hir(hir, evidence)
        .map_err(|error| bounded_message(format_args!("runtime unavailable: {error:?}")))?;
    let selected = program.definition_named("main")
        .map_err(|error| bounded_message(format_args!("runtime unavailable: {error:?}")))?;
    let mut machine = program.start_source_schedule(selected)
        .map_err(|error| bounded_message(format_args!("runtime unavailable: {error:?}")))?;
    let completed = match machine.run(step_budget) {
        RuntimeOutcome::Completed(value) => value,
        RuntimeOutcome::Unavailable(error) => return Err(bounded_message(format_args!("runtime unavailable: {error:?}"))),
        RuntimeOutcome::ResourceExhausted { steps } => return Err(format!("runtime exhausted after {steps} steps; no completed receipt")),
        RuntimeOutcome::UnhandledRequest { source, payload, .. } => {
            let range = machine
                .value(payload)
                .map(|value| value.source.range.clone())
                .unwrap_or_else(|| source.range.clone());
            return Err(bounded_message(format_args!(
                "unhandled runtime request at {range:?}; no completed receipt"
            )));
        }
        RuntimeOutcome::Running => return Err("runtime did not complete; no completed receipt".to_owned()),
    };
    if !matches!(machine.value(completed).map(|value| &value.kind), Some(RuntimeValueKind::Integer(value)) if value.as_ref() == "42") {
        return Err("runtime result is not integer 42; no completed receipt".to_owned());
    }
    machine.operation_v1_runtime_receipt(completed)
        .ok_or_else(|| "runtime completed without the exact v1 callback/handler join; no completed receipt".to_owned())
}

fn prepare_operation_v1_hir(source: &str, name: &str) -> Result<Arc<HirModule>, String> {
    if source.len() > INPUT_CAP {
        return Err(format!("tool input cap exceeded: more than {INPUT_CAP} bytes"));
    }
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
        return Err("syntax diagnostics; no v1 runtime receipt".to_owned());
    }
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("inference-playground", name))),
        &parsed,
        SemanticImports::empty(),
    ).map(Arc::new)
        .map_err(|error| bounded_message(format_args!("candidate lowering unavailable: {error:?}")))
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
        Arc::new(playground_syntax_environment()?),
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
        let conflict_ranges = conflict_ranges_for(
            &hir,
            candidate
                .candidate_conflicts()
                .iter()
                // Only this prefix can pass one observe(1) charge per report row.
                // Keep the diagnostic loop below complete so it preserves the cap error.
                .take(output::WORK_CAP)
                .map(|error| error.occurrence().occurrence()),
        );
        output
            .write_str("candidate type conflicts (experimental; graph export withheld):\n")
            .map_err(cap)?;
        for error in candidate.candidate_conflicts() {
            output.observe(1)?;
            let occurrence = error.occurrence().occurrence();
            let range = conflict_ranges.get(occurrence).copied().flatten();
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

fn playground_syntax_environment() -> Result<SyntaxEnvironment, String> {
    let resolved = pinned_stdlib::resolve_implicit_stdlib()
        .map_err(|error| format!("pinned standard-library bundle unavailable: {error:?}"))?;
    let source = resolved
        .iter()
        .find(|source| source.path == "lib/std/core/ops.yu")
        .ok_or_else(|| "pinned standard-library module std::core::ops is missing".to_owned())?;
    let fingerprint = pinned_stdlib::fingerprint(&source.git_blob);
    let text: Arc<SourceText> = Arc::from(source.text);
    let header = scan_header(text);
    let dependency = SyntaxDependencySlot::from_index(0)
        .expect("the standard-library syntax dependency fits its slot type");
    let provenance = Arc::from([SyntaxDependencyProvenance::new(
        Arc::from(source.path),
        SourceRevision::from_fingerprint(fingerprint),
    )]);
    SyntaxEnvironment::from_imported_headers(
        SyntaxEnvironmentKey::from_fingerprint(fingerprint),
        [(dependency, &header)],
        provenance,
    )
    .map_err(|error| format!("pinned standard-library syntax unavailable: {error:?}"))
}

fn conflict_ranges_for<'requested, 'hir>(
    hir: &'hir HirModule,
    requested: impl IntoIterator<Item = &'requested HirOccurrenceId>,
) -> HashMap<&'requested HirOccurrenceId, Option<&'hir Range<usize>>> {
    let mut ranges = HashMap::new();
    for occurrence in requested {
        ranges.entry(occurrence).or_insert(None);
    }
    if ranges.is_empty() {
        return ranges;
    }

    let mut unresolved = ranges.len();
    for item in hir.items() {
        let source_root = match item {
            HirItem::Binding(binding) => {
                SourceRootId::Definition(binding.definition_root().clone())
            }
            HirItem::Expression(expression) => {
                let Some(root) = hir
                    .expression_root(expression.occurrence())
                    .ok()
                    .flatten()
                else {
                    continue;
                };
                SourceRootId::Expression(root.clone())
            }
            HirItem::Error { .. } => continue,
        };
        let Some(local) = hir.local_source_for(&source_root).ok().flatten() else {
            continue;
        };
        for expression in local.expressions() {
            let Some(range) = ranges.get_mut(&expression.occurrence) else {
                continue;
            };
            if range.is_some() {
                continue;
            }
            *range = Some(&expression.range);
            unresolved -= 1;
            if unresolved == 0 {
                return ranges;
            }
        }
    }
    ranges
}

fn bounded_message(arguments: std::fmt::Arguments<'_>) -> String {
    let mut output = Output::new();
    if output.write_fmt(arguments).is_err() {
        return output::CAP_ERROR.to_owned();
    }
    output.finish().unwrap_or_else(|error| error)
}

#[cfg(test)]
mod tests {
    use super::playground_syntax_environment;
    use super::pinned_stdlib;
    use super::{conflict_ranges_for, execute, prepare};
    use super::output;
    use yu_hir::shadow::{LocalSourceForm, lower_module_with_local_source};
    use yu_hir::{FileId, FileKey, HirItem, HirOccurrenceId, HirModule, ModuleIdentity, SemanticImports, SourceRootId};
    use yu_solver::shadow_apply::CandidateInference;
    use crate::runtime::{RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeUnavailable};
    use std::sync::Arc;
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    #[test]
    fn pinned_fmt_role_and_tuple_impl_keep_exact_module_and_parse_positions() {
        let inventory = pinned_stdlib::parse_role_inventory(
            "std::core::fmt",
            Arc::new(playground_syntax_environment().unwrap()),
        )
        .unwrap();
        assert_eq!(inventory.source.path, "lib/std/core/fmt.yu");
        assert_eq!(
            inventory
                .source
                .git_blob
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>(),
            "fd7b6607094c9ad70bde1fd41890363fa8bd6b31"
        );
        let file_key = inventory.identity.file().key();
        assert_eq!(file_key.realm(), "yulang2-pinned-stdlib");
        assert_eq!(
            file_key.normalized_workspace_relative_path(),
            inventory.source.path
        );

        assert_eq!(inventory.parsed.source(), inventory.source.text);
        let declarations = inventory
            .declaration_ranges
            .iter()
            .map(|(_, range)| &inventory.parsed.source()[range.clone()])
            .collect::<Vec<_>>();
        assert!(!inventory.diagnostics.is_empty());
        assert!(declarations
            .iter()
            .any(|text| text.starts_with("pub role Display 'a:")), "{declarations:?}");
        assert!(declarations
            .iter()
            .any(|text| text.starts_with("impl ('a, 'b): Display:")), "{declarations:?}");
        assert!(inventory.source.text.contains("pub a.show: str"));
        assert!(inventory.source.text.contains("pub a.say = std::io::out::write: a.show +"));
        assert!(inventory.source.text.contains("where 'a: Display\n    where 'b: Display\n    our value.show = case value:"));
        assert!(inventory.source.text.contains("(a, b) -> \"(\" + a.show + \", \" + b.show + \")\""));

        let mut groups = std::collections::BTreeMap::new();
        for diagnostic in &inventory.diagnostics {
            assert!(diagnostic.range.start <= diagnostic.range.end);
            assert!(diagnostic.range.end <= inventory.source.text.len());
            assert!(inventory.source.text.get(diagnostic.range.clone()).is_some());
            assert!(diagnostic.excerpt.len() <= 160);
            assert!(inventory.source.text[diagnostic.range.start..].starts_with(&diagnostic.excerpt));
            *groups
                .entry((diagnostic.category.as_str(), diagnostic.parent.as_str()))
                .or_insert(0usize) += 1;
            assert_eq!(diagnostic.ordinal, Some(groups.values().sum::<usize>() as u32 - 1));
        }
        assert_eq!(inventory.diagnostics.len(), 36);
        assert_eq!(groups.get(&("ErrorGroup", "Root")), Some(&21));
        assert_eq!(groups.get(&("ErrorGroup", "OperatorChain")), Some(&7));
        assert_eq!(groups.get(&("Missing", "CaseArm")), Some(&7));
    }

    #[test]
    fn console_operator_is_loaded_from_the_pinned_imported_source() {
        let source =
            "// println is a library effect handled by the host.\n\nprintln \"hello from Yulang\"\nsay: 1 + 2\n";
        assert_eq!(source.len(), 92);
        let environment = playground_syntax_environment().unwrap();
        assert_ne!(environment.key(), yu_syntax::SyntaxEnvironmentKey::EMPTY);
        assert_eq!(environment.provenance().len(), 1);
        assert_eq!(
            environment.provenance()[0].module_label(),
            "lib/std/core/ops.yu"
        );

        let text: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(
            text.clone(),
            Arc::new(scan_header(text)),
            Arc::new(environment),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
    }

    #[test]
    fn execute_renders_nested_ordered_tuple_values() {
        assert_eq!(
            execute("my main = (1, (2, 3), 4)", "tuple.yu", "main", 10_000, false)
                .unwrap(),
            "(1, (2, 3), 4)\n"
        );
        assert_eq!(
            execute("my main = (1,)", "singleton-tuple.yu", "main", 10_000, false)
                .unwrap(),
            "(1,)\n"
        );
    }

    #[test]
    fn candidate_graph_renderer_exposes_nested_tuple_children_in_order() {
        let (hir, candidate) = prepare("my pair = (42, \"Yulang\")", "tuple-graph.yu", false)
            .unwrap();
        let binding = hir.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "pair" => Some(binding),
            _ => None,
        }).unwrap();
        let export = candidate.export(binding.definition_root()).unwrap();
        let rendered = super::render::graph(&export).unwrap();
        assert!(rendered.contains("Tuple(["), "{rendered}");

        let (hir, candidate) =
            prepare("my nested = (1, (2, 3), 4)", "nested-tuple-graph.yu", false).unwrap();
        let binding = hir.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "nested" => Some(binding),
            _ => None,
        }).unwrap();
        let export = candidate.export(binding.definition_root()).unwrap();
        let rendered = super::render::graph(&export).unwrap();
        let tuple_lines: Vec<_> = rendered.lines().filter(|line| line.contains("Tuple([")).collect();
        assert_eq!(tuple_lines.len(), 2, "{rendered}");
        assert!(tuple_lines.iter().any(|line| line.contains(", ") && line.matches(", ").count() == 2));
        assert!(tuple_lines.iter().any(|line| line.contains(", ") && line.matches(", ").count() == 1));
    }

    fn integer_expression<'hir>(
        hir: &'hir HirModule,
        root: &SourceRootId,
        spelling: &str,
    ) -> &'hir yu_hir::shadow::LocalSourceExpr {
        hir.local_source_for(root)
            .unwrap()
            .unwrap()
            .expressions()
            .iter()
            .find(|expression| matches!(
                &expression.form,
                LocalSourceForm::Integer(value) if value.as_ref() == spelling
            ))
            .expect("the requested original integer expression")
    }

    #[test]
    fn wrong_family_permission_withholds_runtime_and_cli_result() {
        let source = "act signal:\n    our ping: bool -> bool\nact other:\n    our unrelated: int -> int\nmy receive (input:[other] bool) = catch input { signal::ping(p), _ -> false }\nmy main = receive (signal::ping true)";
        assert_eq!(source.len(), 195);

        let text: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(
            text.clone(),
            Arc::new(scan_header(text)),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
        let hir = Arc::new(
            lower_module_with_local_source(
                ModuleIdentity::source_root(FileId::new(FileKey::new(
                    "inference-playground",
                    "-",
                ))),
                &parsed,
                SemanticImports::empty(),
            )
            .unwrap(),
        );
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{source}");

        let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).unwrap();
        let selected = program.definition_named("main").unwrap();
        let mut machine = program.start_source_schedule(selected).unwrap();
        let direct_error = match machine.run(10_000) {
            RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(site)) => {
                RuntimeUnavailable::HandlerEvidence(site)
            }
            outcome => panic!("expected HandlerEvidence, got {outcome:?}"),
        };

        assert_eq!(
            execute(source, "-", "main", 10_000, false).unwrap_err(),
            format!("runtime unavailable: {direct_error:?}")
        );
    }

    #[test]
    fn conflict_range_index_keeps_authentic_roots_and_missing_occurrences() {
        let (hir, _) = prepare("1; my main = 2", "range-index", false).unwrap();
        let direct_root = hir
            .items()
            .iter()
            .find_map(|item| match item {
                HirItem::Expression(expression) => Some(
                    hir.expression_root(expression.occurrence())
                        .unwrap()
                        .unwrap()
                        .clone(),
                ),
                _ => None,
            })
            .expect("the original direct expression root");
        let direct = integer_expression(
            &hir,
            &SourceRootId::Expression(direct_root),
            "1",
        );

        let main = hir
            .items()
            .iter()
            .find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == "main" => Some(binding),
                _ => None,
            })
            .expect("the original main definition");
        let initializer = integer_expression(
            &hir,
            &SourceRootId::Definition(main.definition_root().clone()),
            "2",
        );

        let (foreign_hir, _) = prepare("3; my main = 4", "range-index-foreign", false).unwrap();
        let foreign_root = foreign_hir
            .items()
            .iter()
            .find_map(|item| match item {
                HirItem::Expression(expression) => Some(
                    foreign_hir
                        .expression_root(expression.occurrence())
                        .unwrap()
                        .unwrap()
                        .clone(),
                ),
                _ => None,
            })
            .expect("the separate artifact's direct expression root");
        let foreign = integer_expression(
            &foreign_hir,
            &SourceRootId::Expression(foreign_root),
            "3",
        );

        let empty = conflict_ranges_for(&hir, std::iter::empty::<&HirOccurrenceId>());
        assert!(empty.is_empty());

        let authentic = conflict_ranges_for(
            &hir,
            [&direct.occurrence, &initializer.occurrence],
        );
        assert_eq!(authentic.len(), 2);
        assert!(std::ptr::eq(
            authentic
                .get(&direct.occurrence)
                .copied()
                .flatten()
                .unwrap(),
            &direct.range,
        ));
        assert!(std::ptr::eq(
            authentic
                .get(&initializer.occurrence)
                .copied()
                .flatten()
                .unwrap(),
            &initializer.range,
        ));

        let requests = [
            &direct.occurrence,
            &initializer.occurrence,
            &direct.occurrence,
            &foreign.occurrence,
        ];
        let indexed = conflict_ranges_for(&hir, requests);
        assert_eq!(indexed.len(), 3, "duplicate requested keys are deduplicated");
        assert!(std::ptr::eq(
            indexed
                .get(&direct.occurrence)
                .copied()
                .flatten()
                .unwrap(),
            &direct.range,
        ));
        assert!(std::ptr::eq(
            indexed
                .get(&initializer.occurrence)
                .copied()
                .flatten()
                .unwrap(),
            &initializer.range,
        ));
        assert!(indexed
            .get(&foreign.occurrence)
            .is_some_and(Option::is_none));
    }

    #[test]
    fn conflict_range_index_limits_prefetch_to_observable_prefix() {
        let (hir, _) = prepare("1; my main = 2", "range-index-prefix", false).unwrap();
        let direct_root = hir
            .items()
            .iter()
            .find_map(|item| match item {
                HirItem::Expression(expression) => Some(
                    hir.expression_root(expression.occurrence())
                        .unwrap()
                        .unwrap()
                        .clone(),
                ),
                _ => None,
            })
            .expect("the original direct expression root");
        let direct = integer_expression(
            &hir,
            &SourceRootId::Expression(direct_root),
            "1",
        );

        let mut consumed = 0;
        let requested = std::iter::repeat_with(|| {
            consumed += 1;
            &direct.occurrence
        })
        .take(output::WORK_CAP)
        .chain(std::iter::once_with(|| {
            panic!("the prefetch adapter must not inspect records beyond WORK_CAP")
        }))
        .take(output::WORK_CAP);
        let indexed = conflict_ranges_for(&hir, requested);

        assert_eq!(consumed, output::WORK_CAP);
        assert_eq!(indexed.len(), 1, "repeated records share one authentic key");
        assert!(std::ptr::eq(
            indexed
                .get(&direct.occurrence)
                .copied()
                .flatten()
                .unwrap(),
            &direct.range,
        ));
    }
}
