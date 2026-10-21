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
use yu_hir::{
    FileId, FileKey, HirItem, HirModule, HirOccurrenceId, ModuleIdentity, SemanticImports,
    SourceRootId, index_source_exports,
};
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
                    runtime::RuntimeValueKind::Primitive(operation) => write!(output, "<primitive {operation:?}>")?,
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
    let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("inference-playground", name)));
    let (providers, indexes) = pinned_module_world()?;
    let imports = SemanticImports::with_source_imports(&parsed, &identity, &indexes)
        .map_err(|error| bounded_message(format_args!("source imports unavailable: {error:?}")))?;
    let hir = Arc::new(
        lower_module_with_local_source(
            identity,
            &parsed,
            imports,
        )
        .map_err(|error| {
            bounded_message(format_args!("candidate lowering unavailable: {error:?}"))
        })?,
    );
    let solved = if scoped {
        CandidateInference::solve_scoped_experiment(hir.clone())
    } else {
        let mut modules = providers;
        modules.push(hir.clone());
        CandidateInference::solve_modules(modules)
    };
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

fn pinned_module_world() -> Result<(Vec<Arc<HirModule>>, Vec<yu_hir::SourceExportIndex>), String> {
    use yu_syntax::{SourceText, parse_file, scan_header};

    let sources = pinned_stdlib::resolve_implicit_stdlib()
        .map_err(|error| format!("pinned standard-library bundle unavailable: {error:?}"))?;
    let mut parsed_sources = Vec::new();
    let mut indexes = Vec::new();
    parsed_sources.try_reserve_exact(sources.len()).map_err(|_| "pinned source allocation unavailable".to_owned())?;
    indexes.try_reserve_exact(sources.len()).map_err(|_| "pinned index allocation unavailable".to_owned())?;
    for source in sources.iter() {
        let text: Arc<SourceText> = Arc::from(source.text);
        let parsed = parse_file(
            text.clone(),
            Arc::new(scan_header(text)),
            Arc::new(pinned_stdlib::syntax_environment_for_source(source, &sources)
                .map_err(|error| format!("pinned syntax environment unavailable: {error:?}"))?),
        );
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("pinned-yulang2", source.path)));
        indexes.push(index_source_exports(identity.clone(), &parsed)
            .map_err(|error| format!("pinned source index unavailable: {error:?}"))?);
        parsed_sources.push((identity, parsed));
    }
    let mut providers = Vec::new();
    providers.try_reserve_exact(parsed_sources.len()).map_err(|_| "pinned HIR allocation unavailable".to_owned())?;
    for (identity, parsed) in parsed_sources {
        let imports = SemanticImports::with_source_imports(&parsed, &identity, &indexes)
            .map_err(|error| format!("pinned source imports unavailable for {}: {error:?}", identity.file().key().normalized_workspace_relative_path()))?;
        let hir = lower_module_with_local_source(identity, &parsed, imports)
            .map_err(|error| format!("pinned source HIR unavailable: {error:?}"))?;
        providers.push(Arc::new(hir));
    }
    Ok((providers, indexes))
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
    use yu_hir::shadow::{
        LocalSourceForm, index_role_impl_sources, index_source_exports,
        lower_module_with_local_source, lower_module_with_selected_local_source, resolve_public_export,
    };
    use yu_hir::{FileId, FileKey, HirItem, HirOccurrenceId, HirModule, ModuleIdentity, SemanticImports, SourceRootId};
    use yu_solver::shadow_apply::CandidateInference;
    use crate::runtime::{RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeUnavailable};
    use std::sync::Arc;
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    #[test]
    fn authenticated_implicit_prelude_names_keep_source_identity_and_local_shadowing() {
        let sources = pinned_stdlib::resolve_implicit_stdlib().unwrap();
        let mut indexes = Vec::new();
        for source in sources.iter() {
            let module = source.path.strip_prefix("lib/").unwrap().strip_suffix(".yu").unwrap().replace('/', "::");
            let environment = Arc::new(pinned_stdlib::syntax_environment_for_source(source, &sources).unwrap());
            let inventory = pinned_stdlib::parse_role_inventory(&module, environment).unwrap();
            indexes.push(index_source_exports(inventory.identity, &inventory.parsed).unwrap());
        }

        let source = "// println is a library effect handled by the host.\n\nprintln \"hello from Yulang\"\nsay: 1 + 2\n";
        assert_eq!(source.len(), 92);
        let environment = Arc::new(playground_syntax_environment().unwrap());
        let text: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(text.clone(), Arc::new(scan_header(text)), environment);
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
            "playground", "samples/Console.yu",
        )));
        let imports = SemanticImports::with_implicit_prelude(&parsed, &identity, &indexes).unwrap();
        let hir = lower_module_with_local_source(identity, &parsed, imports).unwrap();
        assert!(hir.errors().iter().all(|error| error.kind() != yu_hir::HirErrorKind::UnresolvedName));
        let imported = hir.source_imports().unwrap();
        for name in ["say", "println"] {
            let yu_hir::SourceImportBinding::Resolved(export) = imported.resolve(name).unwrap() else {
                panic!("expected unique pinned prelude export for {name}");
            };
            assert_eq!(export.module.as_ref(), "std::io::console");
            assert!(export.route.iter().any(|step| step.path.iter().map(AsRef::as_ref).collect::<Vec<_>>() == ["std", "io", "console"]));
            let found = hir.items().iter().filter_map(|item| match item {
                HirItem::Binding(binding) => hir.local_source(binding.definition_root()).ok().flatten(),
                HirItem::Expression(expression) => hir.expression_root(expression.occurrence()).ok().flatten()
                    .and_then(|root| hir.local_source_for(&SourceRootId::Expression(root.clone())).ok().flatten()),
                HirItem::Error { .. } => None,
            }).flat_map(|source| source.expressions()).any(|expression| matches!(
                (&expression.form, name),
                (LocalSourceForm::Name { spelling, resolution: yu_hir::LocalSourceResolution::Imported(id) }, expected)
                    if spelling.as_ref() == expected && id == &export.identity()
            ));
            if name == "println" {
                assert!(found, "the unchanged Console println use must retain its pinned source identity");
            }
        }

        let say_source = "say";
        let text: Arc<SourceText> = Arc::from(say_source);
        let parsed = parse_file(text.clone(), Arc::new(scan_header(text)), Arc::new(playground_syntax_environment().unwrap()));
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("playground", "say.yu")));
        let imports = SemanticImports::with_implicit_prelude(&parsed, &identity, &indexes).unwrap();
        let hir = lower_module_with_local_source(identity, &parsed, imports).unwrap();
        let say_id = match hir.source_imports().unwrap().resolve("say").unwrap() {
            yu_hir::SourceImportBinding::Resolved(export) => export.identity(),
            yu_hir::SourceImportBinding::Ambiguous => panic!("pinned say export must be unique"),
        };
        assert!(hir.items().iter().filter_map(|item| match item {
            HirItem::Expression(expression) => hir.expression_root(expression.occurrence()).ok().flatten()
                .and_then(|root| hir.local_source_for(&SourceRootId::Expression(root.clone())).ok().flatten()),
            _ => None,
        }).flat_map(|source| source.expressions()).any(|expression| matches!(
            &expression.form,
            LocalSourceForm::Name { spelling, resolution: yu_hir::LocalSourceResolution::Imported(id) }
                if spelling.as_ref() == "say" && id == &say_id
        )));

        let shadow_source = "my say = 1\nsay";
        let text: Arc<SourceText> = Arc::from(shadow_source);
        let parsed = parse_file(text.clone(), Arc::new(scan_header(text)), Arc::new(playground_syntax_environment().unwrap()));
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("playground", "shadow.yu")));
        let imports = SemanticImports::with_implicit_prelude(&parsed, &identity, &indexes).unwrap();
        let hir = lower_module_with_local_source(identity, &parsed, imports).unwrap();
        let local_id = hir.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "say" => Some(binding.id().clone()),
            _ => None,
        }).unwrap();
        assert!(hir.items().iter().filter_map(|item| match item {
            HirItem::Expression(expression) => hir.expression_root(expression.occurrence()).ok().flatten().and_then(|root| hir.local_source_for(&SourceRootId::Expression(root.clone())).ok().flatten()),
            _ => None,
        }).flat_map(|source| source.expressions()).any(|expression| matches!(
            &expression.form,
            LocalSourceForm::Name { spelling, resolution: yu_hir::LocalSourceResolution::ModuleDef(id) }
                if spelling.as_ref() == "say" && id == &local_id
        )));
    }

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
        assert!(inventory.diagnostics.is_empty());
        assert!(groups.is_empty());

        let index = index_role_impl_sources(
            inventory.identity.clone(),
            &inventory.parsed,
        )
        .expect("the authentic fmt role and impl declarations retain source identities");
        assert_eq!(index.module(), inventory.identity.module());
        let [display] = index
            .roles()
            .iter()
            .filter(|role| role.head.spelling.as_ref() == "Display")
            .collect::<Vec<_>>()[..]
        else {
            panic!("one Display role source declaration")
        };
        assert_eq!(display.id.module.as_ref(), inventory.identity.module());
        assert_eq!(display.body.as_ref().unwrap().members.len(), 3);
        assert_eq!(
            display
                .body
                .as_ref()
                .unwrap()
                .members
                .iter()
                .map(|member| member.text.trim())
                .collect::<Vec<_>>(),
            [
                "pub a.show: str",
                "pub a.say = std::io::out::write: a.show + \"\\n\"",
                "pub a.note = std::io::err::write: a.show + \"\\n\"",
            ]
        );
        for member in &display.body.as_ref().unwrap().members {
            assert_eq!(
                &inventory.source.text[member.range.clone()],
                member.text.as_ref()
            );
            assert_eq!(member.id.role, display.id);
        }

        let [tuple_display] = index
            .implementations()
            .iter()
            .filter(|implementation| {
                implementation.target.text.trim() == "('a, 'b)"
                    && implementation.role.text.trim() == "Display"
            })
            .collect::<Vec<_>>()[..]
        else {
            panic!("one tuple Display implementation source declaration")
        };
        assert_eq!(
            tuple_display.id.module.as_ref(),
            inventory.identity.module()
        );
        assert_eq!(tuple_display.body.as_ref().unwrap().entries.len(), 3);
        assert!(tuple_display.body.as_ref().unwrap().entries[..2]
            .iter()
            .all(|entry| entry.kind == yu_syntax::SyntaxKind::WhereClause));
        assert_eq!(
            tuple_display.body.as_ref().unwrap().entries[2].kind,
            yu_syntax::SyntaxKind::BindingStatement
        );
        for entry in &tuple_display.body.as_ref().unwrap().entries {
            assert_eq!(
                &inventory.source.text[entry.range.clone()],
                entry.text.as_ref()
            );
            if let Some(member) = &entry.member {
                assert_eq!(member.implementation, tuple_display.id);
            }
        }
    }

    #[test]
    fn pinned_public_export_route_retains_source_owned_edges_and_names() {
        let mut indexed = std::collections::BTreeMap::new();
        let mut provider_hirs = Vec::new();
        let mut ordinary_provider_hirs = Vec::new();
        let mut provider_role_indexes = Vec::new();
        let mut console_parsed = None;
        let sources = pinned_stdlib::resolve_implicit_stdlib().unwrap();
        for source in sources.iter() {
            let module = source
                .path
                .strip_prefix("lib/")
                .unwrap()
                .strip_suffix(".yu")
                .unwrap()
                .replace('/', "::");
            let environment = Arc::new(
                pinned_stdlib::syntax_environment_for_source(source, &sources).unwrap(),
            );
            let inventory = pinned_stdlib::parse_role_inventory(&module, environment).unwrap();
            let index = index_source_exports(inventory.identity.clone(), &inventory.parsed).unwrap();
            if matches!(source.path, "lib/std/io/console.yu" | "lib/std/core/fmt.yu") {
                if source.path == "lib/std/io/console.yu" {
                    console_parsed = Some(inventory.parsed.clone());
                    provider_hirs.push(Arc::new(
                        yu_hir::shadow::lower_module_with_source_identity(
                            inventory.identity.clone(),
                            &inventory.parsed,
                            yu_hir::SemanticImports::empty(),
                        )
                        .unwrap_or_else(|error| panic!("{}: {error:?}", source.path)),
                    ));
                    ordinary_provider_hirs.push(Arc::new(
                        yu_hir::lower_module(
                            inventory.identity.clone(),
                            &inventory.parsed,
                            yu_hir::SemanticImports::empty(),
                        )
                        .unwrap_or_else(|error| panic!("{}: {error:?}", source.path)),
                    ));
                }
                if source.path == "lib/std/core/fmt.yu" {
                    provider_role_indexes.push(
                        index_role_impl_sources(inventory.identity.clone(), &inventory.parsed)
                            .unwrap_or_else(|error| panic!("{}: {error:?}", source.path)),
                    );
                }
            }
            assert_eq!(index.module, *inventory.identity.module());
            assert!(index.uses.iter().all(|item| {
                inventory.parsed.owns_source_key(&item.source)
                    && inventory.source.text.get(item.range.clone()) == Some(item.text.as_ref())
            }));
            assert!(index.declarations.iter().all(|item| {
                inventory.parsed.owns_source_key(&item.source)
                    && inventory.source.text.get(item.range.clone()) == Some(item.text.as_ref())
            }));
            assert!(
                indexed.insert(module, index).is_none(),
                "duplicate pinned module {}",
                source.path
            );
        }

        assert_eq!(indexed.len(), 40);
        let use_texts = |module: &str| {
            indexed[module]
                .uses
                .iter()
                .map(|item| item.text.as_ref())
                .collect::<Vec<_>>()
        };
        assert!(use_texts("std::prelude").iter().any(|text| text.contains("pub use std::core::fmt::*")));
        assert!(use_texts("std::prelude").iter().any(|text| text.contains("pub use std::io::*")));
        assert!(use_texts("std::io").iter().any(|text| text.contains("pub use std::io::console::*")));
        let console = &indexed["std::io::console"];
        for name in ["say", "println"] {
            assert!(console.declarations.iter().any(|item| {
                item.name.as_deref() == Some(name) && item.public && !item.recovered
            }), "missing public source declaration {name}");
        }
        let file_act = &indexed["std::io::file"];
        let members = file_act
            .declarations
            .iter()
            .filter(|item| item.namespace.as_ref() == "std::io::file::file")
            .collect::<Vec<_>>();
        assert_eq!(members.len(), 8);
        for (index, member) in members.iter().enumerate() {
            assert!(members[..index]
                .iter()
                .all(|earlier| earlier.range != member.range));
        }
        for name in ["load", "store", "meta"] {
            assert!(members.iter().any(|item| {
                item.name.as_deref() == Some(name) && item.public && !item.recovered
            }), "missing public host-act member {name}");
        }
        assert!(indexed["std::core::fmt"].declarations.iter().any(|item| {
            item.kind == yu_syntax::SyntaxKind::RoleDeclaration
                && item.name.as_deref() == Some("Display")
                && item.public
                && !item.recovered
        }));

        let indexes = indexed.into_values().collect::<Vec<_>>();
        let display = resolve_public_export(&indexes, "std::prelude", "Display").unwrap();
        assert_eq!(display.module.as_ref(), "std::core::fmt");
        assert_eq!(display.declaration.name.as_deref(), Some("Display"));
        assert_eq!(display.route.len(), 1);
        assert_eq!(
            display.route[0]
                .path
                .iter()
                .map(AsRef::as_ref)
                .collect::<Vec<_>>(),
            ["std", "core", "fmt"]
        );
        let display_owner = yu_hir::shadow::resolve_source_export_owner(
            &provider_hirs,
            &provider_role_indexes,
            &display,
        )
        .unwrap();
        let yu_hir::shadow::SourceExportOwner::Role { declaration, .. } = display_owner else {
            panic!("Display export must resolve to its provider role declaration")
        };
        let expected_display_id = declaration.id.clone();
        let display_implementations =
            yu_hir::shadow::resolve_source_role_implementations(
                &expected_display_id,
                &provider_role_indexes,
            )
            .expect("the authenticated Display role identifies its provider implementations");
        assert_eq!(display_implementations.role.id, expected_display_id);
        assert_eq!(
            display_implementations
                .module
                .module()
                .file()
                .key()
                .normalized_workspace_relative_path(),
            "lib/std/core/fmt.yu"
        );
        assert_eq!(display_implementations.implementations.len(), 14);
        let tuple_display = display_implementations
            .implementations
            .iter()
            .find(|implementation| implementation.target.text.trim() == "('a, 'b)")
            .expect("Display inventory contains the ordered two-element tuple implementation");
        assert_eq!(tuple_display.role.text.trim(), "Display");
        let tuple_show = tuple_display
            .body
            .as_ref()
            .unwrap()
            .entries
            .iter()
            .find_map(|entry| entry.member.as_ref())
            .expect("tuple implementation retains its show member identity");
        assert_eq!(tuple_show.implementation, tuple_display.id);
        assert_eq!(tuple_show.declaration, tuple_display.body.as_ref().unwrap().entries[2].source);
        assert!(matches!(
            yu_hir::shadow::resolve_source_role_implementations(
                &expected_display_id,
                &[],
            ),
            Err(yu_hir::shadow::SourceRoleImplementationError::MissingModule)
        ));
        let duplicated_role_indexes = [
            provider_role_indexes[0].clone(),
            provider_role_indexes[0].clone(),
        ];
        assert!(matches!(
            yu_hir::shadow::resolve_source_role_implementations(
                &expected_display_id,
                &duplicated_role_indexes,
            ),
            Err(yu_hir::shadow::SourceRoleImplementationError::DuplicateModule)
        ));
        let mut stale_display_id = expected_display_id.clone();
        stale_display_id.declaration = declaration
            .body
            .as_ref()
            .unwrap()
            .members[0]
            .id
            .declaration
            .clone();
        assert!(matches!(
            yu_hir::shadow::resolve_source_role_implementations(
                &stale_display_id,
                &provider_role_indexes,
            ),
            Err(yu_hir::shadow::SourceRoleImplementationError::StaleRole)
        ));
        let consumer_text: Arc<SourceText> = Arc::from("Display\n");
        let consumer_parsed = parse_file(
            consumer_text.clone(),
            Arc::new(scan_header(consumer_text)),
            Arc::new(playground_syntax_environment().unwrap()),
        );
        let consumer_identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
            "pinned-role-import-consumer",
            "consumer.yu",
        )));
        let unauthenticated_imports =
            SemanticImports::with_implicit_prelude(&consumer_parsed, &consumer_identity, &indexes)
                .unwrap();
        assert_eq!(
            unauthenticated_imports
                .source_imports()
                .unwrap()
                .role_id("Display"),
            None,
            "export lookup alone must not invent a provider role identity",
        );
        let consumer_imports = SemanticImports::with_implicit_prelude_and_role_indexes(
            &consumer_parsed,
            &consumer_identity,
            &indexes,
            &provider_role_indexes,
        )
        .unwrap();
        assert_eq!(
            consumer_imports
                .source_imports()
                .unwrap()
                .role_id("Display"),
            Some(&expected_display_id),
            "the consumer spelling must retain the exact role declaration identity",
        );
        let imported_display_id = consumer_imports
            .source_imports()
            .unwrap()
            .role_id("Display")
            .expect("the resolved public role import carries its exact source identity");
        let imported_display_implementations =
            yu_hir::shadow::resolve_source_role_implementations(
                imported_display_id,
                &provider_role_indexes,
            )
            .expect("the imported role identity reaches its authenticated implementation inventory");
        assert_eq!(
            imported_display_implementations.role.id,
            expected_display_id,
            "the consumer import and source implementation inventory share one role declaration",
        );
        let say = resolve_public_export(&indexes, "std::prelude", "say").unwrap();
        assert_eq!(say.module.as_ref(), "std::io::console");
        assert_eq!(say.declaration.name.as_deref(), Some("say"));
        assert_eq!(say.route.len(), 2);
        assert_eq!(
            say.route[0]
                .path
                .iter()
                .map(AsRef::as_ref)
                .collect::<Vec<_>>(),
            ["std", "io"]
        );
        assert_eq!(
            say.route[1]
                .path
                .iter()
                .map(AsRef::as_ref)
                .collect::<Vec<_>>(),
            ["std", "io", "console"]
        );
        let println = resolve_public_export(&indexes, "std::prelude", "println").unwrap();
        assert_eq!(println.module.as_ref(), "std::io::console");
        assert_eq!(println.declaration.name.as_deref(), Some("println"));
        assert_eq!(println.route.len(), 2);

        for resolution in [
            resolve_public_export(&indexes, "std::prelude", "println").unwrap(),
            display,
        ] {
            match yu_hir::shadow::resolve_source_export_owner(
                &provider_hirs,
                &provider_role_indexes,
                &resolution,
            )
            .unwrap_or_else(|error| panic!("{}: {error:?}", resolution.name))
            {
                yu_hir::shadow::SourceExportOwner::Binding { module, binding } => {
                    assert_eq!(binding.name().spelling(), resolution.name.as_ref());
                    assert_eq!(binding.visibility(), yu_hir::HirVisibility::Public);
                    assert_eq!(
                        module
                            .identity()
                            .module()
                            .file()
                            .key()
                            .normalized_workspace_relative_path(),
                        "lib/std/io/console.yu",
                    );
                }
                yu_hir::shadow::SourceExportOwner::Role { module, declaration } => {
                    assert_eq!(declaration.head.spelling.as_ref(), resolution.name.as_ref());
                    assert_eq!(declaration.visibility, yu_hir::HirVisibility::Public);
                    assert_eq!(
                        module.module().file().key().normalized_workspace_relative_path(),
                        "lib/std/core/fmt.yu",
                    );
                }
            }
        }
        let say = resolve_public_export(&indexes, "std::prelude", "say").unwrap();
        assert!(
            matches!(
                yu_hir::shadow::resolve_source_export_owner(
                    &provider_hirs,
                    &provider_role_indexes,
                    &say,
                ),
                Err(yu_hir::shadow::SourceExportOwnerError::StaleDeclaration)
            ),
            "the pinned say source declaration is exported but has no admitted binding owner in provider HIR",
        );
        let say_owner = yu_hir::shadow::resolve_source_export_owner(
            &ordinary_provider_hirs,
            &provider_role_indexes,
            &say,
        )
        .unwrap_or_else(|error| panic!("{}: {error:?}", say.name));
        let yu_hir::shadow::SourceExportOwner::Binding { module, binding } = say_owner else {
            panic!("say must be retained as its provider value binding")
        };
        let carrier = module
            .local_source(binding.definition_root())
            .unwrap_or_else(|error| panic!("say carrier: {error:?}"))
            .expect("LocalSource-aware provider must retain say's source carrier");
        assert_eq!(carrier.definition_root(), Some(binding.definition_root()));
        assert_eq!(carrier.where_clauses().len(), 1);
        let where_clause = &carrier.where_clauses()[0];
        assert_eq!(
            module
                .identity()
                .module()
                .file()
                .key()
                .normalized_workspace_relative_path(),
            "lib/std/io/console.yu"
        );
        assert!(where_clause.text.contains("where 'a: Display"));
        assert_eq!(where_clause.subject.text.trim(), "'a");
        assert_eq!(where_clause.role.text.trim(), "Display");
        assert!(console_parsed
            .as_ref()
            .expect("pinned console parse retained")
            .owns_source_key(&where_clause.source));
        let mut stale_println =
            resolve_public_export(&indexes, "std::prelude", "println").unwrap();
        stale_println.declaration.range.start += 1;
        assert!(matches!(
            yu_hir::shadow::resolve_source_export_owner(
                &provider_hirs,
                &provider_role_indexes,
                &stale_println,
            ),
            Err(yu_hir::shadow::SourceExportOwnerError::StaleDeclaration)
        ));
        let println = resolve_public_export(&indexes, "std::prelude", "println").unwrap();
        assert!(matches!(
            yu_hir::shadow::resolve_source_export_owner(
                &[provider_hirs[0].clone(), provider_hirs[0].clone()],
                &provider_role_indexes,
                &println,
            ),
            Err(yu_hir::shadow::SourceExportOwnerError::DuplicateModule)
        ));
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
    fn pinned_stdlib_role_impl_sources_keep_distinct_module_identities() {
        use std::collections::HashSet;

        let sources = pinned_stdlib::resolve_implicit_stdlib().unwrap();
        assert_eq!(sources.len(), 40);
        let mut modules = HashSet::new();
        let mut roles = HashSet::new();
        let mut implementations = HashSet::new();
        let mut diagnostic_count = 0usize;
        let mut recovered_roles = 0usize;
        let mut recovered_implementations = 0usize;
        let mut recovered_paths = HashSet::new();

        for source in sources.iter() {
            let environment = Arc::new(
                pinned_stdlib::syntax_environment_for_source(source, &sources)
                    .unwrap_or_else(|error| panic!("{}: {error:?}", source.path)),
            );
            let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
                "yulang2-pinned-stdlib",
                source.path,
            )));
            assert!(modules.insert(identity.module().clone()), "{}", source.path);
            let text: Arc<SourceText> = Arc::from(source.text);
            let parsed = parse_file(
                text.clone(),
                Arc::new(scan_header(text)),
                environment.clone(),
            );
            let diagnostics = parsed.syntax_diagnostics().unwrap();
            diagnostic_count += diagnostics.len();
            let index = index_role_impl_sources(identity.clone(), &parsed)
                .unwrap_or_else(|error| {
                    panic!(
                        "{}: {error:?}; syntax diagnostics {}, first {:?}",
                        source.path,
                        diagnostics.len(),
                        diagnostics
                            .iter()
                            .take(12)
                            .map(|item| {
                                let range = item.primary().clone();
                                (range.clone(), source.text.get(range).unwrap_or("<invalid>"))
                            })
                            .collect::<Vec<_>>()
                    )
                });
            assert_eq!(index.module(), identity.module());
            for role in index.roles() {
                assert_eq!(role.id.module.as_ref(), identity.module(), "{}", source.path);
                assert!(roles.insert(role.id.clone()), "{}", source.path);
                if role.recovered {
                    recovered_roles += 1;
                    recovered_paths.insert(source.path);
                }
                for member in role.body.iter().flat_map(|body| &body.members) {
                    assert_eq!(member.id.role, role.id, "{}", source.path);
                    assert_eq!(
                        &source.text[member.range.clone()],
                        member.text.as_ref(),
                        "{}",
                        source.path
                    );
                }
            }
            for implementation in index.implementations() {
                assert_eq!(
                    implementation.id.module.as_ref(),
                    identity.module(),
                    "{}",
                    source.path
                );
                assert!(
                    implementations.insert(implementation.id.clone()),
                    "{}",
                    source.path
                );
                if implementation.recovered {
                    recovered_implementations += 1;
                    recovered_paths.insert(source.path);
                }
                for entry in implementation.body.iter().flat_map(|body| &body.entries) {
                    assert_eq!(
                        &source.text[entry.range.clone()],
                        entry.text.as_ref(),
                        "{}",
                        source.path
                    );
                    if let Some(member) = &entry.member {
                        assert_eq!(member.implementation, implementation.id, "{}", source.path);
                    }
                }
            }
        }
        assert!(roles.iter().any(|role| role.module.file().key().normalized_workspace_relative_path()
            == "lib/std/core/fmt.yu"));
        assert!(implementations.iter().any(|implementation| {
            implementation.module.file().key().normalized_workspace_relative_path()
                == "lib/std/core/fmt.yu"
        }));
        eprintln!(
            "indexed {} modules, {} root roles ({} recovered), {} standalone impls ({} recovered) in {:?}; {} total parser diagnostics",
            modules.len(), roles.len(), recovered_roles, implementations.len(),
            recovered_implementations, recovered_paths, diagnostic_count
        );
    }

    #[test]
    fn pinned_int_add_lowers_from_its_exact_selected_source_root() {
        let sources = pinned_stdlib::resolve_implicit_stdlib().unwrap();
        let mut parsed_sources = Vec::new();
        let mut indexes = Vec::new();
        for source in sources.iter() {
            let text: Arc<SourceText> = Arc::from(source.text);
            let parsed = parse_file(
                text.clone(),
                Arc::new(scan_header(text)),
                Arc::new(pinned_stdlib::syntax_environment_for_source(source, &sources).unwrap()),
            );
            let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("pinned-yulang2", source.path)));
            indexes.push(index_source_exports(identity.clone(), &parsed).unwrap());
            parsed_sources.push((source.path, identity, parsed));
        }
        let export = resolve_public_export(&indexes, "std::int", "add").unwrap();
        let (path, identity, parsed) = parsed_sources.iter().find(|(path, _, _)| *path == "lib/std/int.yu").unwrap();
        assert_eq!(*path, "lib/std/int.yu");
        assert_eq!(export.declaration.text.trim(), "pub add: int -> int -> int = builtin_op::int_add");
        let selected = [export.declaration.source.clone()].into_iter().collect::<std::collections::HashSet<_>>();
        let imports = SemanticImports::with_selected_source_imports(parsed, identity, &indexes, &selected).unwrap();
        assert!(imports.source_imports().unwrap().resolve("builtin_op").is_none());
        let projected = lower_module_with_selected_local_source(identity.clone(), parsed, imports, selected).unwrap();
        assert_eq!(projected.items().len(), 1);
        let HirItem::Binding(binding) = &projected.items()[0] else { panic!("selected export remains a binding") };
        assert_eq!(binding.name().spelling(), "add");
        assert!(projected.local_source(binding.definition_root()).unwrap().is_some());
        assert!(projected.errors().iter().all(|error| !matches!(error.attachment(), yu_hir::HirErrorAttachment::Module)));
        assert!(projected.errors().iter().all(|error| error.kind() != yu_hir::HirErrorKind::UnresolvedName), "selected imported names stay source-resolved: {:?}", projected.errors());
        let local = projected.local_source(binding.definition_root()).unwrap().unwrap();
        assert!(local.expressions().iter().any(|expression| matches!(
            &expression.form,
            LocalSourceForm::Primitive { operation: yu_hir::shadow::PinnedPrimitiveOp::IntAdd },
        )), "the pinned builtin registry owns int_add as a distinct primitive identity");
        let projected_candidate = CandidateInference::solve(Arc::new(projected)).expect("the exact projected int provider enters candidate collection");
        assert!(projected_candidate.candidate_conflicts().is_empty());
    }

    #[test]
    fn pinned_int_add_signature_enters_candidate_collection() {
        let source: Arc<SourceText> = Arc::from(
            "pub add: int -> int -> int = builtin_op::int_add\npub to_text: int -> str = builtin_op::int_to_string\npub concat: str -> str -> str = builtin_op::string_concat",
        );
        let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("pinned-primitive-test", "int.yu"))),
            &parsed,
            SemanticImports::empty(),
        ).unwrap());
        let candidate = CandidateInference::solve(hir).expect("the exact pinned primitive identity has a typed candidate owner");
        assert!(candidate.candidate_conflicts().is_empty(), "int_add has a consistent pure curried signature");

        let source: Arc<SourceText> = Arc::from("pub wrong: str -> str -> str = builtin_op::int_add");
        let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("pinned-primitive-test", "wrong.yu"))),
            &parsed,
            SemanticImports::empty(),
        ).unwrap());
        let mismatch = CandidateInference::solve(hir).expect("candidate inference reports a typed signature conflict");
        assert!(!mismatch.candidate_conflicts().is_empty(), "int_add cannot take string operands");
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
