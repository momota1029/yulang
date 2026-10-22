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
    let name = if name == "-" { "stdin.yu" } else { name };
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
    let (provider_sources, indexes, role_indexes) = pinned_source_world()?;
    let imports = match SemanticImports::with_source_imports_and_role_indexes(&parsed, &identity, &indexes, &role_indexes) {
        Ok(imports) => imports,
        Err(import_error @ yu_hir::HirAvailabilityError::StructuralProjection) => {
            // Keep this fallback closed: only a source with no explicit
            // imports and no HIR errors can ignore unavailable
            // implicit-prelude routes.
            let local = lower_module_with_local_source(
                identity.clone(), &parsed, SemanticImports::empty(),
            );
            let no_explicit_imports = parsed.header().imports().is_empty();
            let locally_resolved = no_explicit_imports && local.as_ref().is_ok_and(|module|
                module.errors().is_empty()
            );
            if locally_resolved {
                SemanticImports::empty()
            } else {
                return Err(bounded_message(format_args!(
                    "source imports unavailable: {import_error:?}"
                )));
            }
        }
        Err(error) => return Err(bounded_message(format_args!("source imports unavailable: {error:?}"))),
    };
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
        let providers = pinned_provider_projection(&hir, &provider_sources, &indexes, &role_indexes)?;
        let mut modules = providers;
        modules.push(hir.clone());
        CandidateInference::solve_modules_with_role_sources(modules, &indexes, &role_indexes)
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

type PinnedProviderSource = (ModuleIdentity, yu_syntax::ParsedFile);

fn pinned_source_world() -> Result<(Vec<PinnedProviderSource>, Vec<yu_hir::SourceExportIndex>, Vec<yu_hir::shadow::SourceRoleImplIndex>), String> {
    use yu_syntax::{SourceText, parse_file, scan_header};

    let sources = pinned_stdlib::resolve_implicit_stdlib()
        .map_err(|error| format!("pinned standard-library bundle unavailable: {error:?}"))?;
    let mut parsed_sources = Vec::new();
    let mut indexes = Vec::new();
    let mut role_indexes = Vec::new();
    parsed_sources.try_reserve_exact(sources.len()).map_err(|_| "pinned source allocation unavailable".to_owned())?;
    indexes.try_reserve_exact(sources.len()).map_err(|_| "pinned index allocation unavailable".to_owned())?;
    role_indexes.try_reserve_exact(sources.len()).map_err(|_| "pinned role index allocation unavailable".to_owned())?;
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
            .map_err(|error| format!("pinned source index unavailable: {error:?}"))?
            .with_source_revision(SourceRevision::from_fingerprint(
                pinned_stdlib::fingerprint(&source.git_blob),
            )));
        role_indexes.push(yu_hir::shadow::index_role_impl_sources(identity.clone(), &parsed)
            .map_err(|error| format!("pinned role index unavailable for {}: {error:?}", source.path))?);
        parsed_sources.push((identity, parsed));
    }
    Ok((parsed_sources, indexes, role_indexes))
}

/// Project only exact exported binding roots reached from imported Names,
/// then recursively follow their SourceExportId dependencies.
fn pinned_provider_projection(
    consumer: &HirModule,
    sources: &[PinnedProviderSource],
    indexes: &[yu_hir::SourceExportIndex],
    role_indexes: &[yu_hir::shadow::SourceRoleImplIndex],
) -> Result<Vec<Arc<HirModule>>, String> {
    use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution};
    use std::collections::HashSet;

    fn imported_exports(hir: &HirModule) -> Result<Vec<yu_hir::shadow::SourceExportId>, String> {
        let mut exports = Vec::new();
        for item in hir.items() {
            let HirItem::Binding(binding) = item else { continue };
            let Some(source) = hir.local_source(binding.definition_root())
                .map_err(|error| format!("provider source lookup unavailable: {error:?}"))?
            else { continue };
            for expression in source.expressions() {
                if let LocalSourceForm::Name {
                    resolution: LocalSourceResolution::Imported(export), ..
                } = &expression.form
                {
                    if !exports.contains(export) {
                        exports.try_reserve(1).map_err(|_| "provider dependency allocation unavailable".to_owned())?;
                        exports.push(export.clone());
                    }
                }
            }
        }
        Ok(exports)
    }

    let mut selected = (0..sources.len()).map(|_| HashSet::new()).collect::<Vec<_>>();
    let mut built = (0..sources.len()).map(|_| None).collect::<Vec<Option<Arc<HirModule>>>>();
    let mut pending = imported_exports(consumer)?;
    let mut seen = HashSet::new();
    while let Some(export) = pending.pop() {
        if !seen.insert(export.clone()) { continue; }
        let owner = indexes.iter().enumerate().find_map(|(index, source_index)| {
            source_index.declarations.iter().find(|declaration|
                declaration.source == export.source
                    && declaration.name.as_deref() == Some(export.name.as_ref())
                    && declaration.namespace.as_ref() == export.module.as_ref()
            ).map(|declaration| (index, declaration))
        });
        let Some((source_index, declaration)) = owner else {
            return Err(format!("pinned provider owner missing for {}::{}", export.module, export.name));
        };
        if declaration.kind != yu_syntax::SyntaxKind::BindingStatement { continue; }
        if !selected[source_index].insert(export.source.clone()) { continue; }
        let (identity, parsed) = &sources[source_index];
        let imports = SemanticImports::with_selected_source_imports_and_role_indexes(
            parsed, identity, indexes, &selected[source_index], role_indexes,
        ).map_err(|error| format!("selected pinned imports unavailable for {}: {error:?}", identity.file().key().normalized_workspace_relative_path()))?;
        let projected = yu_hir::shadow::lower_module_with_selected_local_source(
            identity.clone(), parsed, imports, selected[source_index].clone(),
        ).map_err(|error| format!("selected pinned source HIR unavailable for {}: {error:?}", identity.file().key().normalized_workspace_relative_path()))?;
        let projected = Arc::new(projected);
        let dependencies = imported_exports(&projected)?;
        pending.try_reserve(dependencies.len()).map_err(|_| "provider dependency allocation unavailable".to_owned())?;
        pending.extend(dependencies);
        built[source_index] = Some(projected);
    }

    let mut providers = Vec::new();
    providers.try_reserve(built.iter().filter(|module| module.is_some()).count())
        .map_err(|_| "pinned provider allocation unavailable".to_owned())?;
    providers.extend(built.into_iter().flatten());
    Ok(providers)
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
    use super::{conflict_ranges_for, execute, pinned_provider_projection, pinned_source_world, prepare};
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
    fn pinned_provider_projection_follows_exact_imported_value_roots() {
        let source = "use std::int::add\nmy result = add 20 22";
        let text: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(
            text.clone(), Arc::new(scan_header(text)),
            Arc::new(playground_syntax_environment().unwrap()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
            "pinned-demand-projection", "consumer.yu",
        )));
        let (provider_sources, indexes, role_indexes) = pinned_source_world().unwrap();
        let imports = SemanticImports::with_source_imports_and_role_indexes(&parsed, &identity, &indexes, &role_indexes).unwrap();
        let consumer = Arc::new(lower_module_with_local_source(identity, &parsed, imports).unwrap());
        let providers = pinned_provider_projection(&consumer, &provider_sources, &indexes, &role_indexes).unwrap();
        assert_eq!(providers.len(), 1, "only std::int::add is demanded");
        let exported_names = providers[0].items().iter().filter_map(|item| match item {
            HirItem::Binding(binding) => Some(binding.name().spelling()),
            _ => None,
        }).collect::<Vec<_>>();
        assert_eq!(exported_names, ["add"]);
    }

    #[test]
    fn unchanged_types_sample_reaches_deferred_field_tail_boundary() {
        let source = "// our and pub bindings appear in the Types pane.\n\nour id x = x\npub answer = id 42\npub name = id \"Yulang\"\npub pair = (answer, name)\n\npair.say\n";
        assert_eq!(source.len(), 142);
        let error = match prepare(source, "samples/Types.yu", false) {
            Err(error) => error,
            Ok(_) => panic!("pair.say remains behind deferred role selection"),
        };
        assert!(error.contains("candidate inference unavailable: Solve(DeferredSelectionUnavailable)"), "{error}");
        assert!(!error.contains("source imports unavailable"), "provider projection reaches candidate collection: {error}");
    }

    #[test]
    fn unchanged_types_sample_reads_receiver_bounds_from_its_pinned_module_session() {
        let source = "// our and pub bindings appear in the Types pane.\n\nour id x = x\npub answer = id 42\npub name = id \"Yulang\"\npub pair = (answer, name)\n\npair.say\n";
        assert_eq!(source.len(), 142);
        let text: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(
            text.clone(), Arc::new(scan_header(text)),
            Arc::new(playground_syntax_environment().unwrap()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
            "inference-playground", "samples/Types.yu",
        )));
        let (provider_sources, indexes, role_indexes) = pinned_source_world().unwrap();
        let imports = SemanticImports::with_source_imports_and_role_indexes(
            &parsed, &identity, &indexes, &role_indexes,
        ).unwrap();
        let hir = Arc::new(lower_module_with_local_source(identity, &parsed, imports).unwrap());
        let expected_display_id = role_indexes.iter().flat_map(|index| index.roles())
            .find(|role| role.head.spelling.as_ref() == "Display"
                && role.id.module.file().key().normalized_workspace_relative_path() == "lib/std/core/fmt.yu")
            .expect("the pinned fmt module owns Display").id.clone();
        let global_inventory = yu_hir::shadow::resolve_source_role_implementation_candidates(
            &expected_display_id, &indexes, &role_indexes,
        ).expect("relative imports in the complete pinned world resolve from their owning module");
        assert!(global_inventory.implementations.iter().any(|candidate|
            candidate.implementation.id.module.file().key().normalized_workspace_relative_path()
                == "lib/std/text/path.yu"));
        assert!(global_inventory.implementations.iter().any(|candidate|
            candidate.implementation.id.module.file().key().normalized_workspace_relative_path()
                == "lib/std/time.yu"));
        assert_eq!(global_inventory.implementations.len(), 16,
            "the pinned source census retains all Display implementations across fmt, path, and time");
        let unsupported_targets = global_inventory.implementations.iter()
            .filter(|candidate| candidate.implementation.target.shape.is_none())
            .map(|candidate| candidate.implementation.target.text.as_ref())
            .collect::<Vec<_>>();
        assert_eq!(unsupported_targets, ["(list 'a)", "(opt 'a)", "(result 'ok 'err)"],
            "unsupported target syntax stays source-visible and cannot match the primitive where subjects");
        for target_name in ["int", "str"] {
            let matches = global_inventory.implementations.iter().filter(|candidate|
                candidate.implementation.target.shape.as_ref()
                    == Some(&yu_hir::shadow::SourceImplementationTypeShape::Name(target_name.into()))
            ).collect::<Vec<_>>();
            let [matched] = matches.as_slice() else {
                panic!("the exact pinned Display inventory has one {target_name} implementation")
            };
            assert!(matched.implementation.body.as_ref().unwrap().entries.iter()
                .all(|entry| entry.kind != yu_syntax::SyntaxKind::WhereClause),
                "the concrete {target_name} implementation has no source prerequisites");
        }
        let mut modules = pinned_provider_projection(&hir, &provider_sources, &indexes, &role_indexes).unwrap();
        modules.push(hir);

        let readbacks = CandidateInference::inspect_deferred_field_tails_and_member_freshuse_with_role_sources(
            modules, &indexes, &role_indexes,
        ).unwrap();
        let matching_say = readbacks.receivers.iter().filter(|item| item.member.as_ref() == "say")
            .collect::<Vec<_>>();
        let [say] = matching_say.as_slice() else {
            panic!("the unchanged sample has exactly one deferred say receiver")
        };
        assert_eq!(say.positive_shape.as_ref(), Some(&
            yu_solver::shadow_apply::CandidateReceiverShape::Tuple(vec![
                yu_solver::shadow_apply::CandidateReceiverShape::Int,
                yu_solver::shadow_apply::CandidateReceiverShape::Str,
            ]),
        ), "pinned imports and ordinary source schedules preserve tuple element order: {say:?}");
        assert!(say.positive_frontier_complete, "all positive lower rows and tuple children were visited: {say:?}");
        assert!(say.negative_frontier_empty, "no reachable receiver upper row or endpoint is present: {say:?}");
        assert_eq!(say.reachable_negative_row_edges, 0, "{say:?}");
        assert_eq!(say.reachable_negative_bounds, 0, "{say:?}");
        assert!(say.implementation_inventory_complete, "all source-owned implementations for the exact retained Display.say identity are inventoried: {say:?}");
        assert_eq!(say.unsupported_target_count, 3, "the local Display inventory exposes three additional unsupported targets, so selection remains unavailable: {say:?}");
        let [tuple_match] = say.target_matches.as_slice() else {
            panic!("the exact ordered pair has one structural target match: {say:?}")
        };
        assert_eq!(tuple_match.target, yu_hir::shadow::SourceImplementationTypeShape::Tuple(vec![
            yu_hir::shadow::SourceImplementationTypeShape::Name("'a".into()),
            yu_hir::shadow::SourceImplementationTypeShape::Name("'b".into()),
        ]));
        assert_eq!(tuple_match.type_substitution, [
            ("'a".into(), yu_hir::shadow::SourceImplementationTypeShape::Name("int".into())),
            ("'b".into(), yu_hir::shadow::SourceImplementationTypeShape::Name("str".into())),
        ]);
        assert_eq!(tuple_match.where_clause_count, 2);
        assert_eq!(tuple_match.where_role_identities,
            [Some(expected_display_id.clone()), Some(expected_display_id.clone())]);
        assert_eq!(tuple_match.where_clause_readbacks.len(), 2);
        for (clause, (subject, concrete)) in tuple_match.where_clause_readbacks.iter().zip([
            ("'a", "int"), ("'b", "str"),
        ]) {
            assert!(clause.subject_source.is_some(), "where subject keeps source identity: {clause:?}");
            assert_eq!(clause.subject.as_ref(), Some(&
                yu_hir::shadow::SourceImplementationTypeShape::Name(subject.into())));
            assert_eq!(clause.substituted_subject.as_ref(), Some(&
                yu_hir::shadow::SourceImplementationTypeShape::Name(concrete.into())));
            assert_eq!(clause.role_identity, Some(expected_display_id.clone()));
            assert_eq!(clause.matching_implementations.len(), 1, "{clause:?}");
            assert_eq!(clause.matching_implementations_without_prerequisites,
                clause.matching_implementations, "{clause:?}");
            assert_eq!(clause.matching_implementations[0].module.file().key()
                .normalized_workspace_relative_path(), "lib/std/core/fmt.yu");
        }
        assert_eq!(readbacks.captured_member_graph_count, 0,
            "the binding-only provider projection has no imported implementation member graphs");
        assert!(readbacks.captured_member_field_tails.is_empty(),
            "source role inventory does not imply that implementation body HIR entered the session");
    }

    #[test]
    fn unchanged_console_sample_reaches_imported_name_candidate_boundary() {
        let source = "// println is a library effect handled by the host.\n\nprintln \"hello from Yulang\"\nsay: 1 + 2\n";
        assert_eq!(source.len(), 92);
        let error = match prepare(source, "samples/Console.yu", false) {
            Err(error) => error,
            Ok(_) => panic!("Console still requires imported operation/host selection"),
        };
        assert!(error.starts_with("unsupported source: current candidate lowering/inference cannot observe this program"), "{error}");
        assert!(!error.contains("source imports unavailable"), "provider projection reaches candidate preflight: {error}");
    }

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
        let display_members = &display.body.as_ref().unwrap().members;
        let show_signature = display_members[0].header.as_ref().expect("dotted role signature header");
        assert_eq!(show_signature.receiver.spelling.as_ref(), "a");
        assert_eq!(show_signature.method.spelling.as_ref(), "show");
        assert_eq!(show_signature.annotation.as_ref().unwrap().text.as_ref(), "str");
        let say_header = display_members[1].header.as_ref().expect("dotted role default header");
        assert_eq!(say_header.receiver.spelling.as_ref(), "a");
        assert_eq!(say_header.method.spelling.as_ref(), "say");
        assert!(say_header.annotation.is_none());

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
        assert_eq!(tuple_display.body.as_ref().unwrap().entries[..2].iter()
            .map(|entry| {
                let where_clause = entry.where_clause.as_ref().expect("structured implementation where clause");
                (where_clause.subject.text.trim().to_owned(), where_clause.role.text.trim().to_owned())
            }).collect::<Vec<_>>(), [("'a".to_owned(), "Display".to_owned()), ("'b".to_owned(), "Display".to_owned())]);
        assert_eq!(
            tuple_display.body.as_ref().unwrap().entries[2].kind,
            yu_syntax::SyntaxKind::BindingStatement
        );
        let show_header = tuple_display.body.as_ref().unwrap().entries[2].header.as_ref()
            .expect("dotted implementation method header");
        assert_eq!(show_header.receiver.spelling.as_ref(), "value");
        assert_eq!(show_header.method.spelling.as_ref(), "show");
        assert!(show_header.annotation.is_none());
        for entry in &tuple_display.body.as_ref().unwrap().entries {
            assert_eq!(
                &inventory.source.text[entry.range.clone()],
                entry.text.as_ref()
            );
            if let Some(member) = &entry.member {
                assert_eq!(member.implementation, tuple_display.id);
            }
        }

        let carrier_hir = yu_hir::shadow::lower_module_with_member_sources(
            inventory.identity.clone(),
            &inventory.parsed,
            SemanticImports::empty(),
        )
        .expect("the exact pinned fmt source forms member-owned body carriers");
        let say = display.body.as_ref().unwrap().members.iter()
            .find(|member| member.text.trim_start().starts_with("pub a.say ="))
            .unwrap();
        let say_root = carrier_hir.source_role_member_root(&say.id).unwrap().unwrap();
        let say_carrier = carrier_hir.source_carrier_for(&say_root).unwrap().unwrap();
        assert!(matches!(say_carrier, yu_hir::SourceCarrierOutcome::Unsupported(failure)
            if failure.reason == yu_hir::SourceCarrierFailureReason::UnsupportedForm),
            "the exact Display.say source member currently reaches its known operator-form boundary");
        let tuple_show = tuple_display.body.as_ref().unwrap().entries[2].member.as_ref().unwrap();
        let show_root = carrier_hir.source_implementation_member_root(tuple_show).unwrap().unwrap();
        let show_carrier = carrier_hir.source_carrier_for(&show_root).unwrap().unwrap();
        let yu_hir::SourceCarrierOutcome::Supported(show_source) = show_carrier else {
            panic!("the exact ordered-pair Display.show source member retains its parser-associated infix tree: {show_carrier:?}");
        };
        let yu_hir::LocalSourceForm::Case { arms, .. } = &show_source.expression(show_source.body()).unwrap().form else {
            panic!("the pinned show body retains its tuple case");
        };
        let show_body_index = &arms[0].body;
        let show_body = show_source.expression(show_body_index).unwrap();
        let associated = yu_hir::associate_operator_chains(&inventory.parsed);
        fn find_associated_range<'a>(
            expression: &'a yu_hir::HirExpr,
            target: &std::ops::Range<usize>,
            found: &mut Vec<&'a yu_hir::HirExpr>,
        ) {
            if expression.range() == target { found.push(expression); }
            match expression {
                yu_hir::HirExpr::Apply { operands, .. } => {
                    for operand in operands.iter() { find_associated_range(operand, target, found); }
                }
                yu_hir::HirExpr::Value { children, .. } | yu_hir::HirExpr::Error { children, .. } => {
                    for child in children { find_associated_range(child, target, found); }
                }
            }
        }
        let mut associated_roots = Vec::new();
        for chain in associated.chains() {
            find_associated_range(chain.expression(), &show_body.range, &mut associated_roots);
        }
        let [associated_root] = associated_roots.as_slice() else {
            panic!("one parser-associated node owns the pinned show body range: {:?}", associated_roots.len());
        };
        fn compare_association(
            parsed: &yu_syntax::ParsedFile,
            source: &yu_hir::LocalSource,
            index: &yu_hir::LocalSourceIndex,
            associated: &yu_hir::HirExpr,
        ) -> usize {
            let local = source.expression(index).expect("associated local expression");
            assert_eq!(local.range, *associated.range());
            assert!(parsed.owns_source_key(&local.source));
            match (associated, &local.form) {
                (
                    yu_hir::HirExpr::Apply { operator, operands, .. },
                    yu_hir::LocalSourceForm::InfixOperator {
                        operator_source, operator: local_operator, left, right,
                    },
                ) => {
                    assert_eq!(operator, local_operator);
                    assert!(parsed.owns_source_key(operator_source));
                    let [left_associated, right_associated] = operands.as_ref() else {
                        panic!("pinned infix application is binary")
                    };
                    1 + compare_association(parsed, source, left, left_associated)
                        + compare_association(parsed, source, right, right_associated)
                }
                (yu_hir::HirExpr::Value { .. }, _) => 0,
                (yu_hir::HirExpr::Error { .. }, _) => panic!("pinned operator association has no recovery node"),
                _ => panic!("local source operator tree disagrees with parser association: {associated:?} / {:?}", local.form),
            }
        }
        assert_eq!(compare_association(
            &inventory.parsed, show_source, show_body_index, associated_root,
        ), 4, "all four parser-associated operators and ordered operands remain source-owned");
        assert!(matches!(say_root, SourceRootId::Member(ref root)
            if root.kind() == yu_hir::SourceMemberKind::Role));
        assert!(matches!(show_root, SourceRootId::Member(ref root)
            if root.kind() == yu_hir::SourceMemberKind::Implementation));
    }

    #[test]
    fn member_body_receiver_is_a_source_parameter_not_a_synthetic_lambda() {
        let source = "role Echo:\n    our receiver.echo = receiver\nimpl int: Echo:\n    our value.echo = value";
        let text: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(
            text.clone(), Arc::new(scan_header(text)), Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
            "member-receiver-root-input", "members.yu",
        )));
        let hir = yu_hir::shadow::lower_module_with_member_sources(
            identity, &parsed, SemanticImports::empty(),
        ).unwrap();
        let carriers = hir.source_member_carrier_outcomes();
        assert_eq!(carriers.len(), 2);
        for (owner, outcome) in carriers {
            let yu_hir::SourceCarrierOutcome::Supported(local_source) = outcome else {
                panic!("simple member body should form a LocalSource: {outcome:?}");
            };
            assert_eq!(local_source.root_parameters().len(), 1);
            let receiver = &local_source.root_parameters()[0];
            let expected = match owner.member_root().unwrap().kind() {
                yu_hir::SourceMemberKind::Role => "receiver",
                yu_hir::SourceMemberKind::Implementation => "value",
            };
            assert_eq!(receiver.spelling.as_ref(), expected);
            assert!(parsed.owns_source_key(&receiver.source));
            assert_eq!(&source[receiver.range.clone()], expected);
            assert!(matches!(&local_source.expressions()[0].form,
                LocalSourceForm::Name { spelling, resolution: yu_hir::shadow::LocalSourceResolution::Parameter(id) }
                    if spelling.as_ref() == expected && id == &receiver.id));
            assert!(matches!(local_source.expressions()[0].scope,
                yu_hir::shadow::LocalSourceScope::Parameter(ref id) if id == &receiver.id));
            assert_eq!(local_source.expressions().len(), 1, "receiver entry is metadata, not a fake Lambda expression");
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
        let display_say = declaration.body.as_ref().unwrap().members.iter()
            .find(|member| member.text.trim_start().starts_with("pub a.say ="))
            .expect("pinned Display role owns the default say member");
        let resolved_display_say = yu_hir::shadow::resolve_source_role_member(
            &expected_display_id, "say", &provider_role_indexes,
        ).expect("exact Display identity resolves its source-owned say member");
        assert_eq!(resolved_display_say.id, display_say.id);
        assert!(matches!(
            yu_hir::shadow::resolve_source_role_member(
                &expected_display_id, "not_a_display_member", &provider_role_indexes,
            ),
            Err(yu_hir::shadow::SourceRoleMemberError::MissingMember),
        ));
        assert_eq!(display_say.id.role, expected_display_id);
        assert!(!display_say.recovered);
        assert!(display_say.text.contains("std::io::out::write"));
        assert!(display_say.text.contains("a.show"));
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
        assert_eq!(
            display_implementations.implementations.iter()
                .filter(|implementation| implementation.target.text.trim() == "('a, 'b)")
                .count(),
            1,
            "the authenticated Display inventory has one ordered-pair target",
        );
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
        let all_display_implementations = yu_hir::shadow::resolve_source_role_implementation_candidates(
            &expected_display_id, &indexes, &provider_role_indexes,
        ).expect("all cross-module Display implementation heads resolve to the exact role");
        let display_say_candidates = yu_hir::shadow::resolve_source_role_implementation_members(
            &resolved_display_say.id, &all_display_implementations, &provider_role_indexes,
        ).expect("the exact say member joins each implementation override");
        let tuple_say = display_say_candidates.implementations.iter()
            .find(|candidate| candidate.target.text.trim() == "('a, 'b)")
            .expect("the ordered-pair implementation remains in the authenticated candidate set");
        assert_eq!(tuple_say.where_clauses.len(), 2);
        assert_eq!(tuple_say.where_clauses.iter().map(|clause| {
            let clause = clause.as_ref().expect("supported generic role prerequisite");
            (clause.subject.text.trim(), clause.role.text.trim())
        }).collect::<Vec<_>>(), [("'a", "Display"), ("'b", "Display")]);
        assert_eq!(tuple_say.where_roles, [Some(expected_display_id.clone()), Some(expected_display_id.clone())],
            "both generic prerequisites resolve through the implementation module to the exact imported Display role");
        assert_eq!(tuple_say.member, None,
            "the tuple implementation has no say override, so its default stays a separate source member");
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
        assert_eq!(
            unauthenticated_imports.source_imports().unwrap().role_member_id("Display", "say"),
            None,
            "export lookup alone must not invent a role-member identity",
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
        assert_eq!(
            consumer_imports.source_imports().unwrap().role_member_id("Display", "say"),
            Some(&resolved_display_say.id),
            "the imported role retains the exact source-owned member identity",
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
            .unwrap_or_else(|| panic!(
                "LocalSource-aware provider must retain say's source carrier; outcome: {:?}",
                module.source_carrier(binding.definition_root()).unwrap(),
            ));
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
        let (_, operator_source_indexes, _) = pinned_source_world().unwrap();
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
            if source.path == "lib/std/core/fmt.yu" {
                fn operator_at<'a>(expression: &'a yu_hir::HirExpr, range: &std::ops::Range<usize>) -> Option<&'a yu_hir::HirOperator> {
                    match expression {
                        yu_hir::HirExpr::Apply { operator, operands, .. } => {
                            if operator.range().start <= range.start && range.start < operator.range().end {
                                return Some(operator);
                            }
                            operands.iter().find_map(|operand| operator_at(operand, range))
                        }
                        yu_hir::HirExpr::Value { children, .. } | yu_hir::HirExpr::Error { children, .. } => {
                            children.iter().find_map(|child| operator_at(child, range))
                        }
                    }
                }
                let plus_start = source.text.find("a.show + \"\\n\"")
                    .expect("pinned Display.say plus source") + "a.show ".len();
                let plus_range = plus_start..plus_start + 1;
                let associated = yu_hir::associate_operator_chains(&parsed);
                let operator = associated.chains().iter()
                    .filter(|chain| chain.range().start <= plus_start && plus_start < chain.range().end)
                    .find_map(|chain| operator_at(chain.expression(), &plus_range))
                    .expect("the original Display.say + occurrence reaches HIR after glob import retention");
                assert_eq!(operator.spelling(), "+");
                assert_eq!(operator.fixity(), yu_hir::OperatorFixity::Infix);
                assert!(operator.range().start <= plus_start && plus_start < operator.range().end);
                assert_eq!(source.text[operator.range().clone()].trim(), "+");
                let provenance = operator.provenance();
                let yu_syntax::OperatorOrigin::Imported(slot) = provenance.declaration().origin() else {
                    panic!("pinned Display.say + must use the selected imported operator")
                };
                let dependency = parsed.selected_syntax_environment().dependency(slot)
                    .expect("selected dependency slot is owned by this parsed environment");
                let operator_module = sources.iter().find(|candidate| candidate.path == "lib/std/core/ops.yu")
                    .expect("pinned operator provider source");
                assert_eq!(dependency.module_label(), operator_module.path);
                assert_eq!(dependency.revision(), yu_syntax::SourceRevision::from_fingerprint(
                    pinned_stdlib::fingerprint(&operator_module.git_blob),
                ));
                let source_owners = yu_hir::SourceImportEnvironment::for_syntax_operators(
                    &parsed,
                    &identity,
                    &operator_source_indexes,
                )
                .expect("syntax-only source bridge retains exact selected operator providers");
                let operator_body = source_owners.operator_body_for_use(
                        &provenance,
                        provenance.declaration().range(),
                        operator.spelling(),
                        yu_syntax::OperatorFixity::Infix,
                    )
                    .expect("the imported use receipt joins to its one exact provider body");
                assert_eq!(operator_body, "\\x -> \\y -> x.add y");
                let operator_owner = source_owners.operator_owner_for_use(
                    &provenance,
                    provenance.declaration().range(),
                    operator.spelling(),
                    yu_syntax::OperatorFixity::Infix,
                ).expect("the exact imported operator source use has a source owner receipt");
                assert_eq!(operator_owner.module().file().key().normalized_workspace_relative_path(), operator_module.path);
                assert_eq!(operator_owner.revision(), dependency.revision());
                assert_eq!(operator_owner.declaration_range(), provenance.declaration().range());
                assert_eq!(operator_owner.spelling(), "+");
                assert_eq!(operator_owner.fixity(), yu_syntax::OperatorFixity::Infix);
                assert_eq!(operator_owner.visibility(), yu_syntax::Visibility::Public);
                assert!(!operator_owner.is_lazy());
                let declaration_site = provenance.declaration().range();
                let wrong_range = declaration_site.start + 1..declaration_site.end;
                assert_eq!(
                    source_owners.operator_body_for_use(
                        &provenance,
                        &wrong_range,
                        operator.spelling(),
                        yu_syntax::OperatorFixity::Infix,
                    ),
                    None,
                );
                assert!(source_owners.operator_owner_for_use(
                    &provenance, &wrong_range, operator.spelling(), yu_syntax::OperatorFixity::Infix,
                ).is_none());
                assert_eq!(
                    source_owners.operator_body_for_use(
                        &provenance,
                        provenance.declaration().range(),
                        "*",
                        yu_syntax::OperatorFixity::Infix,
                    ),
                    None,
                );
                assert!(source_owners.operator_owner_for_use(
                    &provenance, provenance.declaration().range(), "*", yu_syntax::OperatorFixity::Infix,
                ).is_none());
                assert_eq!(
                    source_owners.operator_body_for_use(
                        &provenance,
                        provenance.declaration().range(),
                        operator.spelling(),
                        yu_syntax::OperatorFixity::Prefix,
                    ),
                    None,
                );
                assert!(source_owners.operator_owner_for_use(
                    &provenance, provenance.declaration().range(), operator.spelling(), yu_syntax::OperatorFixity::Prefix,
                ).is_none());
                let mut wrong_revision_indexes = operator_source_indexes.clone();
                let ops_index = wrong_revision_indexes.iter_mut().find(|index|
                    index.module.file().key().normalized_workspace_relative_path() == operator_module.path
                ).unwrap();
                let wrong_revision = yu_syntax::SourceRevision::from_fingerprint(1);
                assert_ne!(wrong_revision, dependency.revision());
                ops_index.revision = wrong_revision;
                let wrong_revision_imports = yu_hir::SourceImportEnvironment::for_syntax_operators(
                    &parsed, &identity, &wrong_revision_indexes,
                ).unwrap();
                assert_eq!(
                    wrong_revision_imports.operator_body_for_use(
                        &provenance,
                        provenance.declaration().range(),
                        operator.spelling(),
                        yu_syntax::OperatorFixity::Infix,
                    ),
                    None,
                );
                assert!(wrong_revision_imports.operator_owner_for_use(
                    &provenance, provenance.declaration().range(), operator.spelling(), yu_syntax::OperatorFixity::Infix,
                ).is_none());
                let mut wrong_module_indexes = operator_source_indexes.clone();
                let ops_index = wrong_module_indexes.iter_mut().find(|index|
                    index.module.file().key().normalized_workspace_relative_path() == operator_module.path
                ).unwrap();
                ops_index.module = yu_hir::ModuleId::source_root(FileId::new(FileKey::new(
                    "yulang2-pinned-stdlib",
                    "lib/std/core/other_ops.yu",
                )));
                let wrong_module_imports = yu_hir::SourceImportEnvironment::for_syntax_operators(
                    &parsed, &identity, &wrong_module_indexes,
                ).unwrap();
                assert_eq!(
                    wrong_module_imports.operator_body_for_use(
                        &provenance,
                        provenance.declaration().range(),
                        operator.spelling(),
                        yu_syntax::OperatorFixity::Infix,
                    ),
                    None,
                );
                assert!(wrong_module_imports.operator_owner_for_use(
                    &provenance, provenance.declaration().range(), operator.spelling(), yu_syntax::OperatorFixity::Infix,
                ).is_none());
                let declaration = provenance.declaration().range();
                let declaration_text = operator_module.text.get(declaration.clone())
                    .expect("provider declaration range belongs to exact pinned source");
                assert!(declaration_text.starts_with("pub infix (+)"), "{declaration_text}");
                let provider_text: Arc<SourceText> = Arc::from(operator_module.text);
                let indexed_provider = operator_source_indexes.iter().find(|index|
                    index.module.file().key().normalized_workspace_relative_path() == operator_module.path
                        && index.revision == dependency.revision()
                ).expect("the exact selected provider export index is retained");
                let indexed_owner = indexed_provider.operator_owner_for_receipt(
                    &indexed_provider.module,
                    dependency.revision(),
                    provenance.declaration().range(),
                    operator.spelling(),
                    yu_syntax::OperatorFixity::Infix,
                ).expect("the provider index returns its parse-owned operator owner");
                assert_eq!(operator_owner, indexed_owner);
                assert!(!parsed.owns_source_key(operator_owner.declaration()));
                assert!(!parsed.owns_source_key(operator_owner.body()));
                assert_eq!(
                    operator_module.text.get(operator_owner.declaration_range().clone()),
                    Some("pub infix (+) 5.0.0 5.0.1 ="),
                );
                assert_eq!(
                    operator_module.text.get(operator_owner.body_range().clone()),
                    Some("\\x -> \\y -> x.add y"),
                );
                let provider_parsed = parse_file(
                    provider_text.clone(),
                    Arc::new(scan_header(provider_text)),
                    Arc::new(pinned_stdlib::syntax_environment_for_source(operator_module, &sources).unwrap()),
                );
                let provider_identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
                    "yulang2-pinned-stdlib",
                    operator_module.path,
                )));
                let provider_index = index_source_exports(provider_identity.clone(), &provider_parsed)
                    .unwrap()
                    .with_source_revision(dependency.revision());
                let provider_body = provider_index.operator_body_for_receipt(
                    provider_identity.module(),
                    dependency.revision(),
                    declaration,
                    "+",
                    yu_syntax::OperatorFixity::Infix,
                ).expect("imported receipt resolves to the exact pinned declaration body");
                assert_eq!(provider_body, "\\x -> \\y -> x.add y");
                assert!(operator_module.text.contains(provider_body));
            }
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
    fn pinned_core_id_imported_through_prelude_keeps_two_fresh_uses() {
        let sources = pinned_stdlib::resolve_implicit_stdlib().unwrap();
        let mut indexes = Vec::new();
        let mut core = None;
        for source in sources.iter() {
            let module = source.path.strip_prefix("lib/").unwrap().strip_suffix(".yu").unwrap().replace('/', "::");
            let environment = Arc::new(pinned_stdlib::syntax_environment_for_source(source, &sources).unwrap());
            let inventory = pinned_stdlib::parse_role_inventory(&module, environment).unwrap();
            indexes.push(index_source_exports(inventory.identity.clone(), &inventory.parsed).unwrap());
            if module == "std::core" {
                core = Some((inventory.identity, inventory.parsed));
            }
        }
        let (core_identity, core_parsed) = core.expect("pinned std::core provider is present");
        let exported_id = resolve_public_export(&indexes, "std::prelude", "id").unwrap();
        assert_eq!(exported_id.module.as_ref(), "std::core");
        assert_eq!(exported_id.declaration.text.trim(), "pub id x = x");
        let selected = [exported_id.declaration.source.clone()].into_iter().collect::<std::collections::HashSet<_>>();
        let imports = SemanticImports::with_selected_source_imports(&core_parsed, &core_identity, &indexes, &selected).unwrap();
        let provider = Arc::new(lower_module_with_selected_local_source(
            core_identity,
            &core_parsed,
            imports,
            selected,
        ).unwrap());
        assert_eq!(provider.items().len(), 1);

        let text: Arc<SourceText> = Arc::from("my first = id 42\nmy second = id \"Yulang\"");
        let parsed = parse_file(text.clone(), Arc::new(scan_header(text)), Arc::new(playground_syntax_environment().unwrap()));
        let consumer_identity = ModuleIdentity::source_root(FileId::new(FileKey::new("pinned-prelude-id", "consumer.yu")));
        let imports = SemanticImports::with_implicit_prelude(&parsed, &consumer_identity, &indexes).unwrap();
        let consumer = Arc::new(lower_module_with_local_source(consumer_identity, &parsed, imports).unwrap());
        let candidate = CandidateInference::solve_modules(vec![consumer.clone(), provider.clone()]).unwrap();
        assert!(candidate.observes_hir(&consumer));
        assert!(candidate.observes_hir(&provider));
        assert!(candidate.candidate_conflicts().is_empty(), "the pinned polymorphic id accepts both source uses");

        let mut use_occurrences = Vec::new();
        for (name, leaf) in [("first", yu_solver::shadow_apply::CandidateGraphLeaf::IntPositive), ("second", yu_solver::shadow_apply::CandidateGraphLeaf::StrPositive)] {
            let root = consumer.items().iter().find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding.definition_root().clone()),
                _ => None,
            }).expect("consumer binding");
            let graph = candidate.export(&root).unwrap();
            assert!(graph.bounds().any(|bound| bound.lower().leaf() == Some(leaf) || bound.upper().leaf() == Some(leaf)));
            let local = consumer.local_source(&root).unwrap().unwrap();
            let use_occurrence = local.expressions().iter().find_map(|expression| matches!(
                &expression.form,
                LocalSourceForm::Name { spelling, resolution: yu_hir::shadow::LocalSourceResolution::Imported(id) }
                    if spelling.as_ref() == "id" && id == &exported_id.identity()
            ).then(|| expression.occurrence.clone())).expect("id use keeps the exact prelude export identity");
            use_occurrences.push(use_occurrence);
        }
        assert_eq!(use_occurrences.len(), 2);
        let fresh_rows = use_occurrences.iter().map(|occurrence| {
            candidate.fresh_use(occurrence).expect("pinned provider use retains FreshUse").rows().filter(|row| row.source_row().is_local()).collect::<Vec<_>>()
        }).collect::<Vec<_>>();
        assert!(fresh_rows.iter().all(|rows| !rows.is_empty()));
        assert!(fresh_rows[0].iter().all(|first| fresh_rows[1].iter().all(|second| !first.same_identity(second))));
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
