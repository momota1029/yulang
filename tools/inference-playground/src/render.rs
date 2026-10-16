//! Finite observations of the existing private candidate graph.
use std::collections::HashMap;
use std::fmt::Write;
use yu_hir::{HirItem, HirModule, LocalSource, SourceRootId};
use yu_solver::shadow_apply::{CandidateGraphExport, CandidateGraphNode, CandidateGraphRow};
use yu_solver::shadow_apply::{CandidateInference, CandidateSourceValueIdentity};

use crate::output::{Output, cap};

pub const OUTPUT_CAP: usize = 4096;

fn local_source_for_item<'hir>(hir: &'hir HirModule, item: &HirItem) -> Option<&'hir LocalSource> {
    let root = match item {
        HirItem::Binding(binding) => {
            SourceRootId::Definition(binding.definition_root().clone())
        }
        HirItem::Expression(expression) => SourceRootId::Expression(
            hir.expression_root(expression.occurrence()).ok().flatten()?.clone(),
        ),
        HirItem::Error { .. } => return None,
    };
    hir.local_source_for(&root).ok().flatten()
}

fn intern<'a>(
    nodes: &mut Vec<CandidateGraphNode<'a>>,
    node_indices: &mut HashMap<CandidateGraphNode<'a>, usize>,
    node: CandidateGraphNode<'a>,
    output: &mut Output,
) -> Result<usize, String> {
    output.observe(1)?;
    if let Some(index) = node_indices.get(&node) {
        return Ok(*index);
    }
    if nodes.len() == OUTPUT_CAP {
        return Err(format!(
            "tool output cap exceeded: more than {OUTPUT_CAP} observed nodes"
        ));
    }
    let index = nodes.len();
    nodes.push(node);
    node_indices.insert(node, index);
    Ok(index)
}

pub fn graph(graph: &CandidateGraphExport<'_>) -> Result<String, String> {
    let mut output = Output::new();
    graph_into(graph, &mut output)?;
    output.finish()
}

pub(crate) fn graph_into(
    graph: &CandidateGraphExport<'_>,
    output: &mut Output,
) -> Result<(), String> {
    let mut nodes = Vec::new();
    let mut node_indices = HashMap::new();
    let root = intern(&mut nodes, &mut node_indices, graph.root(), output)?;
    let mut rows: Vec<CandidateGraphRow<'_>> = Vec::new();
    let mut row_indices = HashMap::new();
    for row in graph.rows() {
        output.observe(1)?;
        if row_indices.contains_key(&row) {
            continue;
        }
        if rows.len() == OUTPUT_CAP {
            return Err(format!(
                "tool output cap exceeded: more than {OUTPUT_CAP} rows"
            ));
        }
        let index = rows.len();
        rows.push(row);
        row_indices.insert(row, index);
    }
    let mut bounds = Vec::new();
    for bound in graph.bounds() {
        output.observe(1)?;
        if bounds.len() == OUTPUT_CAP {
            return Err(format!(
                "tool output cap exceeded: more than {OUTPUT_CAP} bounds"
            ));
        }
        bounds.push((
            bound.kind(),
            intern(&mut nodes, &mut node_indices, bound.lower(), output)?,
            intern(&mut nodes, &mut node_indices, bound.upper(), output)?,
        ));
    }
    let mut cursor = 0;
    while cursor < nodes.len() {
        output.observe(1)?;
        if let Some(children) = nodes[cursor].children() {
            for child in children {
                intern(&mut nodes, &mut node_indices, child, output)?;
            }
        }
        cursor += 1;
    }
    write!(
        output,
        "  root = n{root}\n  observed nodes (finite references):\n"
    )
    .map_err(cap)?;
    for (index, node) in nodes.iter().copied().enumerate() {
        output.observe(1)?;
        write!(output, "    n{index} [{:?}] = ", node.polarity()).map_err(cap)?;
        if let Some(leaf) = node.leaf() {
            write!(output, "{leaf:?}").map_err(cap)?;
        } else if let Some(row) = node.row() {
            let row_index = row_indices
                .get(&row)
                .copied()
                .ok_or_else(|| {
                    "candidate graph observation unavailable: missing row identity".to_owned()
                })?;
            write!(output, "row r{row_index}").map_err(cap)?;
        } else if let Some(children) = node.children() {
            output.observe(children.len())?;
            let ids = children.map(|child| node_indices.get(&child).copied().unwrap());
            write!(
                output,
                "Function(argument=n{}, argument-effect=n{}, result-effect=n{}, result=n{})",
                ids[0], ids[1], ids[2], ids[3]
            )
            .map_err(cap)?;
        } else {
            output
                .write_str("opaque effect operand (contents unavailable)")
                .map_err(cap)?;
        }
        output.write_char('\n').map_err(cap)?;
    }
    output
        .write_str("  rows (names preserve actual identity):\n")
        .map_err(cap)?;
    for (index, row) in rows.iter().enumerate() {
        writeln!(
            output,
            "    r{index}: {:?}, local={}",
            row.kind(),
            row.is_local()
        )
        .map_err(cap)?;
    }
    output.write_str("  retained constraints:\n").map_err(cap)?;
    for (kind, lower, upper) in bounds {
        writeln!(output, "    n{lower} <: n{upper} [{kind:?}]").map_err(cap)?;
    }
    Ok(())
}

pub fn intrusion(
    candidate: &CandidateInference,
    hir: &HirModule,
    source: &str,
) -> Result<String, String> {
    let mut output = Output::new();
    intrusion_into(candidate, hir, source, &mut output)?;
    output.finish()
}

pub(crate) fn intrusion_into(
    candidate: &CandidateInference,
    hir: &HirModule,
    source: &str,
    output: &mut Output,
) -> Result<(), String> {
    output.write_str("\nStatic computation root source plans (retained entry; no runtime receiver, grant or handling evidence):\n").map_err(cap)?;
    for index in 0..candidate.computation_source_plan_count() {
        output.observe(1)?;
        let Some(plan) = candidate.computation_source_plan(index)
            .map_err(|_| "candidate computation source observation unavailable".to_owned())? else { continue; };
        write!(output, "  static computation root {index}: owner={:?}, lambda={:?}, formal={:?}, annotation={:?}, outer-row={:?}, parameter={:?}, retained-entry-row={}, concrete=[",
            plan.original_owner(), plan.original_lambda(), plan.original_formal(),
            plan.annotation().position, plan.outer_row().position,
            plan.native_parameter_root(), plan.entry_effect_row()).map_err(cap)?;
        for (member, effect) in plan.concrete_members().iter().enumerate() {
            output.observe(1)?;
            if member != 0 { output.write_str(", ").map_err(cap)?; }
            write!(output, "{effect:?}").map_err(cap)?;
        }
        output.write_str("]").map_err(cap)?;
        if let Some(variable) = plan.symbolic_row_variable() {
            output.observe(1)?;
            write!(output, ", symbolic={variable}").map_err(cap)?;
        }
        output.write_char('\n').map_err(cap)?;
    }
    output.write_str("\nDirectional introductions (symbolic candidate evidence; not event consumption or runtime hygiene):\n").map_err(cap)?;
    for index in 0..candidate.source_call_count() {
        output.observe(1)?;
        let call = candidate.source_call(index)
            .map_err(|_| "candidate directional observation unavailable".to_owned())?;
        if let Some(introduction) = call.directional_introduction() {
            write!(output, "  introduction {index}: owner={:?}, lambda={:?}, formal={:?}, scope={:?}, use={:?}, cause={:?}, demand={:?}, ResultEffect={:?}, raw Effect row={} at ",
                introduction.original_owner(), introduction.original_lambda(), introduction.original_formal(),
                introduction.original_scope(), introduction.checking_occurrence(), introduction.checking_cause(),
                introduction.original_demand(), introduction.result_effect(), introduction.raw_invocation_row()).map_err(cap)?;
            crate::location_into(source, &call.source().range, output)?;
            output.write_char('\n').map_err(cap)?;
        } else {
            writeln!(output, "  call {index}: no authenticated omitted-formal introduction; other routes are unsupported evidence, not a language-wide absence claim").map_err(cap)?;
        }
    }
    let observation = candidate
        .intrusion_observation()
        .map_err(|_| "candidate intrusion observation unavailable".to_owned())?;
    write!(
        output,
        "\nRetained intrusion state (not a chronological trace):\n  pending consumed={} total={}\n",
        observation.pending_consumed(),
        observation.pending_total()
    )
    .map_err(cap)?;
    let mut conflict_ranges = None;
    for event in observation.events() {
        output.observe(1)?;
        let occurrence = event.checking.occurrence();
        let conflict_ranges = conflict_ranges.get_or_insert_with(|| {
            crate::conflict_ranges_for(
                hir,
                observation
                    .events()
                    .take(crate::output::WORK_CAP)
                    .map(|event| event.checking.occurrence()),
            )
        });
        let range = conflict_ranges.get(occurrence).copied().flatten();
        write!(
            output,
            "  event {}: origin=v{} (",
            event.ordinal, event.origin.ordinal
        )
        .map_err(cap)?;
        source_value_into(hir, event.origin.identity, output)?;
        write!(
            output,
            ", SCC {}), receiver=v{} (",
            event.origin.component, event.receiver.ordinal
        )
        .map_err(cap)?;
        source_value_into(hir, event.receiver.identity, output)?;
        write!(
            output,
            ", SCC {}), same_scc={} at retained call-tail occurrence ",
            event.receiver.component, event.same_scc
        )
        .map_err(cap)?;
        if let Some(range) = range {
            crate::location_into(source, range, output)?;
        } else {
            output.write_str("source span unavailable").map_err(cap)?;
        }
        output.write_char('\n').map_err(cap)?;
    }
    for pair in observation.parents() {
        output.observe(1)?;
        write!(output, "  pair {}: {:?} parent=raw{}(rep=raw{}) copy=raw{}(rep=raw{}), {:?}, target_level={}, occurrence={}, source_set={:?}, events=", pair.ordinal, pair.parent.kind, pair.parent.ordinal, pair.parent.representative, pair.copy.ordinal, pair.copy.representative, pair.polarity, pair.target, pair.occurrence, pair.source_set).map_err(cap)?;
        source_events_into(pair.source_events, output)?;
    }
    for group in observation.groups() {
        output.observe(1)?;
        writeln!(
            output,
            "  group {}: occurrence={}, pair_range={}..{}, activated={}",
            group.ordinal, group.occurrence, group.start, group.end, group.activated
        )
        .map_err(cap)?;
    }
    for reuse in observation.reuses() {
        output.observe(1)?;
        write!(
            output,
            "  reuse {}: group={}, occurrence={}, source_set={}, events=",
            reuse.ordinal, reuse.group, reuse.occurrence, reuse.source_set
        )
        .map_err(cap)?;
        source_events_into(reuse.source_events, output)?;
    }
    Ok(())
}

fn source_value_into(
    hir: &HirModule,
    identity: CandidateSourceValueIdentity<'_>,
    output: &mut Output,
) -> Result<(), String> {
    match identity {
        CandidateSourceValueIdentity::Module(id) => {
            let name = hir.items().iter().find_map(|item| match item {
                HirItem::Binding(binding) if binding.id() == id => Some(binding.name().spelling()),
                _ => None,
            });
            if let Some(name) = name {
                write!(output, "module {name}").map_err(cap)
            } else {
                output.write_str("module value").map_err(cap)
            }
        }
        CandidateSourceValueIdentity::Local(id) => {
            let name = hir.items().iter().find_map(|item| {
                let local = local_source_for_item(hir, item)?;
                local
                    .bindings()
                    .iter()
                    .find(|binding| &binding.id == id)
                    .map(|binding| &*binding.spelling)
            });
            if let Some(name) = name {
                write!(output, "local {name}").map_err(cap)
            } else {
                output.write_str("local value").map_err(cap)
            }
        }
        CandidateSourceValueIdentity::CatchBinder(_) => {
            output.write_str("catch binder value").map_err(cap)
        }
        CandidateSourceValueIdentity::Parameter(_) => {
            output.write_str("parameter value").map_err(cap)
        }
        CandidateSourceValueIdentity::Expression(_) => {
            output.write_str("expression value").map_err(cap)
        }
    }
}

fn source_events_into(events: &[usize], output: &mut Output) -> Result<(), String> {
    output.observe(events.len())?;
    output.write_char('[').map_err(cap)?;
    for (index, event) in events.iter().enumerate() {
        if index != 0 {
            output.write_str(", ").map_err(cap)?;
        }
        write!(output, "{event}").map_err(cap)?;
    }
    output.write_str("]\n").map_err(cap)
}
