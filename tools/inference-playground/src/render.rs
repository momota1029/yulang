//! Finite observations of the existing private candidate graph.
use std::fmt::Write;
use yu_hir::{HirItem, HirModule};
use yu_solver::shadow_apply::{CandidateGraphExport, CandidateGraphNode, CandidateGraphRow};
use yu_solver::shadow_apply::{CandidateInference, CandidateSourceValueIdentity};

use crate::output::{Output, cap};

pub const OUTPUT_CAP: usize = 4096;

fn intern<'a>(
    nodes: &mut Vec<CandidateGraphNode<'a>>,
    node: CandidateGraphNode<'a>,
    output: &mut Output,
) -> Result<usize, String> {
    output.observe(1)?;
    if let Some(index) = nodes.iter().position(|prior| prior.same_identity(node)) {
        return Ok(index);
    }
    if nodes.len() == OUTPUT_CAP {
        return Err(format!(
            "tool output cap exceeded: more than {OUTPUT_CAP} observed nodes"
        ));
    }
    nodes.push(node);
    Ok(nodes.len() - 1)
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
    let root = intern(&mut nodes, graph.root(), output)?;
    let mut rows: Vec<CandidateGraphRow<'_>> = Vec::new();
    for row in graph.rows() {
        output.observe(1)?;
        if !rows.iter().any(|prior| prior.same_identity(row)) {
            if rows.len() == OUTPUT_CAP {
                return Err(format!(
                    "tool output cap exceeded: more than {OUTPUT_CAP} rows"
                ));
            }
            rows.push(row);
        }
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
            intern(&mut nodes, bound.lower(), output)?,
            intern(&mut nodes, bound.upper(), output)?,
        ));
    }
    let mut cursor = 0;
    while cursor < nodes.len() {
        output.observe(1)?;
        if let Some(children) = nodes[cursor].children() {
            for child in children {
                intern(&mut nodes, child, output)?;
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
            let row_index = rows
                .iter()
                .position(|prior| prior.same_identity(row))
                .ok_or_else(|| {
                    "candidate graph observation unavailable: missing row identity".to_owned()
                })?;
            write!(output, "row r{row_index}").map_err(cap)?;
        } else if let Some(children) = node.children() {
            output.observe(children.len())?;
            let ids = children.map(|child| {
                nodes
                    .iter()
                    .position(|prior| prior.same_identity(child))
                    .unwrap()
            });
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
    for event in observation.events() {
        output.observe(1)?;
        let occurrence = event.checking.occurrence();
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
            crate::location_into(source, &range, output)?;
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
                let HirItem::Binding(binding) = item else {
                    return None;
                };
                let local = hir.local_source(binding.definition_root()).ok().flatten()?;
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
