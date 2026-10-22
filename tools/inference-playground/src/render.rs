//! Finite observations of the existing private candidate graph.
use std::collections::HashMap;
use std::fmt::Write;
use yu_hir::{DefId, HirItem, HirLocalId, HirModule, LocalSource, SourceRootId};
use yu_solver::shadow_apply::{
    CandidateGraphEffectOperand, CandidateGraphExport, CandidateGraphFormalPortStep,
    CandidateGraphNode, CandidateGraphRow,
};
use yu_solver::shadow_apply::{CandidateInference, CandidateSourceValueIdentity};

use crate::output::{Output, cap};

pub const OUTPUT_CAP: usize = 4096;

#[derive(Clone, Copy)]
enum SchemeRowKind { Value, Effect }

struct SchemeBinder {
    name: String,
    kind: SchemeRowKind,
}

enum SchemeType {
    Leaf(&'static str),
    Row { name: String, kind: SchemeRowKind },
    Function {
        argument: Box<SchemeType>,
        argument_effect: Box<SchemeType>,
        result_effect: Box<SchemeType>,
        result: Box<SchemeType>,
    },
    Tuple(Vec<SchemeType>),
}

/// Typed, provisional projection of one drained candidate root. The retained
/// graph constraints and source effect evidence remain attached as text until
/// a source-adequate accepted scheme carrier is proved.
struct CandidatePublicScheme {
    name: String,
    binders: Vec<SchemeBinder>,
    anchors: Vec<SchemeBinder>,
    ty: SchemeType,
    observations: String,
}

impl SchemeType {
    fn render(&self, output: &mut Output) -> Result<(), String> {
        match self {
            Self::Leaf(name) => output.write_str(name).map_err(cap),
            Self::Row { name, kind } => {
                let prefix = match kind { SchemeRowKind::Value => "α", SchemeRowKind::Effect => "ε" };
                if !name.starts_with(prefix) {
                    return Err("candidate scheme row name disagrees with its kind".to_owned());
                }
                output.write_str(name).map_err(cap)
            }
            Self::Function { argument, argument_effect, result_effect, result } => {
                output.write_str("Function(argument=").map_err(cap)?;
                argument.render(output)?;
                output.write_str(", argument-effect=").map_err(cap)?;
                argument_effect.render(output)?;
                output.write_str(", result-effect=").map_err(cap)?;
                result_effect.render(output)?;
                output.write_str(", result=").map_err(cap)?;
                result.render(output)?;
                output.write_char(')').map_err(cap)
            }
            Self::Tuple(items) => {
                output.write_char('(').map_err(cap)?;
                for (index, item) in items.iter().enumerate() {
                    if index != 0 { output.write_str(", ").map_err(cap)?; }
                    item.render(output)?;
                }
                output.write_char(')').map_err(cap)
            }
        }
    }
}

impl CandidatePublicScheme {
    fn render(self) -> Result<String, String> {
        let mut output = Output::new();
        write!(output, "{}: ", self.name).map_err(cap)?;
        if let Some((first, rest)) = self.binders.split_first() {
            output.write_str("∀ ").map_err(cap)?;
            output.write_str(&first.name).map_err(cap)?;
            for binder in rest {
                output.write_char(' ').map_err(cap)?;
                output.write_str(&binder.name).map_err(cap)?;
            }
            output.write_str(". ").map_err(cap)?;
        }
        self.ty.render(&mut output)?;
        output.write_char('\n').map_err(cap)?;
        for anchor in self.anchors {
            let kind = match anchor.kind { SchemeRowKind::Value => "Value", SchemeRowKind::Effect => "Effect" };
            writeln!(output, "  shared {kind} anchor {} (bounds owned by outer context)", anchor.name).map_err(cap)?;
        }
        output.write_str(&self.observations).map_err(cap)?;
        output.finish()
    }
}

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

/// Render a bounded type-facing view from the same candidate graph used by
/// inference. Value constructors are summarized structurally; all quantified
/// Value/Effect rows, bounds, explicit effect labels, and source permissions
/// remain visible so this view never closes an effect tail by pretty-printing.
pub fn public_scheme(graph: &CandidateGraphExport<'_>, name: &str) -> Result<String, String> {
    let mut rows = Vec::new();
    for (index, row) in graph.rows().enumerate() {
        if rows.len() == OUTPUT_CAP {
            return Err(format!("tool output cap exceeded: more than {OUTPUT_CAP} quantified rows"));
        }
        let prefix = match row.kind() {
            _ if row.is_effect() => "ε",
            _ => "α",
        };
        rows.push((row, format!("{prefix}{index}")));
    }
    let mut free_rows = std::collections::HashSet::new();
    let mut active_rows = std::collections::HashSet::new();
    let ty = project_type_node(graph, graph.root(), &rows, &mut active_rows, &mut free_rows)?;
    let mut details = Output::new();
    for permission in graph.formal_effect_permissions()
        .map_err(|_| "candidate scheme permission projection unavailable".to_owned())?
    {
        details.observe(1)?;
        details.write_str("  open formal effect permission ").map_err(cap)?;
        match permission.path().first() {
            Some(CandidateGraphFormalPortStep::Argument) => details.write_str("argument").map_err(cap)?,
            Some(CandidateGraphFormalPortStep::Result) => details.write_str("result").map_err(cap)?,
            None => return Err("candidate scheme permission path is empty".to_owned()),
        }
        for step in &permission.path()[1..] {
            details.write_char('/').map_err(cap)?;
            match step {
                CandidateGraphFormalPortStep::Argument => details.write_str("argument").map_err(cap)?,
                CandidateGraphFormalPortStep::Result => details.write_str("result").map_err(cap)?,
            }
        }
        details.write_str(" permits [").map_err(cap)?;
        for (index, effect) in permission.permitted().iter().enumerate() {
            details.observe(1)?;
            if index != 0 { details.write_str(", ").map_err(cap)?; }
            write!(details, "{effect:?}").map_err(cap)?;
        }
        let tail = permission.open_tail().row().ok_or_else(||
            "candidate scheme permission tail is not an effect row".to_owned())?;
        free_rows.insert(tail);
        write!(details, ", {}] (open)\n", row_name(&rows, tail)?).map_err(cap)?;
    }
    for node in graph.nodes() {
        let Some(operand) = node.effect_operand() else { continue; };
        details.observe(1)?;
        match operand {
            CandidateGraphEffectOperand::Contribution { effect, route, instance } => {
                writeln!(details, "  effect label {effect:?} from {route:?} instance {instance}").map_err(cap)?;
            }
            CandidateGraphEffectOperand::AnnotationMember { effect, position, permitted, tail, .. } => {
                write!(details, "  effect label {effect:?} at annotation {position:?} permits [").map_err(cap)?;
                render_permitted(&mut details, permitted)?;
                render_effect_tail(&mut details, &rows, &mut free_rows, tail)?;
            }
            CandidateGraphEffectOperand::OperationInterfaceMember { effect, occurrence, permitted, tail, .. } => {
                write!(details, "  effect label {effect:?} at operation use {occurrence:?} permits [").map_err(cap)?;
                render_permitted(&mut details, permitted)?;
                render_effect_tail(&mut details, &rows, &mut free_rows, tail)?;
            }
            CandidateGraphEffectOperand::PermissionView { permitted, tail, position, .. }
            | CandidateGraphEffectOperand::SupportView { permitted, tail, position, .. } => {
                write!(details, "  effect view at {position:?} permits [").map_err(cap)?;
                render_permitted(&mut details, permitted)?;
                render_effect_tail(&mut details, &rows, &mut free_rows, tail)?;
            }
        }
    }
    for bound in graph.bounds() {
        details.observe(1)?;
        write!(details, "  retained {:?} bound ", bound.kind()).map_err(cap)?;
        render_constraint_node(graph, bound.lower(), &rows, &mut free_rows, &mut details)?;
        details.write_str(" ⊆ ").map_err(cap)?;
        render_constraint_node(graph, bound.upper(), &rows, &mut free_rows, &mut details)?;
        details.write_char('\n').map_err(cap)?;
    }
    let observations = details.finish()?;
    let binders = rows.iter()
        .filter(|(row, _)| row.is_local() && free_rows.contains(row))
        .map(|(row, name)| SchemeBinder {
            name: name.clone(),
            kind: if row.is_effect() { SchemeRowKind::Effect } else { SchemeRowKind::Value },
        })
        .collect();
    let anchors: Vec<_> = rows.iter()
        .filter(|(row, _)| !row.is_local() && free_rows.contains(row))
        .map(|(row, name)| SchemeBinder {
            name: name.clone(),
            kind: if row.is_effect() { SchemeRowKind::Effect } else { SchemeRowKind::Value },
        })
        .collect();
    CandidatePublicScheme {
        name: name.to_owned(), binders, anchors, ty, observations,
    }.render()
}

fn render_permitted(output: &mut Output, permitted: &[yu_hir::shadow::SourceEffectId]) -> Result<(), String> {
    for (index, effect) in permitted.iter().enumerate() {
        output.observe(1)?;
        if index != 0 { output.write_str(", ").map_err(cap)?; }
        write!(output, "{effect:?}").map_err(cap)?;
    }
    Ok(())
}

fn render_effect_tail<'a>(
    output: &mut Output,
    rows: &[(CandidateGraphRow<'a>, String)],
    free_rows: &mut std::collections::HashSet<CandidateGraphRow<'a>>,
    tail: Option<CandidateGraphNode<'a>>,
) -> Result<(), String> {
    if let Some(tail) = tail {
        let row = tail.row().ok_or_else(|| "effect view tail is not a row".to_owned())?;
        free_rows.insert(row);
        writeln!(output, ", {}] (open)", row_name(rows, row)?).map_err(cap)?;
    } else {
        output.write_str("] (closed view)\n").map_err(cap)?;
    }
    Ok(())
}

fn render_effect_operand<'a>(
    output: &mut Output,
    rows: &[(CandidateGraphRow<'a>, String)],
    free_rows: &mut std::collections::HashSet<CandidateGraphRow<'a>>,
    operand: CandidateGraphEffectOperand<'a>,
) -> Result<(), String> {
    match operand {
        CandidateGraphEffectOperand::Contribution { effect, route, instance } => {
            write!(output, "effect({effect:?}, route={route:?}, instance={instance})").map_err(cap)
        }
        CandidateGraphEffectOperand::AnnotationMember {
            position, member, effect, permitted, tail, ..
        } => {
            write!(output, "annotation-effect({effect:?}, position={position:?}, member={member}, permits=[")
                .map_err(cap)?;
            render_permitted(output, permitted)?;
            output.write_str("], ").map_err(cap)?;
            render_operand_tail(output, rows, free_rows, tail)
        }
        CandidateGraphEffectOperand::OperationInterfaceMember {
            occurrence, member, effect, permitted, tail, ..
        } => {
            write!(output, "operation-effect({effect:?}, occurrence={occurrence:?}, member={member}, permits=[")
                .map_err(cap)?;
            render_permitted(output, permitted)?;
            output.write_str("], ").map_err(cap)?;
            render_operand_tail(output, rows, free_rows, tail)
        }
        CandidateGraphEffectOperand::PermissionView { position, permitted, tail, .. } => {
            write!(output, "permission-view(position={position:?}, permits=[").map_err(cap)?;
            render_permitted(output, permitted)?;
            output.write_str("], ").map_err(cap)?;
            render_operand_tail(output, rows, free_rows, tail)
        }
        CandidateGraphEffectOperand::SupportView { position, permitted, tail, .. } => {
            write!(output, "support-view(position={position:?}, permits=[").map_err(cap)?;
            render_permitted(output, permitted)?;
            output.write_str("], ").map_err(cap)?;
            render_operand_tail(output, rows, free_rows, tail)
        }
    }
}

fn render_operand_tail<'a>(
    output: &mut Output,
    rows: &[(CandidateGraphRow<'a>, String)],
    free_rows: &mut std::collections::HashSet<CandidateGraphRow<'a>>,
    tail: Option<CandidateGraphNode<'a>>,
) -> Result<(), String> {
    if let Some(tail) = tail {
        let row = tail.row().ok_or_else(|| "effect operand tail is not an effect row".to_owned())?;
        if !row.is_effect() {
            return Err("effect operand tail has Value row kind".to_owned());
        }
        free_rows.insert(row);
        write!(output, "open-tail={}", row_name(rows, row)?).map_err(cap)
    } else {
        output.write_str("closed-view").map_err(cap)
    }
}

fn render_constraint_node<'a>(
    graph: &CandidateGraphExport<'a>,
    node: CandidateGraphNode<'a>,
    rows: &[(CandidateGraphRow<'a>, String)],
    free_rows: &mut std::collections::HashSet<CandidateGraphRow<'a>>,
    output: &mut Output,
) -> Result<(), String> {
    if let Some(row) = node.row() {
        if row.is_effect() {
            free_rows.insert(row);
            output.write_str(row_name(rows, row)?).map_err(cap)?;
        } else {
            let index = rows.iter().position(|(candidate, _)| *candidate == row)
                .ok_or_else(|| "candidate scheme row identity unavailable".to_owned())?;
            let mut concrete_head = None;
            for bound in graph.bounds().filter(|bound|
                bound.is_effect() == row.is_effect()
                    && bound.upper().row().is_some_and(|upper| upper == row)
                    && bound.lower().row().is_none()
            ) {
                if concrete_head.is_some_and(|first: CandidateGraphNode<'a>| !first.same_identity(bound.lower())) {
                    return Err("candidate scheme has multiple concrete Value shapes for one row".to_owned());
                }
                concrete_head = Some(bound.lower());
            }
            if concrete_head.is_none() {
                free_rows.insert(row);
                output.write_str(row_name(rows, row)?).map_err(cap)?;
            } else {
                write!(output, "r{index}").map_err(cap)?;
            }
        }
    } else if let Some(children) = node.children() {
        output.write_str("Function(").map_err(cap)?;
        for (index, (label, child)) in ["argument=", "argument-effect=", "result-effect=", "result="]
            .into_iter().zip(children).enumerate()
        {
            if index != 0 { output.write_str(", ").map_err(cap)?; }
            output.write_str(label).map_err(cap)?;
            render_constraint_node(graph, child, rows, free_rows, output)?;
        }
        output.write_char(')').map_err(cap)?;
    } else if let Some(children) = node.tuple_children() {
        output.write_char('(').map_err(cap)?;
        for (index, child) in children.enumerate() {
            if index != 0 { output.write_str(", ").map_err(cap)?; }
            render_constraint_node(graph, child, rows, free_rows, output)?;
        }
        output.write_char(')').map_err(cap)?;
    } else if let Some(leaf) = node.leaf() {
        write!(output, "{leaf:?}").map_err(cap)?;
    } else if let Some(operand) = node.effect_operand() {
        render_effect_operand(output, rows, free_rows, operand)?;
    } else {
        return Err("candidate scheme contains an unsupported bound operand".to_owned());
    }
    Ok(())
}

fn row_name<'a>(rows: &'a [(CandidateGraphRow<'_>, String)], row: CandidateGraphRow<'_>) -> Result<&'a str, String> {
    rows.iter().find(|(candidate, _)| *candidate == row).map(|(_, name)| name.as_str())
        .ok_or_else(|| "candidate scheme row identity unavailable".to_owned())
}

fn project_type_node<'a>(
    graph: &CandidateGraphExport<'a>,
    node: CandidateGraphNode<'a>,
    rows: &[(CandidateGraphRow<'a>, String)],
    active_rows: &mut std::collections::HashSet<CandidateGraphRow<'a>>,
    free_rows: &mut std::collections::HashSet<CandidateGraphRow<'a>>,
) -> Result<SchemeType, String> {
    if let Some(leaf) = node.leaf() {
        let name = match leaf {
            yu_solver::shadow_apply::CandidateGraphLeaf::IntPositive
            | yu_solver::shadow_apply::CandidateGraphLeaf::IntNegative => "int",
            yu_solver::shadow_apply::CandidateGraphLeaf::UnitPositive
            | yu_solver::shadow_apply::CandidateGraphLeaf::UnitNegative => "unit",
            yu_solver::shadow_apply::CandidateGraphLeaf::BoolPositive
            | yu_solver::shadow_apply::CandidateGraphLeaf::BoolNegative => "bool",
            yu_solver::shadow_apply::CandidateGraphLeaf::StrPositive
            | yu_solver::shadow_apply::CandidateGraphLeaf::StrNegative => "str",
            yu_solver::shadow_apply::CandidateGraphLeaf::Bottom
            | yu_solver::shadow_apply::CandidateGraphLeaf::NegativeBottom => "⊥",
            yu_solver::shadow_apply::CandidateGraphLeaf::Top => "⊤",
            yu_solver::shadow_apply::CandidateGraphLeaf::EffectBottom => "∅+",
            yu_solver::shadow_apply::CandidateGraphLeaf::EmptyEffect => "∅−",
        };
        return Ok(SchemeType::Leaf(name));
    }
    if let Some(row) = node.row() {
        if row.is_effect() {
            free_rows.insert(row);
            return Ok(SchemeType::Row { name: row_name(rows, row)?.to_owned(), kind: SchemeRowKind::Effect });
        }
        if !active_rows.insert(row) {
            free_rows.insert(row);
            return Ok(SchemeType::Row { name: row_name(rows, row)?.to_owned(), kind: SchemeRowKind::Value });
        }
        let mut heads = graph.bounds().filter(|bound|
            bound.is_effect() == row.is_effect() && bound.upper().row().is_some_and(|upper| upper == row)
                && bound.lower().row().is_none()
        );
        let Some(head) = heads.next() else {
            free_rows.insert(row);
            active_rows.remove(&row);
            return Ok(SchemeType::Row { name: row_name(rows, row)?.to_owned(), kind: SchemeRowKind::Value });
        };
        let first = head.lower();
        let ambiguous = heads.any(|bound| !bound.lower().same_identity(first));
        if ambiguous {
            return Err("candidate scheme has multiple concrete Value shapes for one row".to_owned());
        }
        let projected = project_type_node(graph, first, rows, active_rows, free_rows)?;
        active_rows.remove(&row);
        return Ok(projected);
    }
    if let Some(children) = node.children() {
        let [argument, argument_effect, result_effect, result] = children;
        let argument = project_type_node(graph, argument, rows, active_rows, free_rows)?;
        let argument_effect = project_type_node(graph, argument_effect, rows, active_rows, free_rows)?;
        let result_effect = project_type_node(graph, result_effect, rows, active_rows, free_rows)?;
        let result = project_type_node(graph, result, rows, active_rows, free_rows)?;
        return Ok(SchemeType::Function {
            argument: Box::new(argument),
            argument_effect: Box::new(argument_effect),
            result_effect: Box::new(result_effect),
            result: Box::new(result),
        });
    }
    if let Some(children) = node.tuple_children() {
        let mut projected = Vec::new();
        for child in children {
            if projected.len() == OUTPUT_CAP {
                return Err(format!("tool output cap exceeded: more than {OUTPUT_CAP} tuple elements"));
            }
            projected.push(project_type_node(graph, child, rows, active_rows, free_rows)?);
        }
        return Ok(SchemeType::Tuple(projected));
    }
    Err("candidate scheme contains an unsupported type node".to_owned())
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
        if let Some(children) = nodes[cursor].tuple_children() {
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
        } else if let Some(children) = node.tuple_children() {
            output.observe(children.len())?;
            output.write_str("Tuple([").map_err(cap)?;
            for (child_index, child) in children.enumerate() {
                if child_index != 0 {
                    output.write_str(", ").map_err(cap)?;
                }
                let child = node_indices.get(&child).copied().ok_or_else(|| {
                    "candidate graph observation unavailable: missing tuple child identity"
                        .to_owned()
                })?;
                write!(output, "n{child}").map_err(cap)?;
            }
            output.write_str("])").map_err(cap)?;
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
    let mut module_names: HashMap<&DefId, &str> = HashMap::new();
    let mut local_names: HashMap<&HirLocalId, &str> = HashMap::new();
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
        source_value_into(
            hir,
            event.origin.identity,
            &mut module_names,
            &mut local_names,
            output,
        )?;
        write!(
            output,
            ", SCC {}), receiver=v{} (",
            event.origin.component, event.receiver.ordinal
        )
        .map_err(cap)?;
        source_value_into(
            hir,
            event.receiver.identity,
            &mut module_names,
            &mut local_names,
            output,
        )?;
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

fn source_value_into<'hir>(
    hir: &'hir HirModule,
    identity: CandidateSourceValueIdentity<'_>,
    module_names: &mut HashMap<&'hir DefId, &'hir str>,
    local_names: &mut HashMap<&'hir HirLocalId, &'hir str>,
    output: &mut Output,
) -> Result<(), String> {
    match identity {
        CandidateSourceValueIdentity::Module(id) => {
            let name = if let Some(name) = module_names.get(&id) {
                Some(*name)
            } else {
                let found = hir.items().iter().find_map(|item| match item {
                    HirItem::Binding(binding) if binding.id() == id => {
                        Some((binding.id(), binding.name().spelling()))
                    }
                    _ => None,
                });
                if let Some((key, name)) = found {
                    module_names.insert(key, name);
                    Some(name)
                } else {
                    None
                }
            };
            if let Some(name) = name {
                write!(output, "module {name}").map_err(cap)
            } else {
                output.write_str("module value").map_err(cap)
            }
        }
        CandidateSourceValueIdentity::Local(id) => {
            let name = if let Some(name) = local_names.get(&id) {
                Some(*name)
            } else {
                let found = hir.items().iter().find_map(|item| {
                    let local = local_source_for_item(hir, item)?;
                    local
                        .bindings()
                        .iter()
                        .find(|binding| &binding.id == id)
                        .map(|binding| (&binding.id, &*binding.spelling))
                });
                if let Some((key, name)) = found {
                    local_names.insert(key, name);
                    Some(name)
                } else {
                    None
                }
            };
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
