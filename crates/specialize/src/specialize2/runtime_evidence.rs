use mono::{EffectFamily, Program, StackWeight, Type};
use poly::expr as poly_expr;
use serde::{Deserialize, Serialize};
use std::fmt::Write as _;

use super::{
    EffectSubtractionDemand, SolvedExprType, SolvedTask, TypeGraph, TypeSlot, TypeSlotKind,
    TypeclassResolution, WeightedSlotEdge, WeightedTypeBound, stack_weight_is_empty,
};

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct SpecializeOutput {
    pub program: Program,
    pub runtime_evidence: RuntimeEvidenceSurface,
}

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct RuntimeEvidenceSurface {
    pub tasks: Vec<RuntimeEvidenceTask>,
}

impl RuntimeEvidenceSurface {
    pub(super) fn push_solved_task(
        &mut self,
        arena: &poly_expr::Arena,
        owner: RuntimeEvidenceTaskOwner,
        solved: &SolvedTask,
    ) {
        self.tasks
            .push(RuntimeEvidenceTask::from_solved(arena, owner, solved));
    }
}

pub fn format_runtime_evidence_surface(surface: &RuntimeEvidenceSurface) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "runtime evidence tasks [{}]", surface.tasks.len());
    for task in &surface.tasks {
        let _ = writeln!(out, "{}", format_task_header(task));
        format_graph_summary(&mut out, &task.graph);
        format_sites(&mut out, &task.sites);
        for expr in &task.expr_types {
            let consumer = expr
                .consumer
                .as_ref()
                .map(mono::dump::dump_type)
                .unwrap_or_else(|| "_".to_string());
            let _ = writeln!(
                out,
                "  expr e{} actual {} consumer {} stack_weights {}",
                expr.expr,
                mono::dump::dump_type(&expr.actual),
                consumer,
                expr.stack_weights.len()
            );
            format_stack_weights(&mut out, &expr.stack_weights);
        }
        for signature in &task.ref_signatures {
            let _ = writeln!(
                out,
                "  ref e{} signature {} stack_weights {}",
                signature.expr,
                mono::dump::dump_type(&signature.ty),
                signature.stack_weights.len()
            );
            format_stack_weights(&mut out, &signature.stack_weights);
        }
        for signature in &task.select_signatures {
            let _ = writeln!(
                out,
                "  select e{} signature {} stack_weights {}",
                signature.expr,
                mono::dump::dump_type(&signature.ty),
                signature.stack_weights.len()
            );
            format_stack_weights(&mut out, &signature.stack_weights);
        }
        for signature in &task.pat_ref_signatures {
            let _ = writeln!(
                out,
                "  pat p{} signature {} stack_weights {}",
                signature.pat,
                mono::dump::dump_type(&signature.ty),
                signature.stack_weights.len()
            );
            format_stack_weights(&mut out, &signature.stack_weights);
        }
        for resolution in &task.typeclass_resolutions {
            let _ = writeln!(
                out,
                "  typeclass e{} -> d{} signature {} stack_weights {}",
                resolution.expr,
                resolution.implementation,
                mono::dump::dump_type(&resolution.signature),
                resolution.stack_weights.len()
            );
            format_stack_weights(&mut out, &resolution.stack_weights);
        }
        if !task.raw_thunk_computations.is_empty() {
            let raw = task
                .raw_thunk_computations
                .iter()
                .map(|expr| format!("e{expr}"))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(out, "  raw thunk computations [{raw}]");
        }
    }
    out
}

fn format_graph_summary(out: &mut String, graph: &RuntimeEvidenceGraph) {
    let _ = writeln!(
        out,
        "  graph slots {} value {} effect {} constraints {} weighted_constraints {} weighted_lower {} weighted_upper {} weighted_edges {} effect_subtractions {} row_residuals {}",
        graph.slot_count,
        graph.value_slot_count,
        graph.effect_slot_count,
        graph.queued_constraint_count,
        graph.weighted_constraint_count,
        graph.weighted_lower_count,
        graph.weighted_upper_count,
        graph.weighted_edge_count,
        graph.effect_subtraction_count,
        graph.row_residuals.len(),
    );
    for residual in &graph.row_residuals {
        let retained = residual
            .retained_families
            .iter()
            .map(format_effect_family)
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(
            out,
            "    row residual t{} -> t{} retained [{}] weight {:?}",
            residual.source, residual.residual, retained, residual.weight
        );
    }
    for slot in graph
        .slots
        .iter()
        .filter(|slot| slot.has_runtime_evidence())
    {
        let _ = writeln!(
            out,
            "    slot t{} {:?} lower {} upper {} successors {} predecessors {} weighted_lower {} weighted_upper {} weighted_successors {} weighted_predecessors {} effect_subtractions {}",
            slot.id,
            slot.kind,
            slot.lower_count,
            slot.upper_count,
            slot.successor_count,
            slot.predecessor_count,
            slot.weighted_lower.len(),
            slot.weighted_upper.len(),
            slot.weighted_successors.len(),
            slot.weighted_predecessors.len(),
            slot.effect_subtractions.len(),
        );
        for bound in &slot.weighted_lower {
            let _ = writeln!(
                out,
                "      weighted lower {} lower {:?} upper {:?}",
                mono::dump::dump_type(&bound.ty),
                bound.lower_weight,
                bound.upper_weight
            );
        }
        for bound in &slot.weighted_upper {
            let _ = writeln!(
                out,
                "      weighted upper {} lower {:?} upper {:?}",
                mono::dump::dump_type(&bound.ty),
                bound.lower_weight,
                bound.upper_weight
            );
        }
        for edge in &slot.weighted_successors {
            let _ = writeln!(
                out,
                "      weighted successor t{} lower {:?} upper {:?}",
                edge.slot, edge.lower_weight, edge.upper_weight
            );
        }
        for edge in &slot.weighted_predecessors {
            let _ = writeln!(
                out,
                "      weighted predecessor t{} lower {:?} upper {:?}",
                edge.slot, edge.lower_weight, edge.upper_weight
            );
        }
        for demand in &slot.effect_subtractions {
            let handled = demand
                .handled_items
                .iter()
                .map(mono::dump::dump_type)
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(
                out,
                "      subtract tail {} runtime {} handled [{}]",
                mono::dump::dump_type(&demand.tail),
                mono::dump::dump_type(&demand.runtime_effect),
                handled
            );
        }
    }
}

fn format_sites(out: &mut String, sites: &[RuntimeEvidenceSite]) {
    if sites.is_empty() {
        return;
    }
    let _ = writeln!(out, "  sites {}", sites.len());
    for site in sites {
        let _ = writeln!(out, "    e{} {}", site.expr, format_site_kind(&site.kind));
        if let Some(boundary) = &site.boundary {
            let _ = writeln!(
                out,
                "      boundary actual {} consumer {} function_like {} argument_contract {}",
                mono::dump::dump_type(&boundary.actual),
                mono::dump::dump_type(&boundary.consumer),
                boundary.function_like,
                boundary.argument_contract,
            );
        }
    }
}

fn format_site_kind(kind: &RuntimeEvidenceSiteKind) -> String {
    match kind {
        RuntimeEvidenceSiteKind::OperationValue { def, path } => {
            format!("operation-value d{def} {}", path.join("::"))
        }
        RuntimeEvidenceSiteKind::OperationCall {
            callee,
            arg,
            def,
            path,
        } => format!(
            "operation-call callee e{callee} arg e{arg} d{def} {}",
            path.join("::")
        ),
        RuntimeEvidenceSiteKind::Catch {
            body,
            handled_paths,
            value_arm_count,
        } => {
            let handled = handled_paths
                .iter()
                .map(|path| path.join("::"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("catch body e{body} handled [{handled}] value_arms {value_arm_count}")
        }
        RuntimeEvidenceSiteKind::App {
            callee,
            arg,
            argument_contract,
        } => format!("app callee e{callee} arg e{arg} argument_contract {argument_contract}"),
        RuntimeEvidenceSiteKind::Lambda {
            param,
            body,
            argument_contract,
        } => format!("lambda param p{param} body e{body} argument_contract {argument_contract}"),
        RuntimeEvidenceSiteKind::RefSet { reference, value } => {
            format!("ref-set reference e{reference} value e{value}")
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RuntimeEvidenceTask {
    pub owner: RuntimeEvidenceTaskOwner,
    pub graph: RuntimeEvidenceGraph,
    pub sites: Vec<RuntimeEvidenceSite>,
    pub expr_types: Vec<RuntimeEvidenceExprType>,
    pub ref_signatures: Vec<RuntimeEvidenceTypeAtExpr>,
    pub select_signatures: Vec<RuntimeEvidenceTypeAtExpr>,
    pub pat_ref_signatures: Vec<RuntimeEvidenceTypeAtPat>,
    pub typeclass_resolutions: Vec<RuntimeEvidenceTypeclassResolution>,
    pub raw_thunk_computations: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceSite {
    pub expr: u32,
    pub kind: RuntimeEvidenceSiteKind,
    pub boundary: Option<RuntimeEvidenceBoundaryCandidate>,
}

impl RuntimeEvidenceSite {
    fn from_expr(
        arena: &poly_expr::Arena,
        expr: poly_expr::ExprId,
        ty: &SolvedExprType,
    ) -> Option<Self> {
        let kind = match arena.expr(expr) {
            poly_expr::Expr::Var(ref_id) => {
                let (def, path) = effect_operation_for_ref(arena, *ref_id)?;
                RuntimeEvidenceSiteKind::OperationValue { def: def.0, path }
            }
            poly_expr::Expr::App(callee, arg) => {
                if let poly_expr::Expr::Var(ref_id) = arena.expr(*callee)
                    && let Some((def, path)) = effect_operation_for_ref(arena, *ref_id)
                {
                    RuntimeEvidenceSiteKind::OperationCall {
                        callee: callee.0,
                        arg: arg.0,
                        def: def.0,
                        path,
                    }
                } else {
                    RuntimeEvidenceSiteKind::App {
                        callee: callee.0,
                        arg: arg.0,
                        argument_contract: callee_has_argument_effect_contract(arena, *callee),
                    }
                }
            }
            poly_expr::Expr::Catch(body, arms) => {
                let handled_paths = arms
                    .iter()
                    .filter_map(|arm| {
                        arm.operation
                            .as_ref()
                            .map(|operation| operation.path.clone())
                    })
                    .collect::<Vec<_>>();
                let value_arm_count =
                    arms.iter().filter(|arm| arm.operation.is_none()).count() as u32;
                RuntimeEvidenceSiteKind::Catch {
                    body: body.0,
                    handled_paths,
                    value_arm_count,
                }
            }
            poly_expr::Expr::Lambda(param, body) => RuntimeEvidenceSiteKind::Lambda {
                param: param.0,
                body: body.0,
                argument_contract: lambda_param_has_effect_contract(arena, *param),
            },
            poly_expr::Expr::RefSet(reference, value) => RuntimeEvidenceSiteKind::RefSet {
                reference: reference.0,
                value: value.0,
            },
            _ => return None,
        };
        Some(Self {
            expr: expr.0,
            boundary: RuntimeEvidenceBoundaryCandidate::from_expr_type(arena, expr, ty),
            kind,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceSiteKind {
    OperationValue {
        def: u32,
        path: Vec<String>,
    },
    OperationCall {
        callee: u32,
        arg: u32,
        def: u32,
        path: Vec<String>,
    },
    Catch {
        body: u32,
        handled_paths: Vec<Vec<String>>,
        value_arm_count: u32,
    },
    App {
        callee: u32,
        arg: u32,
        argument_contract: bool,
    },
    Lambda {
        param: u32,
        body: u32,
        argument_contract: bool,
    },
    RefSet {
        reference: u32,
        value: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceBoundaryCandidate {
    pub actual: Type,
    pub consumer: Type,
    pub function_like: bool,
    pub argument_contract: bool,
}

impl RuntimeEvidenceBoundaryCandidate {
    fn from_expr_type(
        arena: &poly_expr::Arena,
        expr: poly_expr::ExprId,
        ty: &SolvedExprType,
    ) -> Option<Self> {
        let consumer = ty.consumer.as_ref()?;
        let argument_contract = expr_has_effect_argument_contract(arena, expr);
        let function_like = type_is_function_like(&ty.actual) || type_is_function_like(consumer);
        if !argument_contract && !function_like {
            return None;
        }
        Some(Self {
            actual: ty.actual.clone(),
            consumer: consumer.clone(),
            function_like,
            argument_contract,
        })
    }
}

fn effect_operation_for_ref(
    arena: &poly_expr::Arena,
    ref_id: poly_expr::RefId,
) -> Option<(poly_expr::DefId, Vec<String>)> {
    let def = arena.ref_target(ref_id)?;
    let operation = arena.effect_operations.get(&def)?;
    Some((def, operation.path.clone()))
}

fn expr_has_effect_argument_contract(arena: &poly_expr::Arena, expr: poly_expr::ExprId) -> bool {
    match arena.expr(expr) {
        poly_expr::Expr::Lambda(param, _) => lambda_param_has_effect_contract(arena, *param),
        poly_expr::Expr::Var(ref_id) => {
            let Some(def) = arena.ref_target(*ref_id) else {
                return false;
            };
            def_lambda_param_has_effect_contract(arena, def, 0)
        }
        _ => false,
    }
}

fn callee_has_argument_effect_contract(
    arena: &poly_expr::Arena,
    callee: poly_expr::ExprId,
) -> bool {
    let (head, index) = call_spine_head_and_arg_index(arena, callee);
    match arena.expr(head) {
        poly_expr::Expr::Var(ref_id) => {
            let Some(def) = arena.ref_target(*ref_id) else {
                return false;
            };
            def_lambda_param_has_effect_contract(arena, def, index)
        }
        poly_expr::Expr::Lambda(param, body) => {
            lambda_chain_param_has_effect_contract(arena, *param, *body, index)
        }
        _ => false,
    }
}

fn call_spine_head_and_arg_index(
    arena: &poly_expr::Arena,
    mut callee: poly_expr::ExprId,
) -> (poly_expr::ExprId, usize) {
    let mut index = 0;
    while let poly_expr::Expr::App(next, _) = arena.expr(callee) {
        index += 1;
        callee = *next;
    }
    (callee, index)
}

fn def_lambda_param_has_effect_contract(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    index: usize,
) -> bool {
    let Some(poly_expr::Def::Let {
        body: Some(body), ..
    }) = arena.defs.get(def)
    else {
        return false;
    };
    let poly_expr::Expr::Lambda(param, body) = arena.expr(*body) else {
        return false;
    };
    lambda_chain_param_has_effect_contract(arena, *param, *body, index)
}

fn lambda_chain_param_has_effect_contract(
    arena: &poly_expr::Arena,
    param: poly_expr::PatId,
    body: poly_expr::ExprId,
    index: usize,
) -> bool {
    if index == 0 {
        return lambda_param_has_effect_contract(arena, param);
    }
    let poly_expr::Expr::Lambda(param, body) = arena.expr(body) else {
        return false;
    };
    lambda_chain_param_has_effect_contract(arena, *param, *body, index - 1)
}

fn lambda_param_has_effect_contract(arena: &poly_expr::Arena, pat: poly_expr::PatId) -> bool {
    let Some(def) = lambda_param_def(arena, pat) else {
        return false;
    };
    arena.arg_effect_contracts.contains_key(&def)
}

fn lambda_param_def(arena: &poly_expr::Arena, pat: poly_expr::PatId) -> Option<poly_expr::DefId> {
    match arena.pat(pat) {
        poly_expr::Pat::Var(def) => Some(*def),
        poly_expr::Pat::As(_, def) => Some(*def),
        _ => None,
    }
}

fn type_is_function_like(ty: &Type) -> bool {
    match ty {
        Type::Fun { .. } => true,
        Type::Stack { inner, .. } => type_is_function_like(inner),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_is_function_like(left) || type_is_function_like(right)
        }
        _ => false,
    }
}

impl RuntimeEvidenceTask {
    fn from_solved(
        arena: &poly_expr::Arena,
        owner: RuntimeEvidenceTaskOwner,
        solved: &SolvedTask,
    ) -> Self {
        let mut sites = solved
            .exprs
            .iter()
            .filter_map(|(expr, ty)| RuntimeEvidenceSite::from_expr(arena, *expr, ty))
            .collect::<Vec<_>>();
        sites.sort_by_key(|site| site.expr);

        let mut expr_types = solved
            .exprs
            .iter()
            .map(|(expr, ty)| RuntimeEvidenceExprType::new(*expr, &ty.actual, ty.consumer.as_ref()))
            .collect::<Vec<_>>();
        expr_types.sort_by_key(|item| item.expr);

        let mut ref_signatures = type_at_exprs(&solved.ref_signatures);
        let mut select_signatures = type_at_exprs(&solved.select_signatures);
        let mut pat_ref_signatures = solved
            .pat_ref_signatures
            .iter()
            .map(|(pat, ty)| RuntimeEvidenceTypeAtPat::new(*pat, ty))
            .collect::<Vec<_>>();
        let mut typeclass_resolutions = solved
            .typeclass_resolutions
            .iter()
            .map(|(expr, resolution)| RuntimeEvidenceTypeclassResolution::new(*expr, resolution))
            .collect::<Vec<_>>();
        let mut raw_thunk_computations = solved
            .raw_thunk_computations
            .iter()
            .map(|expr| expr.0)
            .collect::<Vec<_>>();

        ref_signatures.sort_by_key(|item| item.expr);
        select_signatures.sort_by_key(|item| item.expr);
        pat_ref_signatures.sort_by_key(|item| item.pat);
        typeclass_resolutions.sort_by_key(|item| item.expr);
        raw_thunk_computations.sort_unstable();

        Self {
            owner,
            graph: solved.runtime_evidence_graph.clone(),
            sites,
            expr_types,
            ref_signatures,
            select_signatures,
            pat_ref_signatures,
            typeclass_resolutions,
            raw_thunk_computations,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceGraph {
    pub slot_count: u32,
    pub value_slot_count: u32,
    pub effect_slot_count: u32,
    pub queued_constraint_count: u32,
    pub weighted_constraint_count: u32,
    pub weighted_lower_count: u32,
    pub weighted_upper_count: u32,
    pub weighted_edge_count: u32,
    pub effect_subtraction_count: u32,
    pub row_residuals: Vec<RuntimeEvidenceRowResidual>,
    pub slots: Vec<RuntimeEvidenceSlot>,
}

impl RuntimeEvidenceGraph {
    pub(super) fn from_type_graph(graph: &TypeGraph<'_>) -> Self {
        let mut value_slot_count = 0u32;
        let mut effect_slot_count = 0u32;
        let mut weighted_lower_count = 0u32;
        let mut weighted_upper_count = 0u32;
        let mut weighted_edge_count = 0u32;
        let mut effect_subtraction_count = 0u32;
        let slots = graph
            .slots
            .iter()
            .enumerate()
            .map(|(id, slot)| {
                match slot.kind {
                    TypeSlotKind::Value => value_slot_count += 1,
                    TypeSlotKind::Effect => effect_slot_count += 1,
                }
                weighted_lower_count += slot.weighted_lower.len() as u32;
                weighted_upper_count += slot.weighted_upper.len() as u32;
                weighted_edge_count += slot.weighted_successors.len() as u32;
                effect_subtraction_count += slot.effect_subtraction_consumers.len() as u32;
                RuntimeEvidenceSlot::from_slot(id as u32, slot)
            })
            .collect::<Vec<_>>();
        let weighted_constraint_count = graph
            .queued_constraints
            .iter()
            .filter(|constraint| {
                !stack_weight_is_empty(&constraint.lower_weight)
                    || !stack_weight_is_empty(&constraint.upper_weight)
            })
            .count() as u32;
        let mut row_residuals = graph
            .row_residuals
            .iter()
            .map(|(key, residual)| RuntimeEvidenceRowResidual {
                source: key.source,
                retained_families: key.retained_families.clone(),
                weight: key.weight.clone(),
                residual: *residual,
            })
            .collect::<Vec<_>>();
        row_residuals.sort_by(|left, right| {
            left.source
                .cmp(&right.source)
                .then_with(|| left.residual.cmp(&right.residual))
                .then_with(|| {
                    format!("{:?}", left.retained_families)
                        .cmp(&format!("{:?}", right.retained_families))
                })
                .then_with(|| format!("{:?}", left.weight).cmp(&format!("{:?}", right.weight)))
        });
        Self {
            slot_count: graph.slots.len() as u32,
            value_slot_count,
            effect_slot_count,
            queued_constraint_count: graph.queued_constraints.len() as u32,
            weighted_constraint_count,
            weighted_lower_count,
            weighted_upper_count,
            weighted_edge_count,
            effect_subtraction_count,
            row_residuals,
            slots,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceSlot {
    pub id: u32,
    pub kind: RuntimeEvidenceSlotKind,
    pub lower_count: u32,
    pub upper_count: u32,
    pub successor_count: u32,
    pub predecessor_count: u32,
    pub weighted_lower: Vec<RuntimeEvidenceWeightedTypeBound>,
    pub weighted_upper: Vec<RuntimeEvidenceWeightedTypeBound>,
    pub weighted_successors: Vec<RuntimeEvidenceWeightedSlotEdge>,
    pub weighted_predecessors: Vec<RuntimeEvidenceWeightedSlotEdge>,
    pub effect_subtractions: Vec<RuntimeEvidenceEffectSubtraction>,
}

impl RuntimeEvidenceSlot {
    fn from_slot(id: u32, slot: &TypeSlot) -> Self {
        Self {
            id,
            kind: RuntimeEvidenceSlotKind::from_kind(slot.kind),
            lower_count: slot.lower.len() as u32,
            upper_count: slot.upper.len() as u32,
            successor_count: slot.successors.len() as u32,
            predecessor_count: slot.predecessors.len() as u32,
            weighted_lower: weighted_type_bounds(&slot.weighted_lower),
            weighted_upper: weighted_type_bounds(&slot.weighted_upper),
            weighted_successors: weighted_slot_edges(&slot.weighted_successors),
            weighted_predecessors: weighted_slot_edges(&slot.weighted_predecessors),
            effect_subtractions: slot
                .effect_subtraction_consumers
                .iter()
                .map(RuntimeEvidenceEffectSubtraction::from_demand)
                .collect(),
        }
    }

    fn has_runtime_evidence(&self) -> bool {
        !self.weighted_lower.is_empty()
            || !self.weighted_upper.is_empty()
            || !self.weighted_successors.is_empty()
            || !self.weighted_predecessors.is_empty()
            || !self.effect_subtractions.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceSlotKind {
    Value,
    Effect,
}

impl RuntimeEvidenceSlotKind {
    fn from_kind(kind: TypeSlotKind) -> Self {
        match kind {
            TypeSlotKind::Value => Self::Value,
            TypeSlotKind::Effect => Self::Effect,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceWeightedTypeBound {
    pub ty: Type,
    pub lower_weight: StackWeight,
    pub upper_weight: StackWeight,
}

impl RuntimeEvidenceWeightedTypeBound {
    fn from_bound(bound: &WeightedTypeBound) -> Self {
        Self {
            ty: bound.ty.clone(),
            lower_weight: bound.lower_weight.clone(),
            upper_weight: bound.upper_weight.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceWeightedSlotEdge {
    pub slot: u32,
    pub lower_weight: StackWeight,
    pub upper_weight: StackWeight,
}

impl RuntimeEvidenceWeightedSlotEdge {
    fn from_edge(edge: &WeightedSlotEdge) -> Self {
        Self {
            slot: edge.slot,
            lower_weight: edge.lower_weight.clone(),
            upper_weight: edge.upper_weight.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceEffectSubtraction {
    pub tail: Type,
    pub runtime_effect: Type,
    pub handled_items: Vec<Type>,
}

impl RuntimeEvidenceEffectSubtraction {
    fn from_demand(demand: &EffectSubtractionDemand) -> Self {
        Self {
            tail: demand.tail.clone(),
            runtime_effect: demand.runtime_effect.clone(),
            handled_items: demand.handled_items.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceRowResidual {
    pub source: u32,
    pub retained_families: Vec<EffectFamily>,
    pub weight: StackWeight,
    pub residual: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceTaskOwner {
    RootExpr { root_index: u32, expr: u32 },
    InstanceBody { instance: u32, def: u32, body: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceExprType {
    pub expr: u32,
    pub actual: Type,
    pub consumer: Option<Type>,
    pub stack_weights: Vec<RuntimeEvidenceStackWeight>,
}

impl RuntimeEvidenceExprType {
    fn new(expr: poly_expr::ExprId, actual: &Type, consumer: Option<&Type>) -> Self {
        let mut stack_weights = Vec::new();
        collect_stack_weights(
            RuntimeEvidenceTypeRole::Actual,
            actual,
            &mut Vec::new(),
            &mut stack_weights,
        );
        if let Some(consumer) = consumer {
            collect_stack_weights(
                RuntimeEvidenceTypeRole::Consumer,
                consumer,
                &mut Vec::new(),
                &mut stack_weights,
            );
        }
        Self {
            expr: expr.0,
            actual: actual.clone(),
            consumer: consumer.cloned(),
            stack_weights,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceTypeAtExpr {
    pub expr: u32,
    pub ty: Type,
    pub stack_weights: Vec<RuntimeEvidenceStackWeight>,
}

impl RuntimeEvidenceTypeAtExpr {
    fn new(expr: poly_expr::ExprId, ty: &Type) -> Self {
        Self {
            expr: expr.0,
            ty: ty.clone(),
            stack_weights: stack_weights_for(RuntimeEvidenceTypeRole::Signature, ty),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceTypeAtPat {
    pub pat: u32,
    pub ty: Type,
    pub stack_weights: Vec<RuntimeEvidenceStackWeight>,
}

impl RuntimeEvidenceTypeAtPat {
    fn new(pat: poly_expr::PatId, ty: &Type) -> Self {
        Self {
            pat: pat.0,
            ty: ty.clone(),
            stack_weights: stack_weights_for(RuntimeEvidenceTypeRole::Signature, ty),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceTypeclassResolution {
    pub expr: u32,
    pub implementation: u32,
    pub signature: Type,
    pub stack_weights: Vec<RuntimeEvidenceStackWeight>,
}

impl RuntimeEvidenceTypeclassResolution {
    fn new(expr: poly_expr::ExprId, resolution: &TypeclassResolution) -> Self {
        Self {
            expr: expr.0,
            implementation: resolution.implementation.0,
            signature: resolution.signature.clone(),
            stack_weights: stack_weights_for(
                RuntimeEvidenceTypeRole::Signature,
                &resolution.signature,
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeEvidenceStackWeight {
    pub role: RuntimeEvidenceTypeRole,
    pub path: Vec<RuntimeEvidenceTypePathStep>,
    pub weight: StackWeight,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceTypeRole {
    Actual,
    Consumer,
    Signature,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuntimeEvidenceTypePathStep {
    Inner,
    FunArg,
    FunArgEffect,
    FunRetEffect,
    FunRet,
    ThunkEffect,
    ThunkValue,
    RecordField { name: String },
    VariantPayload { name: String, index: u32 },
    TupleItem { index: u32 },
    EffectRowItem { index: u32 },
    UnionLeft,
    UnionRight,
    IntersectionLeft,
    IntersectionRight,
    ConArg { index: u32 },
}

fn type_at_exprs(
    types: &std::collections::HashMap<poly_expr::ExprId, Type>,
) -> Vec<RuntimeEvidenceTypeAtExpr> {
    types
        .iter()
        .map(|(expr, ty)| RuntimeEvidenceTypeAtExpr::new(*expr, ty))
        .collect()
}

fn weighted_type_bounds(bounds: &[WeightedTypeBound]) -> Vec<RuntimeEvidenceWeightedTypeBound> {
    bounds
        .iter()
        .map(RuntimeEvidenceWeightedTypeBound::from_bound)
        .collect()
}

fn weighted_slot_edges(edges: &[WeightedSlotEdge]) -> Vec<RuntimeEvidenceWeightedSlotEdge> {
    edges
        .iter()
        .map(RuntimeEvidenceWeightedSlotEdge::from_edge)
        .collect()
}

fn format_effect_family(family: &EffectFamily) -> String {
    if family.args.is_empty() {
        return family.path.join("::");
    }
    let args = family
        .args
        .iter()
        .map(mono::dump::dump_type)
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}({args})", family.path.join("::"))
}

fn format_task_header(task: &RuntimeEvidenceTask) -> String {
    match task.owner {
        RuntimeEvidenceTaskOwner::RootExpr { root_index, expr } => format!(
            "task root[{root_index}] expr e{expr} expr_types {} refs {} selects {} pats {} typeclasses {} raw_thunks {}",
            task.expr_types.len(),
            task.ref_signatures.len(),
            task.select_signatures.len(),
            task.pat_ref_signatures.len(),
            task.typeclass_resolutions.len(),
            task.raw_thunk_computations.len(),
        ),
        RuntimeEvidenceTaskOwner::InstanceBody {
            instance,
            def,
            body,
        } => format!(
            "task instance m{instance} def d{def} body e{body} expr_types {} refs {} selects {} pats {} typeclasses {} raw_thunks {}",
            task.expr_types.len(),
            task.ref_signatures.len(),
            task.select_signatures.len(),
            task.pat_ref_signatures.len(),
            task.typeclass_resolutions.len(),
            task.raw_thunk_computations.len(),
        ),
    }
}

fn format_stack_weights(out: &mut String, weights: &[RuntimeEvidenceStackWeight]) {
    for weight in weights {
        let path = weight
            .path
            .iter()
            .map(format_path_step)
            .collect::<Vec<_>>()
            .join(".");
        let path = if path.is_empty() {
            "<root>".to_string()
        } else {
            path
        };
        let _ = writeln!(
            out,
            "    stack {:?} at {}: {:?}",
            weight.role, path, weight.weight
        );
    }
}

fn format_path_step(step: &RuntimeEvidenceTypePathStep) -> String {
    match step {
        RuntimeEvidenceTypePathStep::Inner => "inner".to_string(),
        RuntimeEvidenceTypePathStep::FunArg => "fun.arg".to_string(),
        RuntimeEvidenceTypePathStep::FunArgEffect => "fun.arg_effect".to_string(),
        RuntimeEvidenceTypePathStep::FunRetEffect => "fun.ret_effect".to_string(),
        RuntimeEvidenceTypePathStep::FunRet => "fun.ret".to_string(),
        RuntimeEvidenceTypePathStep::ThunkEffect => "thunk.effect".to_string(),
        RuntimeEvidenceTypePathStep::ThunkValue => "thunk.value".to_string(),
        RuntimeEvidenceTypePathStep::RecordField { name } => format!("record.{name}"),
        RuntimeEvidenceTypePathStep::VariantPayload { name, index } => {
            format!("variant.{name}.{index}")
        }
        RuntimeEvidenceTypePathStep::TupleItem { index } => format!("tuple.{index}"),
        RuntimeEvidenceTypePathStep::EffectRowItem { index } => format!("effect.{index}"),
        RuntimeEvidenceTypePathStep::UnionLeft => "union.left".to_string(),
        RuntimeEvidenceTypePathStep::UnionRight => "union.right".to_string(),
        RuntimeEvidenceTypePathStep::IntersectionLeft => "intersection.left".to_string(),
        RuntimeEvidenceTypePathStep::IntersectionRight => "intersection.right".to_string(),
        RuntimeEvidenceTypePathStep::ConArg { index } => format!("con.{index}"),
    }
}

fn stack_weights_for(role: RuntimeEvidenceTypeRole, ty: &Type) -> Vec<RuntimeEvidenceStackWeight> {
    let mut out = Vec::new();
    collect_stack_weights(role, ty, &mut Vec::new(), &mut out);
    out
}

fn collect_stack_weights(
    role: RuntimeEvidenceTypeRole,
    ty: &Type,
    path: &mut Vec<RuntimeEvidenceTypePathStep>,
    out: &mut Vec<RuntimeEvidenceStackWeight>,
) {
    match ty {
        Type::Stack { inner, weight } => {
            out.push(RuntimeEvidenceStackWeight {
                role,
                path: path.clone(),
                weight: weight.clone(),
            });
            path.push(RuntimeEvidenceTypePathStep::Inner);
            collect_stack_weights(role, inner, path, out);
            path.pop();
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            with_path(path, RuntimeEvidenceTypePathStep::FunArg, |path| {
                collect_stack_weights(role, arg, path, out)
            });
            with_path(path, RuntimeEvidenceTypePathStep::FunArgEffect, |path| {
                collect_stack_weights(role, arg_effect, path, out)
            });
            with_path(path, RuntimeEvidenceTypePathStep::FunRetEffect, |path| {
                collect_stack_weights(role, ret_effect, path, out)
            });
            with_path(path, RuntimeEvidenceTypePathStep::FunRet, |path| {
                collect_stack_weights(role, ret, path, out)
            });
        }
        Type::Thunk { effect, value } => {
            with_path(path, RuntimeEvidenceTypePathStep::ThunkEffect, |path| {
                collect_stack_weights(role, effect, path, out)
            });
            with_path(path, RuntimeEvidenceTypePathStep::ThunkValue, |path| {
                collect_stack_weights(role, value, path, out)
            });
        }
        Type::Record(fields) => {
            for field in fields {
                with_path(
                    path,
                    RuntimeEvidenceTypePathStep::RecordField {
                        name: field.name.clone(),
                    },
                    |path| collect_stack_weights(role, &field.value, path, out),
                );
            }
        }
        Type::PolyVariant(variants) => {
            for variant in variants {
                for (index, payload) in variant.payloads.iter().enumerate() {
                    with_path(
                        path,
                        RuntimeEvidenceTypePathStep::VariantPayload {
                            name: variant.name.clone(),
                            index: index as u32,
                        },
                        |path| collect_stack_weights(role, payload, path, out),
                    );
                }
            }
        }
        Type::Tuple(items) => {
            for (index, item) in items.iter().enumerate() {
                with_path(
                    path,
                    RuntimeEvidenceTypePathStep::TupleItem {
                        index: index as u32,
                    },
                    |path| collect_stack_weights(role, item, path, out),
                );
            }
        }
        Type::EffectRow(items) => {
            for (index, item) in items.iter().enumerate() {
                with_path(
                    path,
                    RuntimeEvidenceTypePathStep::EffectRowItem {
                        index: index as u32,
                    },
                    |path| collect_stack_weights(role, item, path, out),
                );
            }
        }
        Type::Union(left, right) => {
            with_path(path, RuntimeEvidenceTypePathStep::UnionLeft, |path| {
                collect_stack_weights(role, left, path, out)
            });
            with_path(path, RuntimeEvidenceTypePathStep::UnionRight, |path| {
                collect_stack_weights(role, right, path, out)
            });
        }
        Type::Intersection(left, right) => {
            with_path(
                path,
                RuntimeEvidenceTypePathStep::IntersectionLeft,
                |path| collect_stack_weights(role, left, path, out),
            );
            with_path(
                path,
                RuntimeEvidenceTypePathStep::IntersectionRight,
                |path| collect_stack_weights(role, right, path, out),
            );
        }
        Type::Con { args, .. } => {
            for (index, arg) in args.iter().enumerate() {
                with_path(
                    path,
                    RuntimeEvidenceTypePathStep::ConArg {
                        index: index as u32,
                    },
                    |path| collect_stack_weights(role, arg, path, out),
                );
            }
        }
        Type::Any | Type::Never | Type::OpenVar(_) => {}
    }
}

fn with_path(
    path: &mut Vec<RuntimeEvidenceTypePathStep>,
    step: RuntimeEvidenceTypePathStep,
    f: impl FnOnce(&mut Vec<RuntimeEvidenceTypePathStep>),
) {
    path.push(step);
    f(path);
    path.pop();
}
