//! mono 用 simple-sub 推論をもう一度走らせる `specialize2` の入口。
//!
//! 既存 `solve` は expression へ expected type を手渡す形に寄っている。ここでは task-local な
//! type variable と subtype 制約から concrete annotation を作り、その結果から次の mono demand を
//! 再帰的に展開する。

use std::collections::{HashMap, HashSet, VecDeque};

use mono::{
    ApplicationProvenanceTag, ApplicationSpecializationTask, Block, CaseArm, CatchArm,
    ComputationType, EffectFamilies, EffectFamily, EffectiveThunkType, Expr, ExprKind, Instance,
    InstanceId, InstanceSource, Pat, Program, RecordField, RecordSpread, Root, SelectResolution,
    SelectionProvenanceTag, Signature, StackWeight, StackWeightEntry, Stmt, Type, TypeField,
    TypeVariant,
};
use poly::expr as poly_expr;
use poly::provenance::{
    ProvenanceAnchor, ProvenanceCompleteness, SubtypeProvenanceSidecar, TypePositionStep,
};

use crate::{
    ExprTypeRole, RoleMethodCheckOutcome, RoleMethodCheckResolution, SpecializeError,
    UnsatisfiedSubtypeOrigin, convert_def, convert_def_spread, convert_lit, convert_primitive_op,
    convert_vis, def_kind, equivalent_boundary_types, hygiene, lit_type, primitive_context, roles,
    std_types, types,
};

mod candidate;
mod effect;
mod emit;
mod marker;
mod role_method_check;
mod runtime_evidence;
mod runtime_shape;
mod task_solver;
#[cfg(test)]
mod tests;
mod type_graph;
mod type_resolver;

use candidate::*;
use effect::*;
use marker::*;
pub use runtime_evidence::{
    RuntimeEvidenceBoundaryCandidate, RuntimeEvidenceEffectSubtraction, RuntimeEvidenceExprType,
    RuntimeEvidenceGraph, RuntimeEvidenceKnownStateAccessRole,
    RuntimeEvidenceKnownStateContinuationSemantics, RuntimeEvidenceKnownStateHandler,
    RuntimeEvidenceKnownStateHandlerSource, RuntimeEvidenceNode, RuntimeEvidenceNodeEvidenceRef,
    RuntimeEvidenceNodeKind, RuntimeEvidenceRowResidual, RuntimeEvidenceSite,
    RuntimeEvidenceSiteKind, RuntimeEvidenceSlot, RuntimeEvidenceSlotKind,
    RuntimeEvidenceStackWeight, RuntimeEvidenceStaticRoute,
    RuntimeEvidenceStaticRouteDynamicReason, RuntimeEvidenceStaticRouteResolution,
    RuntimeEvidenceSurface, RuntimeEvidenceTask, RuntimeEvidenceTaskOwner,
    RuntimeEvidenceTypeAtExpr, RuntimeEvidenceTypeAtPat, RuntimeEvidenceTypePathStep,
    RuntimeEvidenceTypeRole, RuntimeEvidenceTypeclassResolution, RuntimeEvidenceWeightedSlotEdge,
    RuntimeEvidenceWeightedTypeBound, SpecializeOutput, format_runtime_evidence_surface,
};
use runtime_shape::*;

pub(crate) fn specialize_with_runtime_evidence(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
) -> Result<SpecializeOutput, SpecializeError> {
    Specializer2::new(sidecar).specialize_with_runtime_evidence(arena)
}

pub(crate) fn specialize_with_runtime_evidence_and_application_provenance(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
    source_applications: impl IntoIterator<Item = poly_expr::ExprId>,
) -> Result<SpecializeOutput, SpecializeError> {
    Specializer2::with_source_applications(sidecar, source_applications)
        .specialize_with_runtime_evidence(arena)
}

pub(crate) fn specialize_with_runtime_evidence_and_source_provenance(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
    source_applications: impl IntoIterator<Item = poly_expr::ExprId>,
    source_selections: impl IntoIterator<Item = poly_expr::SelectId>,
) -> Result<SpecializeOutput, SpecializeError> {
    Specializer2::with_source_provenance(sidecar, source_applications, source_selections)
        .specialize_with_runtime_evidence(arena)
}

pub(crate) fn specialize(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
) -> Result<Program, SpecializeError> {
    Specializer2::new(sidecar).specialize(arena)
}

#[cfg(test)]
fn specialize_with_captured_subtype_failures(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
) -> (
    Result<Program, SpecializeError>,
    Vec<SubtypeFailureProvenance>,
) {
    type_graph::capture_shadow_subtype_failures(|| specialize(arena, sidecar))
}

pub(crate) fn role_method_check(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
) -> Vec<RoleMethodCheckOutcome> {
    RoleMethodChecker::new().check(arena, sidecar)
}

struct Specializer2<'a> {
    sidecar: &'a SubtypeProvenanceSidecar,
    instances: Vec<Option<Instance>>,
    instance_by_key: HashMap<InstanceKey, InstanceId>,
    pending_instances: VecDeque<PendingInstance>,
    local_defs: HashMap<poly_expr::DefId, usize>,
    force_block_tail_exprs: HashSet<poly_expr::ExprId>,
    runtime_evidence: RuntimeEvidenceSurface,
    source_applications: HashSet<poly_expr::ExprId>,
    source_selections: HashSet<poly_expr::SelectId>,
    active_task: Option<ApplicationSpecializationTask>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InstanceKey {
    def: poly_expr::DefId,
    ty: Type,
}

struct PendingInstance {
    id: InstanceId,
    def: poly_expr::DefId,
    body: poly_expr::ExprId,
    inference_signature_ty: Type,
    runtime_signature_ty: Type,
    marker_signature_ty: Type,
}

#[derive(Debug, Clone)]
struct EmittedExpr {
    expr: Expr,
    computation: Option<ComputationShape>,
}

impl EmittedExpr {
    fn pure(expr: Expr, value: Option<Type>) -> Self {
        Self {
            expr,
            computation: value.map(ComputationShape::pure),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ComputationShape {
    effect: Type,
    value: Type,
}

impl ComputationShape {
    fn pure(value: Type) -> Self {
        Self {
            effect: Type::pure_effect(),
            value,
        }
    }

    fn from_runtime_type(ty: &Type) -> Self {
        match ty {
            Type::Thunk { effect, value } => Self {
                effect: effect.as_ref().clone(),
                value: value.as_ref().clone(),
            },
            value => Self::pure(value.clone()),
        }
    }
}

struct SolvedTask {
    exprs: HashMap<poly_expr::ExprId, SolvedExprType>,
    ref_signatures: HashMap<poly_expr::ExprId, Type>,
    select_signatures: HashMap<poly_expr::ExprId, Type>,
    typeclass_resolutions: HashMap<poly_expr::ExprId, TypeclassResolution>,
    pat_ref_signatures: HashMap<poly_expr::PatId, Type>,
    raw_thunk_computations: HashSet<poly_expr::ExprId>,
    runtime_evidence_graph: RuntimeEvidenceGraph,
}

impl SolvedTask {
    fn actual_type_of(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.exprs.get(&expr).map(|ty| &ty.actual)
    }

    fn consumer_type_of(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.exprs.get(&expr).and_then(|ty| ty.consumer.as_ref())
    }

    fn emitted_type_of(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.consumer_type_of(expr)
            .or_else(|| self.actual_type_of(expr))
    }

    fn ref_signature(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.ref_signatures.get(&expr)
    }

    fn select_signature(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.select_signatures.get(&expr)
    }

    fn typeclass_resolution(&self, expr: poly_expr::ExprId) -> Option<&TypeclassResolution> {
        self.typeclass_resolutions.get(&expr)
    }

    fn pat_ref_signature(&self, pat: poly_expr::PatId) -> Option<&Type> {
        self.pat_ref_signatures.get(&pat)
    }

    fn is_raw_thunk_computation(&self, expr: poly_expr::ExprId) -> bool {
        self.raw_thunk_computations.contains(&expr)
    }
}

#[derive(Debug, Clone)]
struct SolvedExprType {
    actual: Type,
    consumer: Option<Type>,
    actual_slots: Vec<u32>,
    consumer_slots: Vec<u32>,
}

#[derive(Debug, Clone)]
struct TypeclassResolution {
    implementation: poly_expr::DefId,
    signature: Type,
}

enum TypeclassMethodResolution {
    Resolved(poly_expr::DefId),
    DefaultBody,
    Unresolved,
    Ambiguous(Vec<poly_expr::DefId>),
}

#[derive(Default)]
struct RoleMethodChecker {
    outcomes: Vec<RoleMethodCheckOutcome>,
    checked_instances: HashSet<InstanceKey>,
}

struct RoleMethodCheckTask {
    outcomes: Vec<RoleMethodCheckOutcome>,
    ref_signatures: HashMap<poly_expr::ExprId, Type>,
    select_signatures: HashMap<poly_expr::ExprId, Type>,
    typeclass_resolutions: HashMap<poly_expr::ExprId, TypeclassResolution>,
}

struct LocalLetBindingType {
    ty: Type,
    exact_value: bool,
    use_as_lambda_signature: bool,
}

impl LocalLetBindingType {
    fn fresh(graph: &mut TypeGraph<'_>) -> Self {
        Self {
            ty: graph.fresh_value(),
            exact_value: true,
            use_as_lambda_signature: false,
        }
    }
}

struct TaskSolver<'a> {
    arena: &'a poly_expr::Arena,
    #[allow(dead_code)] // SUBP-I-1 stores the cold-build sidecar for later shadow root wiring.
    sidecar: &'a SubtypeProvenanceSidecar,
    graph: TypeGraph<'a>,
    exprs: HashMap<poly_expr::ExprId, ExprType>,
    locals: HashMap<poly_expr::DefId, Type>,
    discarded_exprs: HashSet<poly_expr::ExprId>,
    ref_uses: Vec<RefUse>,
    select_uses: Vec<SelectUse>,
    typeclass_uses: Vec<TypeclassUse>,
    pat_ref_uses: Vec<PatRefUse>,
    required_exprs: HashSet<poly_expr::ExprId>,
    raw_thunk_computations: HashSet<poly_expr::ExprId>,
}

struct ExprType {
    actual: Type,
    consumer: Option<Type>,
}

#[derive(Debug, Clone)]
struct RefUse {
    expr: poly_expr::ExprId,
    ty: Type,
}

#[derive(Debug, Clone)]
struct SelectUse {
    expr: poly_expr::ExprId,
    ty: Type,
}

#[derive(Debug, Clone)]
struct TypeclassUse {
    expr: poly_expr::ExprId,
    member: poly_expr::DefId,
    method_ty: Type,
}

struct SelectedMethodDemand {
    evaluation_effect: Type,
    signature: Type,
}

#[derive(Debug, Clone)]
struct PatRefUse {
    pat: poly_expr::PatId,
    ty: Type,
}

struct CatchOperationTypes {
    payload: Type,
    continuation_input: Type,
    effect: Type,
    residual_effect: Type,
}

struct TypeGraph<'a> {
    arena: &'a poly_expr::Arena,
    effect_family_paths: HashSet<Vec<String>>,
    slots: Vec<TypeSlot>,
    pending: VecDeque<SubtypeConstraint>,
    queued_constraints: HashSet<SubtypeConstraint>,
    subtype_provenance_records: Vec<SpecializeSubtypeProvenanceRecord>,
    subtype_provenance_by_key: HashMap<SubtypeConstraint, SpecializeSubtypeProvenanceRecordId>,
    subtype_position_provenance: Vec<SubtypePositionProvenance>,
    shadow_subtype_failures: Vec<SubtypeFailureProvenance>,
    subtype_provenance_metrics: SpecializeSubtypeProvenanceMetrics,
    row_residuals: HashMap<RowResidualKey, u32>,
    closed_effect_subtraction_consumers: HashSet<(u32, EffectSubtractionDemand)>,
    role_demands: Vec<types::InstantiatedRolePredicate>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SpecializeSubtypeProvenanceRecordId(u32);

impl SpecializeSubtypeProvenanceRecordId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SpecializeSubtypeProvenanceRecord {
    semantic_key: SubtypeConstraint,
    incoming: Vec<SpecializeProvenanceDerivation>,
    completeness: ProvenanceCompleteness,
}

#[allow(dead_code)] // Open-variable parent fan-in remains explicitly incomplete in SUBP-F.
#[derive(Debug, Clone, PartialEq, Eq)]
enum SpecializeProvenanceDerivation {
    Root {
        lower: Vec<ProvenanceAnchor>,
        upper: Vec<ProvenanceAnchor>,
    },
    Structural {
        parent: SpecializeSubtypeProvenanceRecordId,
        step: TypePositionStep,
    },
    OpenVarBound {
        parents: Vec<SpecializeSubtypeProvenanceRecordId>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SubtypePositionProvenance {
    lower: types::MaterializedTypeProvenance,
    upper: types::MaterializedTypeProvenance,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SubtypeFailureProvenance {
    record: SpecializeSubtypeProvenanceRecordId,
    lower: Vec<ProvenanceAnchor>,
    upper: Vec<ProvenanceAnchor>,
    completeness: ProvenanceCompleteness,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct SpecializeSubtypeProvenanceMetrics {
    records: usize,
    incoming_considered: usize,
    incoming_inserted: usize,
    incoming_deduplicated: usize,
    semantic_enqueues: usize,
    budget_exhaustions: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeSlotKind {
    Value,
    Effect,
}

fn effect_slot_candidate(graph: &TypeGraph<'_>, slot_kind: TypeSlotKind, ty: Type) -> Option<Type> {
    if slot_kind != TypeSlotKind::Effect {
        return Some(ty);
    }
    normalize_effect_candidate(graph, ty)
}

fn effect_candidate_items(graph: &TypeGraph<'_>, ty: Type) -> Option<Vec<Type>> {
    match ty {
        Type::EffectRow(items) => normalize_effect_row_candidate(graph, items),
        ty if ty.is_pure_effect() => Some(Vec::new()),
        Type::Con { path, args } if graph.is_effect_family_path(&path) => {
            Some(vec![Type::Con { path, args }])
        }
        _ => None,
    }
}

fn normalize_effect_candidate(graph: &TypeGraph<'_>, ty: Type) -> Option<Type> {
    match ty {
        Type::EffectRow(items) => normalize_effect_row_candidate(graph, items).map(Type::EffectRow),
        Type::Stack { .. } | Type::Any => Some(ty),
        ty if ty.is_pure_effect() => Some(Type::pure_effect()),
        Type::Con { path, args } if graph.is_effect_family_path(&path) => {
            Some(Type::EffectRow(vec![Type::Con { path, args }]))
        }
        ty if type_is_effect_tail_candidate(graph, &ty) => Some(Type::EffectRow(vec![ty])),
        _ => None,
    }
}

fn normalize_effect_row_candidate(graph: &TypeGraph<'_>, items: Vec<Type>) -> Option<Vec<Type>> {
    if items.is_empty() {
        return Some(Vec::new());
    }
    let mut out = Vec::new();
    for item in items {
        push_normalized_effect_item(graph, item, &mut out);
    }
    (!out.is_empty()).then_some(out)
}

fn push_normalized_effect_item(graph: &TypeGraph<'_>, item: Type, out: &mut Vec<Type>) {
    match item {
        Type::EffectRow(items) => {
            for item in items {
                push_normalized_effect_item(graph, item, out);
            }
        }
        item if item.is_pure_effect() => {}
        Type::Con { path, args } if graph.is_effect_family_path(&path) => {
            out.push(Type::Con { path, args });
        }
        item if type_is_effect_tail_candidate(graph, &item) => out.push(item),
        Type::Any => out.push(Type::Any),
        _ => {}
    }
}

#[derive(Debug, Clone)]
struct TypeSlot {
    kind: TypeSlotKind,
    lower: Vec<Type>,
    upper: Vec<Type>,
    weighted_lower: Vec<WeightedTypeBound>,
    weighted_upper: Vec<WeightedTypeBound>,
    successors: Vec<u32>,
    predecessors: Vec<u32>,
    weighted_successors: Vec<WeightedSlotEdge>,
    weighted_predecessors: Vec<WeightedSlotEdge>,
    effect_subtraction_consumers: Vec<EffectSubtractionDemand>,
}

impl TypeSlot {
    fn new(kind: TypeSlotKind) -> Self {
        Self {
            kind,
            lower: Vec::new(),
            upper: Vec::new(),
            weighted_lower: Vec::new(),
            weighted_upper: Vec::new(),
            successors: Vec::new(),
            predecessors: Vec::new(),
            weighted_successors: Vec::new(),
            weighted_predecessors: Vec::new(),
            effect_subtraction_consumers: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SubtypeConstraint {
    lower: Type,
    lower_weight: StackWeight,
    upper: Type,
    upper_weight: StackWeight,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct WeightedTypeBound {
    ty: Type,
    lower_weight: StackWeight,
    upper_weight: StackWeight,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct WeightedSlotEdge {
    slot: u32,
    lower_weight: StackWeight,
    upper_weight: StackWeight,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RowResidualKey {
    source: u32,
    retained_families: Vec<EffectFamily>,
    weight: StackWeight,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct EffectSubtractionDemand {
    tail: Type,
    runtime_effect: Type,
    handled_items: Vec<Type>,
}

struct Solution {
    slots: Vec<SlotSolution>,
}

#[derive(Debug, Clone)]
enum SlotSolution {
    Unknown,
    Resolved(Type),
    Conflicting { existing: Type, incoming: Type },
}

impl SlotSolution {
    fn is_settled(&self) -> bool {
        !matches!(self, Self::Unknown)
    }
}

struct TypeResolver<'a, 'solution> {
    graph: &'a TypeGraph<'a>,
    solution: &'solution Solution,
    resolving: HashSet<u32>,
    candidate_cache: HashMap<u32, Type>,
}
