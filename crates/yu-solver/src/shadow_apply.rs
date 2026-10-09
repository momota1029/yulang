//! Experimental value projection only; no source Apply typing or admission.
use crate::*;
use std::sync::Arc;
use yu_hir::HirErrorKind;
pub use crate::candidate_call::{CandidateSourceCall, OriginalGenCall0Input, PendingCallConstruction, PendingCallSupplier};

/// Every entry remains unresolved, including after successful structural solving.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnresolvedPremise {
    CandidatePureEffectModelUnresolved,
    CandidateOwnRowGeneralizationModelUnresolved,
    ApplicationTypingRule,
    CompleteInvocationImage,
    WholeArgumentProviderCompatibility,
    SourceTypingAndAdmission,
    RoleEntryAndProtection,
    WholeTupleScopeTransport,
    GeneralizationAndFreshUseCorrespondence,
    OriginalGenCall0MembershipSourceReferenceOnly,
    CompleteFunctionInterpretation,
    QIndependentCallViewFormation,
    EventOutputCorrespondence,
    ImmediateCallEffectPositionFormation,
    TypedOccurrenceIntroduction,
    FormalApplicability,
    DirectionalProtection,
    ModuleNameSourceTypingAndAdmission,
    ModuleUseReceivingExportCorrespondence,
}
pub const UNRESOLVED: &[UnresolvedPremise] = &[
    UnresolvedPremise::CandidatePureEffectModelUnresolved,
    UnresolvedPremise::CandidateOwnRowGeneralizationModelUnresolved,
    UnresolvedPremise::ApplicationTypingRule,
    UnresolvedPremise::CompleteInvocationImage,
    UnresolvedPremise::WholeArgumentProviderCompatibility,
    UnresolvedPremise::SourceTypingAndAdmission,
    UnresolvedPremise::RoleEntryAndProtection,
    UnresolvedPremise::WholeTupleScopeTransport,
    UnresolvedPremise::GeneralizationAndFreshUseCorrespondence,
    UnresolvedPremise::OriginalGenCall0MembershipSourceReferenceOnly,
    UnresolvedPremise::CompleteFunctionInterpretation,
    UnresolvedPremise::QIndependentCallViewFormation,
    UnresolvedPremise::EventOutputCorrespondence,
    UnresolvedPremise::ImmediateCallEffectPositionFormation,
    UnresolvedPremise::TypedOccurrenceIntroduction,
    UnresolvedPremise::FormalApplicability,
    UnresolvedPremise::DirectionalProtection,
    UnresolvedPremise::ModuleNameSourceTypingAndAdmission,
    UnresolvedPremise::ModuleUseReceivingExportCorrespondence,
];
/// Same actual returned provider/world/whole carrier/source incidence/original
/// shared scope/xi are all unresolved under WholeArgumentProviderCompatibility.
pub struct CandidateCall {
    pub occurrence: HirOccurrenceId,
    pub callee: HirOccurrenceId,
    pub argument: HirOccurrenceId,
    pub unresolved: &'static [UnresolvedPremise],
}
#[derive(Debug)]
pub enum CandidateError {
    Unsupported,
    Collection(CollectionAvailabilityError),
    Solve(SolveAvailabilityError),
}
/// Owns a private solver result which cannot be published as a SolvedModule.
/// Invocation/evaluation effects are intentionally absent from this API.
pub struct CandidateValueObservation {
    solved: SolvedModule,
    calls: Vec<CandidateCall>,
    definition_uses: Vec<CandidateDefinitionUse>,
    apply_recipe_occurrences: Vec<HirOccurrenceId>,
}
/// Private successor inference using retained value and effect variable graphs.
/// Complete Call, source admission and public scheme correspondence remain open.
pub struct CandidateInference {
    solved: SolvedModule,
}
impl CandidateInference {
    pub fn solve(hir: Arc<HirModule>) -> Result<Self, CandidateError> {
        let mut calls = Vec::new();
        let mut permitted_errors = HashSet::new();
        for item in hir.items() {
            if let HirItem::Binding(binding) = item {
                if let Some(source) = hir.local_source(binding.definition_root())
                    .map_err(|_| CandidateError::Unsupported)? {
                    crate::candidate_source::preflight(source)?;
                    crate::candidate_source::retain_placeholder_errors(binding.value(), &mut permitted_errors)?;
                    continue;
                }
                if let Some(local) = hir
                    .shadow_local_binding(binding.definition_root())
                    .map_err(|_| CandidateError::Unsupported)?
                {
                    preflight_local_binding(
                        &hir,
                        binding.value(),
                        local,
                        &mut calls,
                        &mut permitted_errors,
                    )?;
                    continue;
                }
            }
            let expr = match item {
                HirItem::Binding(binding) => binding.value(),
                HirItem::Expression(expr) if matches!(expr, ResolvedExpr::Integer { .. }) => expr,
                _ => return Err(CandidateError::Unsupported),
            };
            preflight_expression(expr, &mut calls, &mut permitted_errors)?;
        }
        if hir.errors().iter().any(|error| {
            !permitted_errors.contains(&error.id())
                || error.kind() != HirErrorKind::UnsupportedExpression
        }) {
            return Err(CandidateError::Unsupported);
        }
        let batch = ConstraintBatch::collect_candidate_mode(hir, true, true).map_err(CandidateError::Collection)?;
        let mut session = InferenceSession::try_new(batch).map_err(CandidateError::Solve)?;
        session
            .start_candidate_graph()
            .map_err(CandidateError::Solve)?;
        Ok(Self {
            solved: session.run().map_err(CandidateError::Solve)?,
        })
    }
    pub fn observes_hir(&self, hir: &HirModule) -> bool {
        std::ptr::eq(self.solved.hir.as_ref(), hir)
    }
    /// Candidate conflicts never establish source rejection.
    pub fn candidate_conflicts(&self) -> &[SolverError] {
        self.solved.errors()
    }
    pub fn export(
        &self,
        root: &DefinitionRootId,
    ) -> Result<CandidateGraphExport<'_>, ArtifactMismatch> {
        if !self.solved.hir.owns_definition_root(root) {
            return Err(ArtifactMismatch);
        }
        let position = self
            .solved
            .root_scheme_positions
            .get(root)
            .ok_or(ArtifactMismatch)?;
        let state = self
            .solved
            .candidate_graph
            .as_ref()
            .ok_or(ArtifactMismatch)?;
        let graph = state.graphs[*position].as_ref().ok_or(ArtifactMismatch)?;
        Ok(CandidateGraphExport { state, graph })
    }
    pub fn fresh_use(&self, occurrence: &HirOccurrenceId) -> Option<CandidateGraphFreshUse<'_>> {
        if !self.solved.hir.owns_occurrence(occurrence) {
            return None;
        }
        let state = self.solved.candidate_graph.as_ref()?;
        if let Some(route) = state.local_routes.iter().find(|route| &route.occurrence == occurrence) {
            let scheme = state.locals.get(route.slot)?.as_ref()?;
            if scheme.id != route.local { return None; }
            return Some(CandidateGraphFreshUse {
                state, occurrence: &route.occurrence, rows: &route.rows, graph: &route.graph,
            });
        }
        let route = state.routes.iter().find(|route| route.use_id.occurrence() == occurrence)?;
        Some(CandidateGraphFreshUse {
            state,
            occurrence: route.use_id.occurrence(),
            rows: &route.rows,
            graph: &route.graph,
        })
    }
    /// Indexed observations retain one pending construction request per source Call.
    pub fn source_call_count(&self) -> usize { self.solved.candidate_calls.calls.len() }
    pub fn source_call(&self, index: usize) -> Result<CandidateSourceCall<'_>, ArtifactMismatch> {
        crate::candidate_call::observe(&self.solved, index)
    }
    pub fn unresolved(&self) -> &'static [UnresolvedPremise] {
        UNRESOLVED
    }
}
/// Exact immutable leaf of the private retained graph.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateGraphLeaf {
    Bottom,
    Top,
    NegativeBottom,
    IntPositive,
    IntNegative,
    EffectBottom,
    EmptyEffect,
}
pub struct CandidateGraphExport<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    graph: &'a crate::candidate_scheme::Graph,
}
impl<'a> CandidateGraphExport<'a> {
    pub fn root(&self) -> CandidateGraphNode<'a> {
        CandidateGraphNode {
            state: self.state,
            graph: self.graph,
            index: self.graph.root,
        }
    }
    pub fn node_count(&self) -> usize {
        self.graph.nodes.len()
    }
    pub fn rows(&self) -> impl Iterator<Item = CandidateGraphRow<'a>> + 'a {
        let state = self.state;
        let graph = self.graph;
        (0..graph.rows.len()).map(move |index| CandidateGraphRow { state, graph, index })
    }
    pub fn bounds(&self) -> impl Iterator<Item = CandidateGraphBound<'a>> + 'a {
        let state = self.state;
        let graph = self.graph;
        graph
            .bounds
            .iter()
            .map(move |bound| CandidateGraphBound { state, graph, bound })
    }
    pub fn unresolved(&self) -> &'static [UnresolvedPremise] {
        UNRESOLVED
    }
}
#[derive(Clone, Copy)]
pub struct CandidateGraphNode<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    graph: &'a crate::candidate_scheme::Graph,
    index: usize,
}
impl<'a> CandidateGraphNode<'a> {
    pub fn same_identity(self, other: Self) -> bool {
        std::ptr::eq(self.graph, other.graph) && self.index == other.index
    }
    pub fn leaf(self) -> Option<CandidateGraphLeaf> {
        use crate::candidate_scheme::{Atom, Node};
        Some(match self.graph.nodes[self.index] {
            Node::Leaf(atom) => match atom {
                Atom::Bottom => CandidateGraphLeaf::Bottom,
                Atom::Top => CandidateGraphLeaf::Top,
                Atom::NegativeBottom => CandidateGraphLeaf::NegativeBottom,
                Atom::IntPositive => CandidateGraphLeaf::IntPositive,
                Atom::IntNegative => CandidateGraphLeaf::IntNegative,
                Atom::EffectBottom => CandidateGraphLeaf::EffectBottom,
                Atom::EmptyEffect => CandidateGraphLeaf::EmptyEffect,
            },
            _ => return None,
        })
    }
    pub fn polarity(self) -> Polarity {
        use crate::candidate_scheme::{Atom, Node};
        match self.graph.nodes[self.index] {
            Node::Row { polarity, .. } | Node::Function { polarity, .. } => polarity,
            Node::Leaf(Atom::Bottom | Atom::IntPositive | Atom::EffectBottom) => Polarity::Positive,
            Node::Leaf(_) => Polarity::Negative,
        }
    }
    pub fn children(self) -> Option<[Self; 4]> {
        match self.graph.nodes[self.index] {
            crate::candidate_scheme::Node::Function { children, .. } => {
                Some(children.map(|index| Self {
                    state: self.state,
                    graph: self.graph,
                    index,
                }))
            }
            _ => None,
        }
    }
    pub fn row(self) -> Option<CandidateGraphRow<'a>> {
        match self.graph.nodes[self.index] {
            crate::candidate_scheme::Node::Row { row, .. } => Some(CandidateGraphRow {
                state: self.state,
                graph: self.graph,
                index: row,
            }),
            _ => None,
        }
    }
}
#[derive(Clone, Copy)]
pub struct CandidateGraphRow<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    graph: &'a crate::candidate_scheme::Graph,
    index: usize,
}
impl CandidateGraphRow<'_> {
    pub fn kind(self) -> ComponentKind {
        self.graph.rows[self.index].key.kind()
    }
    pub fn is_local(self) -> bool {
        self.graph.rows[self.index].local
    }
    pub fn same_identity(self, other: Self) -> bool {
        std::ptr::eq(self.state, other.state)
            && self.state.intrusion.rep(self.graph.rows[self.index].key)
                == other.state.intrusion.rep(other.graph.rows[other.index].key)
    }
}
pub struct CandidateGraphBound<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    graph: &'a crate::candidate_scheme::Graph,
    bound: &'a crate::candidate_scheme::Bound,
}
impl<'a> CandidateGraphBound<'a> {
    pub fn kind(&self) -> ComponentKind {
        self.bound.kind
    }
    pub fn lower(&self) -> CandidateGraphNode<'a> {
        CandidateGraphNode {
            state: self.state,
            graph: self.graph,
            index: self.bound.lower,
        }
    }
    pub fn upper(&self) -> CandidateGraphNode<'a> {
        CandidateGraphNode {
            state: self.state,
            graph: self.graph,
            index: self.bound.upper,
        }
    }
}
pub struct CandidateGraphFreshUse<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    occurrence: &'a HirOccurrenceId,
    rows: &'a [crate::candidate_scheme::RowKey],
    graph: &'a crate::candidate_scheme::Graph,
}
impl<'a> CandidateGraphFreshUse<'a> {
    pub fn occurrence(&self) -> &'a HirOccurrenceId {
        self.occurrence
    }
    pub fn rows(&self) -> impl Iterator<Item = CandidateGraphFreshRow<'a>> + 'a {
        let state = self.state;
        let rows = self.rows;
        let graph = self.graph;
        (0..rows.len()).map(move |index| CandidateGraphFreshRow {
            state,
            rows,
            graph,
            index,
        })
    }
    pub fn unresolved(&self) -> &'static [UnresolvedPremise] {
        UNRESOLVED
    }
}
pub struct CandidateGraphFreshRow<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    rows: &'a [crate::candidate_scheme::RowKey],
    graph: &'a crate::candidate_scheme::Graph,
    index: usize,
}
impl<'a> CandidateGraphFreshRow<'a> {
    pub fn source_row(&self) -> CandidateGraphRow<'a> {
        CandidateGraphRow {
            state: self.state,
            graph: self.graph,
            index: self.index,
        }
    }
    pub fn kind(&self) -> ComponentKind {
        self.rows[self.index].kind()
    }
    pub fn same_identity(&self, other: &Self) -> bool {
        std::ptr::eq(self.state, other.state)
            && self.state.intrusion.rep(self.rows[self.index]) == other.state.intrusion.rep(other.rows[other.index])
    }
}
/// Borrowed retained candidate solver relation only. All semantic premises
/// remain unresolved; this does not establish source typing or admission.
#[derive(Clone, Copy)]
pub struct CandidateApplyFactObservation<'a> {
    edge: &'a ProvenanceEdge,
    fact: &'a SemanticFact,
    call: &'a CandidateCall,
}
impl<'a> CandidateApplyFactObservation<'a> {
    pub fn edge(self) -> &'a ProvenanceEdge {
        self.edge
    }
    pub fn fact(self) -> &'a SemanticFact {
        self.fact
    }
    pub fn unresolved(self) -> &'static [UnresolvedPremise] {
        self.call.unresolved
    }
}
pub struct CandidateExport<'a> {
    pub unresolved: &'static [UnresolvedPremise],
    pub value: SolvedValue,
    scheme: crate::shadow_f5::ClosedSchemeRef<'a>,
}
impl<'a> CandidateExport<'a> {
    /// Exact borrowed scheme behind this candidate value observation.
    pub fn scheme(&self) -> crate::shadow_f5::ClosedSchemeRef<'a> {
        self.scheme
    }
    /// Whole four-port observation under the named unresolved effect model.
    pub fn endpoints(&self) -> yu_types::ClosedValueSchemeView<'_> {
        self.scheme.endpoints()
    }
}
/// Collection-owned identity retained before the batch is consumed.
struct CandidateDefinitionUse {
    record: DefinitionUse,
    target_root: DefinitionRootId,
    receiving_root: DefinitionRootId,
}

/// Borrowed current module Name use. No source typing or export transport follows.
#[derive(Clone, Copy)]
pub struct CandidateDefinitionUseRef<'a> {
    observation: &'a CandidateValueObservation,
    retained: &'a CandidateDefinitionUse,
    target: crate::shadow_f5::ClosedSchemeRef<'a>,
    receiving: crate::shadow_f5::ClosedSchemeRef<'a>,
}
impl<'a> CandidateDefinitionUseRef<'a> {
    pub fn occurrence(self) -> &'a HirOccurrenceId {
        self.retained.record.id().occurrence()
    }
    pub fn same_identity(self, other: Self) -> bool {
        self.retained.record.id() == other.retained.record.id()
    }
    pub fn target_scheme(self) -> crate::shadow_f5::ClosedSchemeRef<'a> {
        self.target
    }
    pub fn receiving_scheme(self) -> crate::shadow_f5::ClosedSchemeRef<'a> {
        self.receiving
    }
    /// Actual receiving-root candidate observation from this same solve.
    /// This does not establish semantic source typing or export transport.
    pub fn receiving_export(self) -> Result<CandidateExport<'a>, ArtifactMismatch> {
        self.observation.export(&self.retained.receiving_root)
    }
    pub fn fresh_instantiation(self) -> crate::shadow_f5::FreshCaptureState<'a> {
        self.target.fresh_capture(
            self.retained.record.id(),
            self.retained.record.target(),
            true,
        )
    }
    /// Exact retained store causes; an empty inventory supplies no invented fact.
    pub fn provenance_causes(self) -> impl Iterator<Item = &'a CauseId> + 'a {
        self.observation
            .solved
            .store
            .provenance()
            .iter()
            .map(|edge| edge.cause())
            .filter(move |cause| cause.occurrence().occurrence() == self.occurrence())
    }
    pub fn unresolved(self) -> &'static [UnresolvedPremise] {
        UNRESOLVED
    }
}
/// Historical row identity within this candidate's ordinary use substitution.
pub struct CandidateFreshRow<'a> {
    capture: &'a ShadowFreshCapture,
    use_id: &'a DefinitionUseId,
    row: u32,
    binder: crate::shadow_f5::FreshBinderRef<'a>,
}
impl<'a> CandidateFreshRow<'a> {
    pub fn source_binder(&self) -> crate::shadow_f5::FreshBinderRef<'a> {
        self.binder
    }
    pub fn source_use(&self) -> &HirOccurrenceId {
        self.use_id.occurrence()
    }
    pub fn same_identity(&self, other: &Self) -> bool {
        std::ptr::eq(self.capture, other.capture) && self.row == other.row
    }
}
impl CandidateValueObservation {
    pub fn solve(hir: Arc<HirModule>) -> Result<Self, CandidateError> {
        let mut calls = Vec::new();
        let mut permitted_errors = HashSet::new();
        // Preflight bounds recursive emission without consuming the native stack.
        // Only retained HIR shapes are admitted; no CST reconstruction occurs.
        for item in hir.items() {
            if let HirItem::Binding(binding) = item {
                if let Some(local) = hir
                    .shadow_local_binding(binding.definition_root())
                    .map_err(|_| CandidateError::Unsupported)?
                {
                    preflight_local_binding(
                        &hir,
                        binding.value(),
                        local,
                        &mut calls,
                        &mut permitted_errors,
                    )?;
                    continue;
                }
            }
            let expr = match item {
                HirItem::Binding(b) => b.value(),
                HirItem::Expression(e) if matches!(e, ResolvedExpr::Integer { .. }) => e,
                _ => return Err(CandidateError::Unsupported),
            };
            preflight_expression(expr, &mut calls, &mut permitted_errors)?;
        }
        if hir.errors().iter().any(|e| {
            !permitted_errors.contains(&e.id()) || e.kind() != HirErrorKind::UnsupportedExpression
        }) {
            return Err(CandidateError::Unsupported);
        }
        let batch = ConstraintBatch::collect_mode(hir, true).map_err(CandidateError::Collection)?;
        if batch
            .scc_plan()
            .components_in_dependency_first_order()
            .any(|c| {
                !batch
                    .scc_plan()
                    .internal_uses(c)
                    .expect("owned SCC")
                    .is_empty()
            })
        {
            return Err(CandidateError::Unsupported);
        }
        let definition_uses = batch
            .definition_uses()
            .iter()
            .map(|record| CandidateDefinitionUse {
                record: record.clone(),
                target_root: batch.definitions[record.target().ordinal() as usize]
                    .root
                    .clone(),
                receiving_root: batch.definitions[record.parent().ordinal() as usize]
                    .root
                    .clone(),
            })
            .collect();
        // Slot zero also belongs to Group recipes; retain the relation kind
        // before consuming the batch rather than inferring it from store terms.
        let apply_recipe_occurrences = batch
            .candidate_recipes
            .iter()
            .filter(|recipe| matches!(recipe.relation, CandidateRelation::Apply { .. }))
            .map(|recipe| recipe.occurrence.clone())
            .collect();
        let solved =
            SolvedModule::solve_with_shadow_fresh_capture(batch).map_err(CandidateError::Solve)?;
        Ok(Self {
            solved,
            calls,
            definition_uses,
            apply_recipe_occurrences,
        })
    }
    /// Tests the exact retained HIR instance even when it has no module uses.
    pub fn observes_hir(&self, hir: &HirModule) -> bool {
        std::ptr::eq(self.solved.hir.as_ref(), hir)
    }
    /// Borrows the retained startup row for this candidate's exact HIR parameter.
    /// `FreshRowRef::same_identity` compares it with retained generalization
    /// origins without assigning source meaning or successor ownership.
    pub fn parameter_row(
        &self,
        parameter: &HirParameterId,
    ) -> Result<crate::shadow_f5::ParameterRowState<'_>, yu_hir::shadow::SourceIdentityError> {
        self.solved.shadow_parameter_row(parameter)
    }
    /// Ordinary incoming source-use substitution; aliases receive one route,
    /// with no second candidate-specific freshening.
    pub fn fresh_rows(&self, occurrence: &HirOccurrenceId) -> Option<Vec<CandidateFreshRow<'_>>> {
        let use_observation = self.definition_use(occurrence)?;
        let crate::shadow_f5::FreshCaptureState::Captured(instantiation) =
            use_observation.fresh_instantiation()
        else {
            return None;
        };
        let capture = self.solved.shadow_fresh_capture.as_ref()?;
        let route = &capture.routes[*capture
            .positions
            .get(use_observation.retained.record.id())?];
        Some(
            route
                .rows
                .iter()
                .zip(instantiation.bindings())
                .map(|((_, _, row), (binder, _))| CandidateFreshRow {
                    capture,
                    use_id: &route.use_id,
                    row: *row,
                    binder,
                })
                .collect(),
        )
    }
    /// Non-module occurrences have no definition use; capture availability is a
    /// separate state on a validated module use, including zero-binder routes.
    pub fn definition_use(
        &self,
        occurrence: &HirOccurrenceId,
    ) -> Option<CandidateDefinitionUseRef<'_>> {
        let retained = self
            .definition_uses
            .iter()
            .find(|u| u.record.occurrence() == occurrence)?;
        if retained.record.id() != retained.record.cause().id()
            || retained.record.id().occurrence() != retained.record.occurrence()
            || !self.solved.hir.owns_occurrence(occurrence)
        {
            return None;
        }
        let schemes = self.solved.shadow_closed_schemes();
        Some(CandidateDefinitionUseRef {
            observation: self,
            retained,
            target: schemes.for_root(&retained.target_root).ok()?,
            receiving: schemes.for_root(&retained.receiving_root).ok()?,
        })
    }
    pub fn definition_uses(&self) -> impl Iterator<Item = CandidateDefinitionUseRef<'_>> {
        self.definition_uses
            .iter()
            .filter_map(|u| self.definition_use(u.record.occurrence()))
    }
    pub fn calls(&self) -> &[CandidateCall] {
        &self.calls
    }
    /// Observes only an exact retained call from this solve and its Apply recipe.
    /// Missing or ambiguous provenance/facts fail closed. This borrowed solver
    /// relation leaves every call premise unresolved and performs no solving.
    pub fn apply_fact(&self, call: &CandidateCall) -> Option<CandidateApplyFactObservation<'_>> {
        let mut calls = self.calls.iter().filter(|owned| std::ptr::eq(*owned, call));
        let call = calls.next()?;
        if calls.next().is_some()
            || self
                .apply_recipe_occurrences
                .iter()
                .filter(|occurrence| *occurrence == &call.occurrence)
                .count()
                != 1
        {
            return None;
        }
        let mut edges = self.solved.store.provenance().iter().filter(|edge| {
            edge.cause().occurrence().occurrence() == &call.occurrence
                && edge.cause().occurrence().local_slot() == 0
        });
        let edge = edges.next()?;
        if edges.next().is_some() {
            return None;
        }
        let mut facts = self
            .solved
            .store
            .facts()
            .iter()
            .filter(|fact| fact.id() == edge.fact());
        let fact = facts.next()?;
        if facts.next().is_some() {
            return None;
        }
        Some(CandidateApplyFactObservation { edge, fact, call })
    }
    /// Candidate conflicts never establish source rejection.
    pub fn candidate_conflicts(&self) -> &[SolverError] {
        self.solved.errors()
    }
    pub fn export(&self, root: &DefinitionRootId) -> Result<CandidateExport<'_>, ArtifactMismatch> {
        Ok(CandidateExport {
            unresolved: UNRESOLVED,
            value: self.solved.root_value_for(root)?,
            scheme: self.solved.shadow_closed_schemes().for_root(root)?,
        })
    }
}
// The HIR owner already restricted this carrier to the approved source fixture.
// Validate its lexical incidences before allocating any candidate solver state.
fn preflight_local_binding(
    hir: &HirModule,
    expr: &ResolvedExpr,
    local: &yu_hir::shadow::ShadowLocalBind,
    calls: &mut Vec<CandidateCall>,
    permitted_errors: &mut HashSet<yu_hir::HirErrorId>,
) -> Result<(), CandidateError> {
    let ResolvedExpr::Lambda {
        parameter: outer,
        body: placeholder,
        ..
    } = expr
    else {
        return Err(CandidateError::Unsupported);
    };
    let ResolvedExpr::Error {
        errors: placeholder_errors,
        ..
    } = placeholder.as_ref()
    else {
        return Err(CandidateError::Unsupported);
    };
    let ResolvedExpr::Lambda {
        parameter: inner,
        body,
        ..
    } = &local.initializer
    else {
        return Err(CandidateError::Unsupported);
    };
    let ResolvedExpr::Apply {
        occurrence,
        callee,
        argument,
        errors,
        ..
    } = body.as_ref()
    else {
        return Err(CandidateError::Unsupported);
    };
    if outer == inner
        || local.captures.as_ref() != std::slice::from_ref(outer)
        || local.continuation.local != local.local
        || hir
            .shadow_parameter_local_owner(inner)
            .map_err(|_| CandidateError::Unsupported)?
            != Some(&local.local)
        || !matches!(callee.as_ref(), ResolvedExpr::Name { resolution: NameResolution::Parameter(p), .. } if p == outer)
        || !matches!(argument.as_ref(), ResolvedExpr::Name { resolution: NameResolution::Parameter(p), .. } if p == inner)
        || errors != placeholder_errors
    {
        return Err(CandidateError::Unsupported);
    }
    permitted_errors
        .try_reserve(errors.len())
        .map_err(|_| CandidateError::Unsupported)?;
    permitted_errors.extend(errors.iter().copied());
    calls
        .try_reserve(1)
        .map_err(|_| CandidateError::Unsupported)?;
    calls.push(CandidateCall {
        occurrence: occurrence.clone(),
        callee: callee.occurrence().clone(),
        argument: argument.occurrence().clone(),
        unresolved: UNRESOLVED,
    });
    Ok(())
}
fn preflight_expression(
    expr: &ResolvedExpr,
    calls: &mut Vec<CandidateCall>,
    permitted_errors: &mut HashSet<yu_hir::HirErrorId>,
) -> Result<(), CandidateError> {
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| CandidateError::Unsupported)?;
    pending.push((Some(expr), 1usize));
    let mut formals = Vec::new();
    while let Some((expr, depth)) = pending.pop() {
        let Some(expr) = expr else {
            formals.pop();
            continue;
        };
        if depth > 128 {
            return Err(CandidateError::Unsupported);
        }
        pending
            .try_reserve(2)
            .map_err(|_| CandidateError::Unsupported)?;
        match expr {
            ResolvedExpr::Integer { .. }
            | ResolvedExpr::Name {
                resolution: NameResolution::Resolved(_),
                ..
            } => {}
            ResolvedExpr::Name {
                resolution: NameResolution::Parameter(p),
                ..
            } if formals.contains(&p) => {}
            ResolvedExpr::Group { inner, .. } => pending.push((Some(inner), depth + 1)),
            ResolvedExpr::Apply {
                occurrence,
                callee,
                argument,
                errors,
                ..
            } => {
                permitted_errors
                    .try_reserve(errors.len())
                    .map_err(|_| CandidateError::Unsupported)?;
                permitted_errors.extend(errors.iter().copied());
                calls
                    .try_reserve(1)
                    .map_err(|_| CandidateError::Unsupported)?;
                calls.push(CandidateCall {
                    occurrence: occurrence.clone(),
                    callee: callee.occurrence().clone(),
                    argument: argument.occurrence().clone(),
                    unresolved: UNRESOLVED,
                });
                pending.push((Some(argument), depth + 1));
                pending.push((Some(callee), depth + 1));
            }
            ResolvedExpr::Lambda {
                parameter, body, ..
            } => {
                formals
                    .try_reserve(1)
                    .map_err(|_| CandidateError::Unsupported)?;
                formals.push(parameter);
                pending.push((None, depth));
                pending.push((Some(body.as_ref()), depth + 1));
            }
            _ => return Err(CandidateError::Unsupported),
        }
    }
    Ok(())
}

pub(super) type CandidateEndpoint = LambdaValueEndpoint;
#[derive(Clone, Debug)]
pub(super) enum CandidateRelation {
    Group {
        child: CandidateEndpoint,
        child_effect: usize,
        result: usize,
        result_effect: usize,
    },
    Apply {
        callee: CandidateEndpoint,
        callee_effect: usize,
        argument: CandidateEndpoint,
        argument_effect: usize,
        result: usize,
        result_effect: usize,
    },
}
#[derive(Clone, Debug)]
pub(super) struct CandidateConstraintRecipe {
    pub(super) occurrence: HirOccurrenceId,
    pub(super) relation: CandidateRelation,
    pub(super) after_collected_fact: usize,
    pub(super) source_input: Option<usize>,
}
impl ConstraintBatch {
    pub(super) fn emit_candidate_local_value<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        local: &'a yu_hir::shadow::ShadowLocalBind,
        root: &DefinitionRootId,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<(), CollectionAvailabilityError> {
        let unsupported = || CollectionAvailabilityError::MissingDefinitionEndpoint;
        let ResolvedExpr::Lambda {
            occurrence: outer_occurrence,
            parameter: outer,
            ..
        } = expr
        else {
            return Err(unsupported());
        };
        let ResolvedExpr::Lambda {
            occurrence: inner_occurrence,
            parameter: inner,
            body,
            ..
        } = &local.initializer
        else {
            return Err(unsupported());
        };
        let ResolvedExpr::Apply {
            occurrence,
            callee,
            argument,
            ..
        } = body.as_ref()
        else {
            return Err(unsupported());
        };
        self.parameter_recipes
            .try_reserve(2)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        let outer_position = self.parameter_recipes.len();
        self.parameter_recipes.push(outer.clone());
        let inner_position = self.parameter_recipes.len();
        self.parameter_recipes.push(inner.clone());
        // The capture is the actual outer row, not a fresh local Name use.
        let mut formals = Vec::new();
        formals
            .try_reserve(2)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        formals.push(outer_position);
        formals.push(inner_position);
        let (callee, callee_effect) =
            self.emit_candidate_expression(callee, &mut formals, parent, uses)?;
        let (argument, argument_effect) =
            self.emit_candidate_expression(argument, &mut formals, parent, uses)?;
        let call = self.candidate_component(occurrence)?;
        self.retain_candidate_relation(
            occurrence,
            CandidateRelation::Apply {
                callee,
                callee_effect,
                argument,
                argument_effect,
                result: call.value,
                result_effect: call.effect,
            },
        )?;
        self.occurrence_component(inner_occurrence.clone(), ComponentKind::Value)?;
        self.occurrence_component(inner_occurrence.clone(), ComponentKind::Effect)?;
        let inner_value = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
        };
        self.occurrence_component_positions
            .insert(inner_occurrence.clone(), inner_value);
        self.candidate_local_lambda_effect(inner_occurrence, inner_value.effect)?;
        self.retain_candidate_local_lambda(
            inner_occurrence,
            inner_position,
            inner_value.value,
            call.value,
            call.effect,
            inner_value.effect,
        )?;
        // The terminal local reference reuses its initializer's endpoint,
        // just as a formal reference reuses its row. No proxy bound, call,
        // local generalization or freshening is introduced by returning it.
        self.occurrence_component(outer_occurrence.clone(), ComponentKind::Effect)?;
        let outer_effect = self.components.len() - 1;
        self.candidate_local_lambda_effect(outer_occurrence, outer_effect)?;
        self.retain_candidate_local_lambda(
            outer_occurrence,
            outer_position,
            self.root_component_positions[root].component,
            inner_value.value,
            inner_value.effect,
            outer_effect,
        )
    }
    pub(super) fn candidate_local_lambda_effect(
        &mut self,
        occurrence: &HirOccurrenceId,
        position: usize,
    ) -> Result<(), CollectionAvailabilityError> {
        let effect = self.component_term_at(position);
        let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
        let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
        self.emit(occurrence.clone(), 0, bottom, effect)?;
        self.emit(occurrence.clone(), 1, effect, empty)
    }
    pub(super) fn retain_candidate_local_lambda(
        &mut self,
        occurrence: &HirOccurrenceId,
        parameter_position: usize,
        root_component: usize,
        body_value_component: usize,
        body_effect_component: usize,
        lambda_effect_component: usize,
    ) -> Result<(), CollectionAvailabilityError> {
        self.lambda_recipes
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.lambda_recipes.push(LambdaRecipe {
            occurrence: occurrence.clone(),
            parameter_position,
            root_component,
            body_value_endpoint: LambdaValueEndpoint::Component(body_value_component),
            body_effect_component,
            lambda_effect_component,
            after_collected_fact: self.occurrences.len(),
        });
        self.counters.emitted_facts = self
            .counters
            .emitted_facts
            .checked_add(1)
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.counters.generated_work_items = self
            .counters
            .generated_work_items
            .checked_add(1)
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        Ok(())
    }
    pub(super) fn candidate_component(
        &mut self,
        occurrence: &HirOccurrenceId,
    ) -> Result<ComponentPositions, CollectionAvailabilityError> {
        self.occurrence_component(occurrence.clone(), ComponentKind::Value)?;
        self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
        let positions = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
        };
        self.occurrence_component_positions
            .insert(occurrence.clone(), positions);
        if !self.candidate_graph_effects {
            self.candidate_pure_effect(occurrence, positions.effect)?;
        }
        Ok(positions)
    }
    fn candidate_pure_effect(
        &mut self,
        occurrence: &HirOccurrenceId,
        position: usize,
    ) -> Result<(), CollectionAvailabilityError> {
        // These bounds belong only to CandidatePureEffectModelUnresolved.
        let effect = self.component_term_at(position);
        let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
        let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
        self.emit(occurrence.clone(), 1, bottom, effect)?;
        self.emit(occurrence.clone(), 2, effect, empty)
    }
    pub(super) fn retain_candidate_relation(
        &mut self,
        occurrence: &HirOccurrenceId,
        relation: CandidateRelation,
    ) -> Result<(), CollectionAvailabilityError> {
        self.candidate_recipes
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        let fact_count = if self.candidate_graph_effects {
            match &relation {
                CandidateRelation::Group { .. } => 2,
                CandidateRelation::Apply { .. } => 3,
            }
        } else {
            1
        };
        self.counters.emitted_facts = self
            .counters
            .emitted_facts
            .checked_add(fact_count)
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.counters.generated_work_items = self
            .counters
            .generated_work_items
            .checked_add(fact_count)
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.candidate_recipes.push(CandidateConstraintRecipe {
            occurrence: occurrence.clone(),
            relation,
            after_collected_fact: self.occurrences.len(),
            source_input: None,
        });
        Ok(())
    }
    pub(super) fn emit_candidate_value<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        root: Option<&DefinitionRootId>,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<(), CollectionAvailabilityError> {
        let mut formals = Vec::new();
        if matches!(expr, ResolvedExpr::Lambda { .. }) {
            let root = root.ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?;
            self.emit_candidate_lambda(
                expr,
                self.root_component_positions[root].component,
                &mut formals,
                parent,
                uses,
            )?;
        } else {
            let (value, _) = self.emit_candidate_expression(expr, &mut formals, parent, uses)?;
            if let Some(root) = root {
                let CandidateEndpoint::Component(position) = value else {
                    return Err(CollectionAvailabilityError::MissingDefinitionEndpoint);
                };
                let component = self.root_value_component_for_collect(root)?;
                self.emit(
                    expr.occurrence().clone(),
                    10,
                    self.component_term_at(position),
                    self.term_for_component(&component),
                )?;
            }
        }
        Ok(())
    }
    fn emit_candidate_lambda<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        value_component: usize,
        formals: &mut Vec<usize>,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<usize, CollectionAvailabilityError> {
        let ResolvedExpr::Lambda {
            occurrence,
            parameter,
            body,
            ..
        } = expr
        else {
            return Err(CollectionAvailabilityError::MissingDefinitionEndpoint);
        };
        self.parameter_recipes
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        formals
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        let parameter_position = self.parameter_recipes.len();
        self.parameter_recipes.push(parameter.clone());
        formals.push(parameter_position);
        let body_result = self.emit_candidate_expression(body, formals, parent, uses);
        formals.pop();
        let (value, effect) = body_result?;
        self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
        let lambda_effect_component = self.components.len() - 1;
        self.candidate_local_lambda_effect(occurrence, lambda_effect_component)?;
        self.lambda_recipes
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.lambda_recipes.push(LambdaRecipe {
            occurrence: occurrence.clone(),
            parameter_position,
            root_component: value_component,
            body_value_endpoint: value,
            body_effect_component: effect,
            lambda_effect_component,
            after_collected_fact: self.occurrences.len(),
        });
        self.counters.emitted_facts = self
            .counters
            .emitted_facts
            .checked_add(1)
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.counters.generated_work_items = self
            .counters
            .generated_work_items
            .checked_add(1)
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        Ok(lambda_effect_component)
    }
    fn emit_candidate_expression<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        formals: &mut Vec<usize>,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<(CandidateEndpoint, usize), CollectionAvailabilityError> {
        let occurrence = expr.occurrence();
        let positions = match expr {
            ResolvedExpr::Integer { .. } => {
                self.emit_integer(occurrence.clone(), None)?;
                self.occurrence_component_positions[occurrence]
            }
            ResolvedExpr::Name {
                resolution: NameResolution::Resolved(target),
                ..
            } => {
                self.emit_resolved_binding_name(occurrence.clone(), None)?;
                let old_capacity = uses.capacity();
                uses.try_reserve(1)
                    .map_err(|_| CollectionAvailabilityError::DefinitionUseIdentityExhausted)?;
                uses.push(PendingDefinitionUse {
                    parent_ordinal: parent
                        .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?
                        .ordinal(),
                    target,
                    occurrence: occurrence.clone(),
                });
                self.counters
                    .definition_use_endpoint_workspace_peak_capacity = self
                    .counters
                    .definition_use_endpoint_workspace_peak_capacity
                    .max(uses.capacity());
                if uses.capacity() != old_capacity {
                    self.counters
                        .definition_use_endpoint_workspace_capacity_growths += 1;
                }
                self.occurrence_component_positions[occurrence]
            }
            ResolvedExpr::Name {
                resolution: NameResolution::Parameter(parameter),
                ..
            } => {
                let position = formals
                    .iter()
                    .rev()
                    .copied()
                    .find(|p| &self.parameter_recipes[*p] == parameter)
                    .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?;
                self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
                let effect = self.components.len() - 1;
                let term = self.component_term_at(effect);
                let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                self.emit(occurrence.clone(), 0, bottom, term)?;
                self.emit(occurrence.clone(), 1, term, empty)?;
                return Ok((CandidateEndpoint::Parameter(position), effect));
            }
            ResolvedExpr::Lambda { .. } => {
                self.occurrence_component(occurrence.clone(), ComponentKind::Value)?;
                let value = self.components.len() - 1;
                let effect = self.emit_candidate_lambda(expr, value, formals, parent, uses)?;
                let positions = ComponentPositions { value, effect };
                self.occurrence_component_positions
                    .insert(occurrence.clone(), positions);
                positions
            }
            ResolvedExpr::Group { inner, .. } => {
                let (child, child_effect) =
                    self.emit_candidate_expression(inner, formals, parent, uses)?;
                let positions = self.candidate_component(occurrence)?;
                self.retain_candidate_relation(
                    occurrence,
                    CandidateRelation::Group {
                        child,
                        child_effect,
                        result: positions.value,
                        result_effect: positions.effect,
                    },
                )?;
                positions
            }
            ResolvedExpr::Apply {
                callee, argument, ..
            } => {
                let (callee, callee_effect) =
                    self.emit_candidate_expression(callee, formals, parent, uses)?;
                let (argument, argument_effect) =
                    self.emit_candidate_expression(argument, formals, parent, uses)?;
                let positions = self.candidate_component(occurrence)?;
                self.retain_candidate_relation(
                    occurrence,
                    CandidateRelation::Apply {
                        callee,
                        callee_effect,
                        argument,
                        argument_effect,
                        result: positions.value,
                        result_effect: positions.effect,
                    },
                )?;
                positions
            }
            _ => return Err(CollectionAvailabilityError::MissingDefinitionEndpoint),
        };
        Ok((
            CandidateEndpoint::Component(positions.value),
            positions.effect,
        ))
    }
}
impl InferenceSession {
    pub(super) fn candidate_endpoint(
        &mut self,
        endpoint: CandidateEndpoint,
        polarity: Polarity,
    ) -> Result<Term, SolveAvailabilityError> {
        let row = match endpoint {
            CandidateEndpoint::Component(position) => self.live_components[position].ordinal,
            CandidateEndpoint::Parameter(position) => self
                .parameter_live_base
                .checked_add(
                    u32::try_from(position)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                )
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        };
        self.live_value_term(polarity, row)
    }
    pub(super) fn admit_candidate_fact(
        &mut self,
        recipe: &CandidateConstraintRecipe,
    ) -> Result<(), SolveAvailabilityError> {
        if let Some(source_input) = recipe.source_input {
            let input = self.batch.candidate_calls.calls.get(source_input)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let registered_recipe = self.batch.candidate_recipes.get(input.recipe)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let CandidateRelation::Apply {
                callee, callee_effect, argument, argument_effect, result, result_effect,
            } = recipe.relation else { return Err(SolveAvailabilityError::IdentityExhausted); };
            if registered_recipe.source_input != Some(source_input)
                || registered_recipe.occurrence != recipe.occurrence
                || input.checking.occurrence() != &recipe.occurrence
                || !crate::candidate_call::same_endpoint(input.callee_value, callee)
                || !crate::candidate_call::same_endpoint(input.argument_value, argument)
                || input.callee_effect != callee_effect || input.argument_effect != argument_effect
                || input.result != result || input.application_effect != result_effect
            { return Err(SolveAvailabilityError::IdentityExhausted); }
        }
        let mut invocation_effect = None;
        let (lower, upper) = match recipe.relation {
            CandidateRelation::Group { child, result, .. } => (
                self.candidate_endpoint(child, Polarity::Positive)?,
                self.candidate_endpoint(CandidateEndpoint::Component(result), Polarity::Negative)?,
            ),
            CandidateRelation::Apply {
                callee,
                argument,
                argument_effect,
                result,
                result_effect,
                ..
            } => {
                let callee = self.candidate_endpoint(callee, Polarity::Positive)?;
                let argument = self.candidate_endpoint(argument, Polarity::Positive)?;
                let result = self
                    .candidate_endpoint(CandidateEndpoint::Component(result), Polarity::Negative)?;
                let (argument_effect, return_effect) = if self.batch.candidate_graph_effects {
                    let EffectEndpointKey::EffectRow(application_row) = self.canonical_effect(EffectEndpointKey::EffectRow(self.live_components[result_effect].ordinal)) else { unreachable!() };
                    let level = self.effect_levels[application_row as usize];
                    let row = self.fresh_effect_at_level(level)?;
                    invocation_effect = Some(row);
                    (
                        self.live_effect_term(
                            Polarity::Positive,
                            self.live_components[argument_effect].ordinal,
                        )?,
                        self.live_effect_term(Polarity::Negative, row)?,
                    )
                } else {
                    (
                        self.batch.collected_leaf_term(Leaf::EffectBottomPositive),
                        self.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    )
                };
                let demand =
                    self.negative_function_term(argument, argument_effect, return_effect, result)?;
                if let Some(source_input) = recipe.source_input {
                    let row = invocation_effect.ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    let application_effect = self.live_effect_term(
                        Polarity::Negative, self.live_components[result_effect].ordinal,
                    )?;
                    let CandidateRelation::Apply { callee_effect, .. } = recipe.relation
                        else { return Err(SolveAvailabilityError::IdentityExhausted); };
                    let callee_effect = self.live_effect_term(
                        Polarity::Positive, self.live_components[callee_effect].ordinal,
                    )?;
                    let input = self.batch.candidate_calls.calls.get_mut(source_input)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    if input.checking.occurrence() != &recipe.occurrence || input.native.is_some() {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    }
                    input.native = Some(crate::candidate_call::NativeInterface {
                        callee, argument, callee_effect, argument_effect, result, demand,
                        invocation_effect: return_effect, invocation_row: row, application_effect,
                    });
                }
                (callee, demand)
            }
        };
        let id = ConstraintOccurrenceId::new(recipe.occurrence.clone(), 0);
        let occurrence = ConstraintOccurrence {
            cause: CauseId::for_occurrence(id.clone()),
            id,
            lower,
            upper,
        };
        self.store
            .admit_and_record_provenance(&occurrence)
            .map_err(SolveAvailabilityError::from)?;
        let key = CanonicalValuePairKey {
            lower: self.value_endpoint(lower, Polarity::Positive),
            upper: self.value_endpoint(upper, Polarity::Negative),
        };
        let transitions = self.constrain_live_value(key, &occurrence.id, &occurrence.cause)?;
        #[cfg(test)]
        {
            self.initial_value_pair_probes += 1;
            self.summary_false_to_true_transitions += transitions;
        }
        #[cfg(not(test))]
        let _ = transitions;
        if self.batch.candidate_graph_effects {
            match recipe.relation {
                CandidateRelation::Group {
                    child_effect,
                    result_effect,
                    ..
                } => {
                    self.admit_candidate_effect(
                        recipe,
                        1,
                        self.live_components[child_effect].ordinal,
                        self.live_components[result_effect].ordinal,
                    )?;
                }
                CandidateRelation::Apply {
                    callee_effect,
                    result_effect,
                    ..
                } => {
                    let result = self.live_components[result_effect].ordinal;
                    self.admit_candidate_effect(
                        recipe,
                        1,
                        self.live_components[callee_effect].ordinal,
                        result,
                    )?;
                    self.admit_candidate_effect(
                        recipe,
                        2,
                        invocation_effect.expect("graph Apply allocates its invocation effect"),
                        result,
                    )?;
                }
            }
        }
        self.sample_f4_resources(ResourceBoundary::InitialAdmission)
    }

    fn admit_candidate_effect(
        &mut self,
        recipe: &CandidateConstraintRecipe,
        slot: u8,
        lower: u32,
        upper: u32,
    ) -> Result<(), SolveAvailabilityError> {
        let id = ConstraintOccurrenceId::new(recipe.occurrence.clone(), slot);
        let occurrence = ConstraintOccurrence {
            cause: CauseId::for_occurrence(id.clone()),
            id,
            lower: self.live_effect_term(Polarity::Positive, lower)?,
            upper: self.live_effect_term(Polarity::Negative, upper)?,
        };
        self.store
            .admit_and_record_provenance(&occurrence)
            .map_err(SolveAvailabilityError::from)?;
        self.constrain_live_effect(
            EffectEndpointKey::EffectRow(lower),
            EffectEndpointKey::EffectRow(upper),
            &occurrence.id,
            &occurrence.cause,
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn module(text: &str) -> Arc<HirModule> {
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        Arc::new(
            yu_hir::shadow::lower_module_with_shadow_applications(
                yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                    "candidate-internal",
                    "candidate.yu",
                ))),
                &parsed,
                yu_hir::SemanticImports::empty(),
            )
            .unwrap(),
        )
    }
    #[test]
    fn candidate_apply_fact_observation_rejects_copied_call() {
        let candidate =
            CandidateValueObservation::solve(module("my id x = x; my first = id 1")).unwrap();
        let [call] = candidate.calls() else {
            panic!("one Apply")
        };
        assert!(candidate.apply_fact(call).is_some());
        let copied = CandidateCall {
            occurrence: call.occurrence.clone(),
            callee: call.callee.clone(),
            argument: call.argument.clone(),
            unresolved: call.unresolved,
        };
        assert!(candidate.apply_fact(&copied).is_none());
    }

    #[test]
    fn candidate_apply_fact_observation_fails_closed_on_missing_or_ambiguous_inputs() {
        // Each mutation starts from an independently solved, valid observation.
        for scenario in 0..6 {
            let mut candidate =
                CandidateValueObservation::solve(module("my id x = x; my first = id 1")).unwrap();
            let occurrence = candidate.calls[0].occurrence.clone();
            let observation = candidate.apply_fact(&candidate.calls[0]).unwrap();
            let edge = observation.edge().clone();
            let fact = observation.fact().clone();
            match scenario {
                0 => candidate.apply_recipe_occurrences.clear(),
                1 => candidate.apply_recipe_occurrences.push(occurrence.clone()),
                2 => candidate
                    .solved
                    .store
                    .provenance
                    .retain(|retained| retained != &edge),
                3 => candidate.solved.store.provenance.push(edge),
                4 => candidate
                    .solved
                    .store
                    .facts
                    .retain(|retained| retained.id() != fact.id()),
                5 => candidate.solved.store.facts.push(fact),
                _ => unreachable!(),
            }
            assert!(
                candidate.apply_fact(&candidate.calls[0]).is_none(),
                "scenario {scenario}"
            );
        }
    }

    #[test]
    fn candidate_direct_chain_keeps_direction_and_bounded_shared_diagonal() {
        fn positive(value: &F5cPositive<'_>, qs: &mut HashSet<u32>) -> bool {
            match value {
                F5cPositive::Quantified(q) => {
                    qs.insert(*q);
                    false
                }
                F5cPositive::Int => true,
                F5cPositive::Union(parts) => parts
                    .iter()
                    .fold(false, |int, part| positive(part, qs) || int),
                _ => false,
            }
        }
        fn negative(value: &F5cNegative<'_>, qs: &mut HashSet<u32>) {
            match value {
                F5cNegative::Quantified(q) => {
                    qs.insert(*q);
                }
                F5cNegative::Intersection(parts) => {
                    for part in parts.iter() {
                        negative(part, qs);
                    }
                }
                _ => {}
            }
        }
        for case in [0, 1, 2] {
            let meter = DraftHeapMeter::default();
            let batch = ConstraintBatch::collect_mode(module("my f = 1"), true).unwrap();
            let mut session = InferenceSession::new(batch);
            let definition = session.batch.definitions[0].definition.clone();
            let root = session.batch.definitions[0].root.clone();
            let root_row = session.live_components
                [session.batch.root_component_positions[&root].component]
                .ordinal;
            let a = session.fresh_value_at_level(1).unwrap();
            let b = session.fresh_value_at_level(1).unwrap();
            let c = session.fresh_value_at_level(1).unwrap();
            for (lower, upper) in [(a, b), (b, c)] {
                session.bounds[lower as usize].direct_upper_rows.push(upper);
                session.bounds[upper as usize].direct_lower_rows.push(lower);
            }
            let (argument, result) = match case {
                0 => (a, c),
                1 => (c, a),
                _ => (a, a),
            };
            if case == 2 {
                session.bounds[a as usize]
                    .exact_non_variable_lowers
                    .push(ValueEndpointKey::IntPositive);
            }
            let argument = session
                .live_value_term(Polarity::Negative, argument)
                .unwrap();
            let result = session.live_value_term(Polarity::Positive, result).unwrap();
            let function = session
                .positive_function_term(
                    argument,
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    result,
                )
                .unwrap();
            session.bounds[root_row as usize]
                .exact_non_variable_lowers
                .push(ValueEndpointKey::PositiveFunction(function));
            let draft = session.generalization_draft(&meter, &definition).unwrap();
            let F5cPositive::Function {
                argument, result, ..
            } = &draft.predicate
            else {
                panic!("Function")
            };
            if case == 1 {
                assert_eq!(**argument, F5cNegative::Top);
                assert_eq!(**result, F5cPositive::Bottom);
            } else {
                let mut argument_qs = HashSet::new();
                let mut result_qs = HashSet::new();
                negative(argument, &mut argument_qs);
                let has_int = positive(result, &mut result_qs);
                assert!(argument_qs.intersection(&result_qs).next().is_some());
                if case == 2 {
                    assert!(has_int);
                }
            }
        }
    }
    #[test]
    fn candidate_boxed_and_flat_sessions_preserve_whole_scheme_parity() {
        for text in [
            "my id x = x; my wrap y = id y; pub out = wrap 1",
            "my id x = x; my wrap y = id (id y); pub out = wrap 1",
            "my self x = x x",
        ] {
            let hir = module(text);
            let mut results = Vec::new();
            for flat in [false, true] {
                let batch = ConstraintBatch::collect_mode(hir.clone(), true).unwrap();
                let mut session = InferenceSession::new(batch);
                session.flat_candidate_enabled = flat;
                results.push(session.run());
            }
            match (&results[0], &results[1]) {
                (Ok(boxed), Ok(flat)) => {
                    for item in hir.items() {
                        let HirItem::Binding(binding) = item else {
                            continue;
                        };
                        assert!(
                            boxed
                                .shadow_closed_schemes()
                                .for_root(binding.definition_root())
                                .unwrap()
                                .endpoints()
                                .alpha_eq(
                                    flat.shadow_closed_schemes()
                                        .for_root(binding.definition_root())
                                        .unwrap()
                                        .endpoints()
                                )
                        );
                    }
                }
                (Err(left), Err(right)) => assert_eq!(left, right),
                _ => panic!("boxed/flat availability differs"),
            }
        }
    }
    #[test]
    fn candidate_self_application_keeps_active_admission_invariant() {
        let hir = module("my self x = x x");
        let batch = ConstraintBatch::collect_mode(hir, true).unwrap();
        let mut session = InferenceSession::new(batch);
        session.admit_all_collected_facts().unwrap();
        let root = session.batch.definitions[0].root.clone();
        let row = session.live_components[session.batch.root_component_positions[&root].component]
            .ordinal;
        let meter = DraftHeapMeter::default();
        let mut generalizer = F5cGeneralizer::with_source_meter(&session, &meter);
        generalizer.assert_admission_invariant = true;
        // This checks safe generalizer execution, never source acceptance or R meaning.
        let _ = generalizer.build_component(row);
    }
    #[test]
    fn parameter_references_reuse_actual_startup_row() {
        let hir = module("my repeated f = f f");
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let ResolvedExpr::Lambda {
            parameter, body, ..
        } = binding.value()
        else {
            panic!("lambda")
        };
        let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
        let capture = candidate.solved.shadow_fresh_capture.as_ref().unwrap();
        let rows = capture.parameter_rows.as_ref().unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(&rows[0].0, parameter);
        let row = rows[0].1;
        assert!(
            capture.routes.is_empty(),
            "formals have no definition-use substitution"
        );
        let cause =
            CauseId::for_occurrence(ConstraintOccurrenceId::new(body.occurrence().clone(), 0));
        let fact_id = candidate
            .solved
            .store
            .provenance()
            .iter()
            .find(|edge| edge.cause() == &cause)
            .expect("Apply provenance")
            .fact();
        let fact = candidate
            .solved
            .store
            .facts()
            .iter()
            .find(|fact| fact.id() == fact_id)
            .expect("Apply demand");
        let TermView::LiveVariable(callee) =
            candidate.solved.store.term_view(fact.lower()).unwrap()
        else {
            panic!("direct formal callee")
        };
        assert_eq!(callee.ordinal(), row);
        let TermView::NegativeFunction { argument, .. } =
            candidate.solved.store.term_view(fact.upper()).unwrap()
        else {
            panic!("demand")
        };
        let TermView::LiveVariable(argument) = candidate.solved.store.term_view(argument).unwrap()
        else {
            panic!("direct formal argument")
        };
        assert_eq!(argument.ordinal(), row);
        let batch = ConstraintBatch::collect_mode(hir.clone(), true).unwrap();
        assert_eq!(batch.parameter_recipes.len(), 1);
        assert!(batch.definition_uses.is_empty());
        assert!(batch.components.iter().all(|component| !matches!(component,
            ComponentId::Occurrence { occurrence, kind: ComponentKind::Value } if occurrence != body.occurrence())));
    }
    #[test]
    fn preflight_depth_counts_both_apply_children() {
        let hir = module("my f x = x 1");
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let ResolvedExpr::Lambda { body, .. } = binding.value() else {
            panic!("lambda")
        };
        for callee_side in [true, false] {
            for (groups, accepted) in [(125, true), (126, false)] {
                let mut tree = binding.value().clone();
                let ResolvedExpr::Lambda { body: apply, .. } = &mut tree else {
                    unreachable!()
                };
                let ResolvedExpr::Apply {
                    callee, argument, ..
                } = apply.as_mut()
                else {
                    panic!("apply")
                };
                let child = if callee_side { callee } else { argument };
                for _ in 0..groups {
                    **child = ResolvedExpr::Group {
                        occurrence: body.occurrence().clone(),
                        range: body.range().clone(),
                        inner: Box::new(child.as_ref().clone()),
                    };
                }
                assert_eq!(
                    preflight_expression(&tree, &mut Vec::new(), &mut HashSet::new()).is_ok(),
                    accepted
                );
            }
        }
    }
    #[test]
    fn preflight_depth_counts_root_lambda_and_every_group_child() {
        let hir = module("my f x = 1");
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let ResolvedExpr::Lambda {
            occurrence,
            parameter,
            body,
            range,
        } = binding.value()
        else {
            panic!("lambda")
        };
        for (groups, accepted) in [(126, true), (127, false)] {
            let mut inner = body.as_ref().clone();
            for _ in 0..groups {
                inner = ResolvedExpr::Group {
                    occurrence: body.occurrence().clone(),
                    range: range.clone(),
                    inner: Box::new(inner),
                };
            }
            let tree = ResolvedExpr::Lambda {
                occurrence: occurrence.clone(),
                parameter: parameter.clone(),
                body: Box::new(inner),
                range: range.clone(),
            };
            let result = preflight_expression(&tree, &mut Vec::new(), &mut HashSet::new());
            assert_eq!(result.is_ok(), accepted);
        }
    }
}
