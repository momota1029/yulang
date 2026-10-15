//! Private top-level successor graph capture and per-use reconstruction.
//! This retains live algebra, not a closed F5 scheme or a Call certificate.
use crate::*;

#[derive(Debug, Default)]
pub(super) struct GraphState {
    pub intrusion: candidate_intrusion::State,
    pub graphs: Vec<Option<Graph>>,
    pub routes: Vec<FreshRoute>,
    pub locals: Vec<Option<LocalScheme>>,
    pub local_routes: Vec<LocalFreshRoute>,
    pub local_use: Vec<LocalUse>,
    #[cfg(test)]
    pub local_use_census: Option<LocalUseCensus>,
    pub source: Option<candidate_source::Frame>,
    pub retained_bytes: usize,
    pub scratch_bytes: usize,
    pub orchestration_bytes: usize,
    pub capture_peak_bytes: usize,
    pub use_peak_bytes: usize,
    #[cfg(test)]
    pub evidence_failure: Option<candidate_context::EvidenceFailurePoint>,
    #[cfg(test)]
    pub failed_evidence_point: Option<candidate_context::EvidenceFailurePoint>,
    #[cfg(test)]
    pub failed_evidence_sample: Option<(candidate_context::EvidenceFailurePoint, usize, usize)>,
    #[cfg(test)]
    pub import_failure_sample: Option<(usize, usize, bool)>,
    #[cfg(test)]
    pub failed_import_count: Option<usize>,
    #[cfg(test)]
    pub capture_evidence_peak_capacity: usize,
    #[cfg(test)]
    pub import_evidence_peak_capacity: usize,
}

#[derive(Debug)]
pub(super) struct Graph {
    pub source_frontier: Vec<candidate_source::SourceRegionId>,
    pub owned_regions: Vec<candidate_source::SourceRegionId>,
    pub negative_functions: HashMap<Term, usize>,
    pub nodes: Vec<Node>,
    pub rows: Vec<Row>,
    pub bounds: Vec<Bound>,
    pub bound_evidence: Vec<candidate_context::EvidenceSnapshot>,
    pub attachment_bundles: Vec<(candidate_context::RelationId, candidate_context::AttachmentBundleId)>,
    pub attachment_spans: HashMap<candidate_context::RelationId, (usize, usize)>,
    pub context_views: Vec<(candidate_context::LocalWeightId, u32, Option<usize>)>,
    pub root: usize,
    pub live_root: u32,
    pub boundary: u32,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum RowKey {
    Value(u32),
    Effect(u32),
}
impl RowKey {
    pub fn kind(self) -> ComponentKind {
        match self {
            Self::Value(_) => ComponentKind::Value,
            Self::Effect(_) => ComponentKind::Effect,
        }
    }
    fn ordinal(self) -> u32 {
        match self {
            Self::Value(i) | Self::Effect(i) => i,
        }
    }
}
#[derive(Clone, Copy, Debug)]
pub(super) struct Row {
    pub key: RowKey,
    pub local: bool,
}
#[derive(Clone, Copy, Debug)]
pub(super) enum Node {
    Leaf(Atom),
    EffectOperand { endpoint: EffectEndpointKey, tail: Option<usize>, polarity: Polarity },
    Row {
        row: usize,
        polarity: Polarity,
    },
    Function {
        polarity: Polarity,
        children: [usize; 4],
    },
}
#[derive(Clone, Copy, Debug)]
pub(super) enum Atom {
    Bottom,
    Top,
    NegativeBottom,
    IntPositive,
    IntNegative,
    UnitPositive,
    BoolPositive,
    StrPositive,
    UnitNegative,
    BoolNegative,
    StrNegative,
    EffectBottom,
    EmptyEffect,
}
// This reference is valid only inside its owning Graph.
#[derive(Clone, Copy, Debug)]
pub(super) struct CapturedEvidenceRef(pub usize);
#[derive(Clone, Copy, Debug)]
pub(super) struct Bound {
    pub evidence: CapturedEvidenceRef,
    pub relation: Option<candidate_context::RelationId>,
    pub source_bound: candidate_effect::BoundKey,
    pub kind: ComponentKind,
    pub side: Polarity,
    pub lower: usize,
    pub upper: usize,
}
#[derive(Debug)]
pub(super) struct FreshRoute {
    pub use_id: DefinitionUseId,
    pub graph: Graph,
    pub rows: Vec<RowKey>,
}
#[derive(Debug)]
pub(super) struct LocalScheme {
    pub capture_region: Option<candidate_source::SourceRegionId>,
    pub id: yu_hir::HirLocalId,
    pub root: u32,
    pub boundary: u32,
}
#[derive(Debug)]
pub(super) struct LocalFreshRoute {
    pub slot: usize,
    pub local: yu_hir::HirLocalId,
    pub occurrence: HirOccurrenceId,
    pub graph: Graph,
    pub rows: Vec<RowKey>,
}
// Disposable, explicitly enabled native-constructor observations. The route
// continues to own its graph and row map; this retains only expiring maps.
#[cfg(test)]
#[derive(Debug, Default)]
pub(super) struct LocalUseCensus {
    pub requested: HashSet<HirOccurrenceId>,
    pub snapshots: Vec<LocalUseSnapshot>,
    pub module_uses: Vec<(HirOccurrenceId, usize)>,
}
#[cfg(test)]
#[derive(Debug)]
pub(super) struct LocalUseSnapshot {
    pub route: usize,
    pub slot: usize,
    pub occurrence: HirOccurrenceId,
    pub target_component: usize,
    pub terms: Vec<Option<Term>>,
    pub effect_operands: HashMap<usize, EffectEndpointKey>,
    pub context_remap: HashMap<candidate_context::ContextId, candidate_context::ContextId>,
    pub evidence_remap: Vec<candidate_context::EvidenceSnapshotId>,
    pub context_use: usize,
    pub restored_bounds: usize,
}
// Construction is atomic. Only the ordered restoration frontier is mutable
// after this fresh use is retained; resume never rebuilds these remaps.
#[derive(Debug)]
pub(super) struct FreshUse {
    scope_remap: candidate_source::ScopeRemap,
    scoped_relations: HashMap<candidate_context::RelationId, candidate_context::ScopedFlow>,
    context_use: usize,
    rows: Vec<RowKey>,
    terms: Vec<Option<Term>>,
    effect_operands: HashMap<usize, EffectEndpointKey>,
    bundle_remap: HashMap<candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId>,
    context_remap: HashMap<candidate_context::ContextId, candidate_context::ContextId>,
    evidence_remap: Vec<candidate_context::EvidenceSnapshotId>,
}
impl FreshUse {
    fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        sum(&[self.scope_remap.bytes()?, bytes::<(candidate_context::RelationId, candidate_context::ScopedFlow)>(self.scoped_relations.capacity())?, bytes::<RowKey>(self.rows.capacity())?, bytes::<Option<Term>>(self.terms.capacity())?,
            bytes::<(usize, EffectEndpointKey)>(self.effect_operands.capacity())?,
            bytes::<(candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId)>(self.bundle_remap.capacity())?,
            bytes::<(candidate_context::ContextId, candidate_context::ContextId)>(self.context_remap.capacity())?,
            bytes::<candidate_context::EvidenceSnapshotId>(self.evidence_remap.capacity())?])
    }
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct LocalUseCursor {
    pub next_bound: usize,
    pub restoration: Option<candidate_context::ReplayOperationId>,
    pub complete: bool,
}
#[derive(Debug)]
pub(super) struct LocalUse {
    slot: usize,
    local: yu_hir::HirLocalId,
    occurrence: HirOccurrenceId,
    value: usize,
    level: u32,
    graph: Graph,
    fresh: FreshUse,
    pub cursor: LocalUseCursor,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LocalRun { Complete, Paused }
// This closed script holds one exclusive session borrow from the first pause
// through resume/rollback. It has no callback or external mutation operation.
// Idle is a conditional unchanged-wait control, not a readiness certificate.
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(super) enum LocalScriptStep { DriveOne, Idle, FailOne, Complete }
#[cfg(test)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LocalScriptObservation {
    pub source_next: usize,
    pub use_origin: Option<usize>,
    pub cursor: Option<LocalUseCursor>,
    pub restoration: Option<candidate_context::BoundRestoration>,
    pub checkpoint: candidate_context::Checkpoint,
    pub retained_bytes: usize,
    pub routes: usize,
    pub facts: usize,
    pub typed_drains: usize,
}
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
enum Endpoint {
    Value(ValueEndpointKey, Polarity),
    Effect(EffectEndpointKey, Polarity),
}
fn exhausted() -> SolveAvailabilityError {
    SolveAvailabilityError::IdentityExhausted
}
fn push<T>(values: &mut Vec<T>, value: T) -> Result<(), SolveAvailabilityError> {
    values.try_reserve(1).map_err(|_| exhausted())?;
    values.push(value);
    Ok(())
}
fn bytes<T>(capacity: usize) -> Result<usize, SolveAvailabilityError> {
    capacity
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(exhausted)
}
fn vec_bytes<T>(values: &Vec<T>) -> Result<usize, SolveAvailabilityError> {
    bytes::<T>(values.capacity())
}
fn sum(parts: &[usize]) -> Result<usize, SolveAvailabilityError> {
    parts
        .iter()
        .try_fold(0usize, |n, &part| n.checked_add(part).ok_or_else(exhausted))
}
impl Graph {
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        sum(&[
            bytes::<(candidate_context::LocalWeightId, u32, Option<usize>)>(self.context_views.capacity())?,
            bytes::<candidate_source::SourceRegionId>(self.source_frontier.capacity())?,
            bytes::<candidate_source::SourceRegionId>(self.owned_regions.capacity())?,
            bytes::<(Term, usize)>(self.negative_functions.capacity())?,
            bytes::<Node>(self.nodes.capacity())?,
            bytes::<Row>(self.rows.capacity())?,
            bytes::<Bound>(self.bounds.capacity())?,
            bytes::<candidate_context::EvidenceSnapshot>(self.bound_evidence.capacity())?,
            bytes::<(candidate_context::RelationId, candidate_context::AttachmentBundleId)>(self.attachment_bundles.capacity())?,
            bytes::<(candidate_context::RelationId, (usize, usize))>(self.attachment_spans.capacity())?,
        ])
    }
}
impl GraphState {
    pub(super) fn commit_local_use(&mut self) {
        let frame = self.local_use.pop().expect("completed local parent");
        #[cfg(test)]
        if let Some(census) = &mut self.local_use_census {
            if census.requested.contains(&frame.occurrence) {
                census.snapshots.push(LocalUseSnapshot {
                    route: self.local_routes.len(), slot: frame.slot,
                    occurrence: frame.occurrence.clone(), target_component: frame.value,
                    terms: frame.fresh.terms.clone(),
                    effect_operands: frame.fresh.effect_operands.clone(),
                    context_remap: frame.fresh.context_remap.clone(),
                    evidence_remap: frame.fresh.evidence_remap.clone(),
                    context_use: frame.fresh.context_use,
                    restored_bounds: frame.cursor.next_bound,
                });
            }
        }

        // All capacities and arithmetic were preflighted by frame accounting and
        // final route reservation. Only construction maps are released here.
        let released = frame.fresh.bytes().expect("accounted fresh storage")
            - bytes::<RowKey>(frame.fresh.rows.capacity()).expect("accounted rows");
        self.local_routes.push(LocalFreshRoute { slot: frame.slot, local: frame.local,
            occurrence: frame.occurrence, graph: frame.graph, rows: frame.fresh.rows });
        self.retained_bytes -= released;
    }
    pub fn refresh_bytes(&mut self) -> Result<(), SolveAvailabilityError> {
        let mut total = sum(&[
            bytes::<Option<Graph>>(self.graphs.capacity())?,
            bytes::<FreshRoute>(self.routes.capacity())?,
            bytes::<Option<LocalScheme>>(self.locals.capacity())?,
            bytes::<LocalFreshRoute>(self.local_routes.capacity())?,
            bytes::<LocalUse>(self.local_use.capacity())?,
        ])?;
        for graph in self.graphs.iter().flatten() {
            total = total.checked_add(graph.bytes()?).ok_or_else(exhausted)?;
        }
        for route in &self.routes {
            total = sum(&[total, route.graph.bytes()?, bytes::<RowKey>(route.rows.capacity())?])?;
        }
        for route in &self.local_routes {
            total = sum(&[total, route.graph.bytes()?, bytes::<RowKey>(route.rows.capacity())?])?;
        }
        for frame in &self.local_use {
            total = sum(&[total, frame.graph.bytes()?, frame.fresh.bytes()?])?;
        }
        self.retained_bytes = total;
        Ok(())
    }
}
#[derive(Default)]
struct CaptureEvidenceMeter {
    bytes: std::cell::Cell<usize>,
    #[cfg(test)]
    capacity: std::cell::Cell<usize>,
}
struct Capture<'a> {
    evidence_keys: HashMap<candidate_context::EvidenceSnapshot, CapturedEvidenceRef>,
    evidence_charge: &'a CaptureEvidenceMeter,
    session: &'a InferenceSession,
    graph: Graph,
    endpoints: HashMap<Endpoint, usize>,
    rows: HashMap<RowKey, usize>,
    pending: Vec<Endpoint>,
    bound_keys: HashSet<(ComponentKind, Polarity, usize, usize, Option<candidate_context::RelationId>)>,
    boundary: u32,
}
impl<'a> Capture<'a> {
    fn charge_evidence(&self) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        self.evidence_charge.capacity.set(self.evidence_keys.capacity());
        self.evidence_charge.bytes.set(sum(&[
            bytes::<(candidate_context::EvidenceSnapshot, CapturedEvidenceRef)>(self.evidence_keys.capacity())?,
            bytes::<candidate_context::EvidenceSnapshot>(self.graph.bound_evidence.capacity())?,
        ])?);
        Ok(())
    }
    fn intern(&mut self, endpoint: Endpoint) -> Result<usize, SolveAvailabilityError> {
        let endpoint = match endpoint { Endpoint::Value(v, p) => Endpoint::Value(self.session.canonical_value(v), p), Endpoint::Effect(e, p) => Endpoint::Effect(self.session.canonical_effect(e), p) };
        if let Some(&index) = self.endpoints.get(&endpoint) {
            return Ok(index);
        }
        self.endpoints.try_reserve(1).map_err(|_| exhausted())?;
        let index = self.graph.nodes.len();
        push(&mut self.graph.nodes, Node::Leaf(Atom::Bottom))?;
        push(&mut self.pending, endpoint)?;
        self.endpoints.insert(endpoint, index);
        Ok(index)
    }
    fn row(&mut self, key: RowKey) -> Result<usize, SolveAvailabilityError> {
        let key = self.session.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.rep(key);
        if let Some(&index) = self.rows.get(&key) {
            return Ok(index);
        }
        let ordinal = key.ordinal() as usize;
        let (level, metadata) = match key {
            RowKey::Value(_) => (
                self.session.value_levels.get(ordinal),
                self.session.value_metadata.get(ordinal),
            ),
            RowKey::Effect(_) => (
                self.session.effect_levels.get(ordinal),
                self.session.effect_metadata.get(ordinal),
            ),
        };
        let (&level, metadata) = (
            level.ok_or_else(exhausted)?,
            metadata.ok_or_else(exhausted)?,
        );
        let local = level > self.boundary && !metadata.non_generic;
        self.rows.try_reserve(1).map_err(|_| exhausted())?;
        let index = self.graph.rows.len();
        push(&mut self.graph.rows, Row { key, local })?;
        self.rows.insert(key, index);
        Ok(index)
    }
    fn term_endpoint(
        &self,
        term: Term,
        kind: ComponentKind,
        polarity: Polarity,
    ) -> Result<Endpoint, SolveAvailabilityError> {
        let endpoint = match self
            .session
            .store
            .term_view(term)
            .map_err(|_| exhausted())?
        {
            TermView::Component(component) if component.kind() == kind => {
                let row = self.session.component_endpoint(term);
                match kind {
                    ComponentKind::Value => {
                        Endpoint::Value(ValueEndpointKey::ValueRow(row.ordinal), polarity)
                    }
                    ComponentKind::Effect => {
                        Endpoint::Effect(EffectEndpointKey::EffectRow(row.ordinal), polarity)
                    }
                }
            }
            TermView::LiveVariable(v) if v.kind() == kind && v.polarity() == polarity => match kind
            {
                ComponentKind::Value => {
                    Endpoint::Value(ValueEndpointKey::ValueRow(v.ordinal()), polarity)
                }
                ComponentKind::Effect => {
                    Endpoint::Effect(EffectEndpointKey::EffectRow(v.ordinal()), polarity)
                }
            },
            TermView::PositiveFunction { .. }
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::PositiveFunction(term), polarity)
            }
            TermView::NegativeFunction { .. }
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::NegativeFunction(term), polarity)
            }
            TermView::PositiveBottom
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::BottomPositive, polarity)
            }
            TermView::NegativeTop
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::TopNegative, polarity)
            }
            TermView::NegativeBottom
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::BottomNegative, polarity)
            }
            TermView::Leaf(Leaf::IntPositive)
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::IntPositive, polarity)
            }
            TermView::Leaf(Leaf::UnitPositive)
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::UnitPositive, polarity)
            }
            TermView::Leaf(Leaf::BoolPositive)
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::BoolPositive, polarity)
            }
            TermView::Leaf(Leaf::StrPositive)
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::StrPositive, polarity)
            }
            TermView::Leaf(Leaf::IntNegative)
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::IntNegative, polarity)
            }
            TermView::Leaf(Leaf::UnitNegative)
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::UnitNegative, polarity)
            }
            TermView::Leaf(Leaf::BoolNegative)
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::BoolNegative, polarity)
            }
            TermView::Leaf(Leaf::StrNegative)
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::StrNegative, polarity)
            }
            TermView::Leaf(Leaf::EffectBottomPositive)
                if kind == ComponentKind::Effect && polarity == Polarity::Positive =>
            {
                Endpoint::Effect(EffectEndpointKey::BottomPositive, polarity)
            }
            TermView::Leaf(Leaf::EmptyEffectNegative)
                if kind == ComponentKind::Effect && polarity == Polarity::Negative =>
            {
                Endpoint::Effect(EffectEndpointKey::EmptyNegative, polarity)
            }
            _ => return Err(exhausted()),
        };
        Ok(endpoint)
    }
    fn expand_node(&mut self, endpoint: Endpoint) -> Result<(), SolveAvailabilityError> {
        use EffectEndpointKey as E;
        use ValueEndpointKey as V;
        let index = self.endpoints[&endpoint];
        let node = match endpoint {
            Endpoint::Value(V::ValueRow(i), p) => Node::Row {
                row: self.row(RowKey::Value(i))?,
                polarity: p,
            },
            Endpoint::Effect(E::EffectRow(i), p) => Node::Row {
                row: self.row(RowKey::Effect(i))?,
                polarity: p,
            },
            Endpoint::Value(V::BottomPositive, Polarity::Positive) => Node::Leaf(Atom::Bottom),
            Endpoint::Value(V::TopNegative, Polarity::Negative) => Node::Leaf(Atom::Top),
            Endpoint::Value(V::BottomNegative, Polarity::Negative) => {
                Node::Leaf(Atom::NegativeBottom)
            }
            Endpoint::Value(V::IntPositive, Polarity::Positive) => Node::Leaf(Atom::IntPositive),
            Endpoint::Value(V::UnitPositive, Polarity::Positive) => Node::Leaf(Atom::UnitPositive),
            Endpoint::Value(V::BoolPositive, Polarity::Positive) => Node::Leaf(Atom::BoolPositive),
            Endpoint::Value(V::StrPositive, Polarity::Positive) => Node::Leaf(Atom::StrPositive),
            Endpoint::Value(V::IntNegative, Polarity::Negative) => Node::Leaf(Atom::IntNegative),
            Endpoint::Value(V::UnitNegative, Polarity::Negative) => Node::Leaf(Atom::UnitNegative),
            Endpoint::Value(V::BoolNegative, Polarity::Negative) => Node::Leaf(Atom::BoolNegative),
            Endpoint::Value(V::StrNegative, Polarity::Negative) => Node::Leaf(Atom::StrNegative),
            Endpoint::Effect(E::BottomPositive, Polarity::Positive) => {
                Node::Leaf(Atom::EffectBottom)
            }
            Endpoint::Effect(E::EmptyNegative, Polarity::Negative) => Node::Leaf(Atom::EmptyEffect),
            Endpoint::Effect(endpoint @ E::Contribution(_), Polarity::Positive) => Node::EffectOperand { endpoint, tail: None, polarity: Polarity::Positive },
            Endpoint::Effect(endpoint @ E::AnnotationMember(id, _), Polarity::Positive) => {
                let tail = self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[id as usize].tail;
                let tail = tail.map(|row| self.intern(Endpoint::Effect(E::EffectRow(row), Polarity::Positive))).transpose()?;
                Node::EffectOperand { endpoint, tail, polarity: Polarity::Positive }
            },
            Endpoint::Effect(endpoint @ E::Allowance(id), Polarity::Negative)
            | Endpoint::Effect(endpoint @ E::Support(id), Polarity::Positive) => {
                let polarity = if matches!(endpoint, E::Support(_)) { Polarity::Positive } else { Polarity::Negative };
                let tail = self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[id as usize].tail;
                let tail = tail.map(|row| self.intern(Endpoint::Effect(E::EffectRow(row), polarity))).transpose()?;
                Node::EffectOperand { endpoint, tail, polarity }
            }
            Endpoint::Value(V::PositiveFunction(term), Polarity::Positive)
            | Endpoint::Value(V::NegativeFunction(term), Polarity::Negative) => {
                let (p, terms) = match self
                    .session
                    .store
                    .term_view(term)
                    .map_err(|_| exhausted())?
                {
                    TermView::PositiveFunction {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => (
                        Polarity::Positive,
                        [argument, argument_effect, result_effect, result],
                    ),
                    TermView::NegativeFunction {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => (
                        Polarity::Negative,
                        [argument, argument_effect, result_effect, result],
                    ),
                    _ => return Err(exhausted()),
                };
                let expected = match endpoint {
                    Endpoint::Value(_, p) => p,
                    _ => unreachable!(),
                };
                if p != expected {
                    return Err(exhausted());
                }
                let opposite = if p == Polarity::Positive {
                    Polarity::Negative
                } else {
                    Polarity::Positive
                };
                let kinds = [
                    ComponentKind::Value,
                    ComponentKind::Effect,
                    ComponentKind::Effect,
                    ComponentKind::Value,
                ];
                let polarities = [opposite, opposite, p, p];
                let mut children = [0; 4];
                for i in 0..4 {
                    children[i] =
                        self.intern(self.term_endpoint(terms[i], kinds[i], polarities[i])?)?;
                }
                Node::Function {
                    polarity: p,
                    children,
                }
            }
            _ => return Err(exhausted()),
        };
        self.graph.nodes[index] = node;
        Ok(())
    }
    fn bound(
        &mut self,
        kind: ComponentKind,
        side: Polarity,
        lower: Endpoint,
        upper: Endpoint,
    ) -> Result<(), SolveAvailabilityError> {
        let endpoint = |endpoint| match endpoint { Endpoint::Value(v, _) => ExtrusionEndpoint::Value(v), Endpoint::Effect(e, _) => ExtrusionEndpoint::Effect(e) };
        let (owner, item) = if side == Polarity::Positive { (endpoint(upper), endpoint(lower)) } else { (endpoint(lower), endpoint(upper)) };
        let context = &self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        let mut cursor = context.bound_cursor(candidate_effect::BoundKey(owner, side, item));
        let absent = cursor.is_none();
        let lower = self.intern(lower)?;
        let upper = self.intern(upper)?;
        let mut absent = absent;
        while cursor.is_some() || absent {
            let relation = if let Some(index) = cursor {
                let (relation, next) = self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_entry(index);
                cursor = next;
                Some(relation)
            } else { absent = false; None };
            let key = (kind, side, lower, upper, relation);
            if self.bound_keys.contains(&key) { continue; }
            self.bound_keys.try_reserve(1).map_err(|_| exhausted())?;
            let source_bound = candidate_effect::BoundKey(owner, side, item);
            let snapshot = self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.evidence_snapshot(source_bound, relation);
            let evidence = if let Some(&evidence) = self.evidence_keys.get(&snapshot) { evidence } else {
                let reserved = self.evidence_keys.try_reserve(1);
                self.charge_evidence()?;
                reserved.map_err(|_| exhausted())?;
                let reserved = self.graph.bound_evidence.try_reserve(1);
                self.charge_evidence()?;
                reserved.map_err(|_| exhausted())?;
                #[cfg(test)]
                if self.session.candidate_graph.as_ref().unwrap().evidence_failure == Some(candidate_context::EvidenceFailurePoint::CaptureScratch) {
                    return Err(exhausted());
                }
                let evidence = CapturedEvidenceRef(self.graph.bound_evidence.len());
                self.graph.bound_evidence.push(snapshot);
                self.evidence_keys.insert(snapshot, evidence);
                evidence
            };
            push(&mut self.graph.bounds, Bound { evidence, relation, source_bound, kind, side, lower, upper })?;
            self.bound_keys.insert(key);
        }
        Ok(())
    }
    fn expand_row(&mut self, index: usize) -> Result<(), SolveAvailabilityError> {
        let Row { key, local } = self.graph.rows[index];
        let session = self.session;
        // freshenAbove stops at older identities. Their mutable bounds stay
        // in the session, so later constraints reach every shared anchor use.
        if !local { return Ok(()); }
        let p = Polarity::Positive;
        let n = Polarity::Negative;
        match key {
            RowKey::Value(i) => {
                let row = session.bounds.get(i as usize).ok_or_else(exhausted)?;
                for &lower in &row.direct_lower_rows {
                    self.bound(
                        ComponentKind::Value,
                        Polarity::Positive,
                        Endpoint::Value(ValueEndpointKey::ValueRow(lower), p),
                        Endpoint::Value(ValueEndpointKey::ValueRow(i), n),
                    )?;
                }
                for &upper in &row.direct_upper_rows {
                    self.bound(
                        ComponentKind::Value,
                        Polarity::Negative,
                        Endpoint::Value(ValueEndpointKey::ValueRow(i), p),
                        Endpoint::Value(ValueEndpointKey::ValueRow(upper), n),
                    )?;
                }
                for &lower in &row.exact_non_variable_lowers {
                    if matches!(lower, ValueEndpointKey::ValueRow(_)) {
                        return Err(exhausted());
                    }
                    self.bound(
                        ComponentKind::Value,
                        Polarity::Positive,
                        Endpoint::Value(lower, p),
                        Endpoint::Value(ValueEndpointKey::ValueRow(i), n),
                    )?;
                }
                for &upper in &row.exact_non_variable_uppers {
                    if matches!(upper, ValueEndpointKey::ValueRow(_)) {
                        return Err(exhausted());
                    }
                    self.bound(
                        ComponentKind::Value,
                        Polarity::Negative,
                        Endpoint::Value(ValueEndpointKey::ValueRow(i), p),
                        Endpoint::Value(upper, n),
                    )?;
                }
            }
            RowKey::Effect(i) => {
                let state = &session.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra;
                let mut record = state.capture_incidence.get(&i).map(|bucket| bucket.head);
                while let Some(index) = record {
                    let incidence = state.capture_records[index];
                    record = incidence.next;
                    self.bound(ComponentKind::Effect, n,
                        Endpoint::Effect(EffectEndpointKey::EffectRow(incidence.source), p),
                        Endpoint::Effect(EffectEndpointKey::Allowance(incidence.view), n))?;
                }
                let row = session
                    .effect_bounds
                    .get(i as usize)
                    .ok_or_else(exhausted)?;
                for &lower in &row.direct_lower_rows {
                    self.bound(
                        ComponentKind::Effect,
                        Polarity::Positive,
                        Endpoint::Effect(EffectEndpointKey::EffectRow(lower), p),
                        Endpoint::Effect(EffectEndpointKey::EffectRow(i), n),
                    )?;
                }
                for &upper in &row.direct_upper_rows {
                    self.bound(
                        ComponentKind::Effect,
                        Polarity::Negative,
                        Endpoint::Effect(EffectEndpointKey::EffectRow(i), p),
                        Endpoint::Effect(EffectEndpointKey::EffectRow(upper), n),
                    )?;
                }
                for &lower in &row.exact_non_variable_lowers {
                    if matches!(lower, EffectEndpointKey::EffectRow(_)) {
                        return Err(exhausted());
                    }
                    self.bound(
                        ComponentKind::Effect,
                        Polarity::Positive,
                        Endpoint::Effect(lower, p),
                        Endpoint::Effect(EffectEndpointKey::EffectRow(i), n),
                    )?;
                }
                for &upper in &row.exact_non_variable_uppers {
                    if matches!(upper, EffectEndpointKey::EffectRow(_)) {
                        return Err(exhausted());
                    }
                    self.bound(
                        ComponentKind::Effect,
                        Polarity::Negative,
                        Endpoint::Effect(EffectEndpointKey::EffectRow(i), p),
                        Endpoint::Effect(upper, n),
                    )?;
                }
            }
        }
        Ok(())
    }
}
impl InferenceSession {
    pub(super) fn start_candidate_graph(&mut self) -> Result<(), SolveAvailabilityError> {
        let mut state = GraphState::default();
        state.intrusion.effect_algebra.initialize()?;
        state.intrusion.effect_algebra.context.scoped_enabled = self.batch.candidate_source.scoped_experiment;
        if self.batch.candidate_source.scoped_experiment {
            state.intrusion.effect_algebra.context.scope_inventory = candidate_source::ScopeInventory::from_plan(&self.batch.candidate_source)?;
        }
        state
            .graphs
            .try_reserve_exact(self.batch.definitions.len())
            .map_err(|_| exhausted())?;
        state
            .graphs
            .resize_with(self.batch.definitions.len(), || None);
        state.locals.try_reserve_exact(self.batch.candidate_source.locals.len()).map_err(|_| exhausted())?;
        state.locals.resize_with(self.batch.candidate_source.locals.len(), || None);
        state.refresh_bytes()?;
        self.candidate_graph = Some(state);
        Ok(())
    }
    pub(super) fn capture_candidate_graph(&mut self, row: u32, boundary: u32) -> Result<Graph, SolveAvailabilityError> {
        self.capture_candidate_graph_owned(row, boundary, &[])
    }
    fn capture_candidate_graph_owned(&mut self, row: u32, boundary: u32, frontier: &[candidate_source::SourceRegionId]) -> Result<Graph, SolveAvailabilityError> {
        if self.batch.candidate_source.scoped_experiment && frontier.is_empty() { return Err(SolveAvailabilityError::ReceiptMismatch); }
        let entry = self.candidate_graph.as_ref().ok_or_else(exhausted)?.scratch_bytes;
        let evidence_charge = CaptureEvidenceMeter::default();
        let result = self.capture_candidate_graph_inner(row, boundary, &evidence_charge, frontier);
        #[cfg(test)]
        {
            let state = self.candidate_graph.as_mut().unwrap();
            state.capture_evidence_peak_capacity = state.capture_evidence_peak_capacity.max(evidence_charge.capacity.get());
        }
        if result.is_err() {
            // Capture owns immutable session access. Its checked capacity meter
            // survives failure, so dropped transient evidence is still sampled.
            let state = self.candidate_graph.as_mut().unwrap();
            state.scratch_bytes = entry.checked_add(evidence_charge.bytes.get()).ok_or_else(exhausted)?;
            state.capture_peak_bytes = state.capture_peak_bytes.max(state.scratch_bytes);
            let sampled = self.sample_f4_resources(ResourceBoundary::SourceDrafts);
            #[cfg(test)]
            if self.candidate_graph.as_ref().unwrap().evidence_failure == Some(candidate_context::EvidenceFailurePoint::CaptureScratch) {
                let total = self.resource_ledger.inference_session_retained_bytes;
                let state = self.candidate_graph.as_mut().unwrap();
                state.evidence_failure = None;
                state.failed_evidence_point = Some(candidate_context::EvidenceFailurePoint::CaptureScratch);
                state.failed_evidence_sample = Some((candidate_context::EvidenceFailurePoint::CaptureScratch, state.scratch_bytes, total));
            }
            self.candidate_graph.as_mut().unwrap().scratch_bytes = entry;
            // Preserve the original capture failure even if its sample also fails.
            let _ = sampled;
        }
        result
    }
    fn capture_candidate_graph_inner(&mut self, row: u32, boundary: u32, evidence_charge: &CaptureEvidenceMeter, frontier: &[candidate_source::SourceRegionId]) -> Result<Graph, SolveAvailabilityError> {
        let mut source_frontier = Vec::new(); source_frontier.try_reserve_exact(frontier.len()).map_err(|_| exhausted())?;
        source_frontier.extend_from_slice(frontier);
        let owned_regions = self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra.context.scope_inventory.owned(frontier)?;
        let mut capture = Capture {
            evidence_keys: HashMap::new(),
            evidence_charge,
            session: self,
            graph: Graph {
                source_frontier, owned_regions, negative_functions: HashMap::new(),
                nodes: Vec::new(),
                rows: Vec::new(),
                bounds: Vec::new(),
                bound_evidence: Vec::new(),
                attachment_bundles: Vec::new(),
                attachment_spans: HashMap::new(),
                context_views: Vec::new(),
                root: 0,
                live_root: row,
                boundary,
            },
            endpoints: HashMap::new(),
            rows: HashMap::new(),
            pending: Vec::new(),
            bound_keys: HashSet::new(),
            boundary,
        };
        capture.graph.root = capture.intern(Endpoint::Value(
            ValueEndpointKey::ValueRow(row),
            Polarity::Positive,
        ))?;
        let mut row_cursor = 0;
        let mut bound_cursor = 0;
        let mut context_seen = HashSet::new();
        let mut payload_seen = HashSet::new();
        let mut context_pending = Vec::new();
        let mut payloads = Vec::new();
        loop {
            while !capture.pending.is_empty() || row_cursor < capture.graph.rows.len() {
                while let Some(endpoint) = capture.pending.pop() { capture.expand_node(endpoint)?; }
                if row_cursor < capture.graph.rows.len() {
                    capture.expand_row(row_cursor)?;
                    row_cursor += 1;
                }
            }
            while bound_cursor < capture.graph.bounds.len() {
                let bound = capture.graph.bounds[bound_cursor];
                bound_cursor += 1;
                if let Some(relation) = bound.relation {
                    let context = &capture.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
                    context.context_payloads(context.relation_context(relation)?, &mut context_seen, &mut context_pending, &mut payloads)?;
                    // A deferred original demand is a retained latent payload,
                    // even when no structural bound reaches its Function root.
                    if let Some(demand) = context.scoped_flow(relation)?.demand {
                        capture.intern(Endpoint::Value(ValueEndpointKey::NegativeFunction(demand.root), Polarity::Negative))?;
                    }
                }
            }
            while let Some(weight) = payloads.pop() {
                if payload_seen.contains(&weight) { continue; }
                payload_seen.try_reserve(1).map_err(|_| exhausted())?;
                payload_seen.insert(weight);
                let algebra = &capture.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
                let id = algebra.context.payload_view(weight)?;
                let view = algebra.views.get(id as usize).ok_or_else(exhausted)?;
                algebra.context.validate_payload_view(weight, id, view)?;
                let tail = view.tail;
                let tail = tail.map(|tail| capture.intern(Endpoint::Effect(EffectEndpointKey::EffectRow(tail), Polarity::Positive))).transpose()?;
                push(&mut capture.graph.context_views, (weight, id, tail))?;
            }
            if capture.pending.is_empty() && row_cursor == capture.graph.rows.len() { break; }
        }
        let context = &capture.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        let mut attachment_resolved = HashSet::new();
        for bound in &capture.graph.bounds {
            if let Some(relation) = bound.relation {
                if attachment_resolved.contains(&relation) { continue; }
                attachment_resolved.try_reserve(1).map_err(|_| exhausted())?;
                attachment_resolved.insert(relation);
                let start = capture.graph.attachment_bundles.len();
                for bundle in context.relation_bundles(relation) {
                    push(&mut capture.graph.attachment_bundles, (relation, bundle))?;
                }
                let length = capture.graph.attachment_bundles.len() - start;
                if length != 0 {
                    capture.graph.attachment_spans.try_reserve(1).map_err(|_| exhausted())?;
                    capture.graph.attachment_spans.insert(relation, (start, length));
                }
            }
        }
        let scratch = sum(&[
            bytes::<(candidate_context::EvidenceSnapshot, CapturedEvidenceRef)>(capture.evidence_keys.capacity())?,
            bytes::<candidate_context::ContextId>(context_seen.capacity())?,
            bytes::<candidate_context::LocalWeightId>(payload_seen.capacity())?,
            bytes::<candidate_context::ContextId>(context_pending.capacity())?,
            bytes::<candidate_context::LocalWeightId>(payloads.capacity())?,
            bytes::<candidate_context::RelationId>(attachment_resolved.capacity())?,
            bytes::<(Endpoint, usize)>(capture.endpoints.capacity())?,
            bytes::<(RowKey, usize)>(capture.rows.capacity())?,
            bytes::<Endpoint>(capture.pending.capacity())?,
            bytes::<(ComponentKind, Polarity, usize, usize, Option<candidate_context::RelationId>)>(capture.bound_keys.capacity())?,
        ])?;
        if capture.session.batch.candidate_source.scoped_experiment {
            capture.graph.negative_functions.try_reserve(capture.endpoints.len()).map_err(|_| exhausted())?;
            for (&endpoint, &index) in &capture.endpoints {
                if let Endpoint::Value(ValueEndpointKey::NegativeFunction(term), Polarity::Negative) = endpoint {
                    capture.graph.negative_functions.insert(term, index);
                }
            }
        }
        let graph_bytes = capture.graph.bytes()?;
        let Capture {
            graph,
            endpoints,
            rows,
            pending,
            bound_keys,
            evidence_keys,
            ..
        } = capture;
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        state.scratch_bytes = state
            .scratch_bytes
            .checked_add(graph_bytes)
            .and_then(|n| n.checked_add(scratch))
            .ok_or_else(exhausted)?;
        state.capture_peak_bytes = state.capture_peak_bytes.max(state.scratch_bytes);
        let sampled = self.sample_f4_resources(ResourceBoundary::SourceDrafts);
        drop((endpoints, rows, pending, bound_keys, evidence_keys, attachment_resolved, context_seen, payload_seen, context_pending, payloads));
        self.candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .scratch_bytes -= scratch;
        sampled?;
        #[cfg(test)]
        self.candidate_evidence_failure(candidate_context::EvidenceFailurePoint::CaptureScratch)?;
        Ok(graph)
    }
    pub(super) fn execute_candidate_graph_plan(&mut self) -> Result<(), SolveAvailabilityError> {
        // Internal occurrences observe open live roots. All member schedules
        // finish before any graph in the component is captured or published.
        let mut components = Vec::new();
        for component in self.batch.scc_plan().components_in_dependency_first_order() {
            push(&mut components, component.clone())?;
        }
        let component_bytes = vec_bytes(&components)?;
        for component in &components {
            let mut members = Vec::new();
            for member in self
                .batch
                .scc_component_members(&component)
                .map_err(|_| exhausted())?
            {
                push(&mut members, member.clone())?;
            }
            let mut staged = Vec::new();
            staged
                .try_reserve_exact(members.len())
                .map_err(|_| exhausted())?;
            self.candidate_graph
                .as_mut()
                .ok_or_else(exhausted)?
                .orchestration_bytes =
                sum(&[component_bytes, vec_bytes(&members)?, vec_bytes(&staged)?])?;
            {
                let state = &mut self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion;
                state.active_roots.try_reserve(members.len()).map_err(|_| exhausted())?;
                state.active_uses.try_reserve(self.batch.scc_plan().internal_uses(component).map_err(|_| exhausted())?.len()).map_err(|_| exhausted())?;
                for member in &members {
                    let root = &self.batch.definitions[member.ordinal() as usize].root;
                    let position = self.batch.root_component_positions[root].component;
                    state.active_roots.insert(member.clone(), self.live_components[position].ordinal);
                }
                for id in self.batch.scc_plan().internal_uses(component).map_err(|_| exhausted())? { state.active_uses.insert(id.clone()); }
            }
            if self.batch.candidate_source.active {
                for member in &members {
                    let root = self.batch.definitions[member.ordinal() as usize].root.clone();
                    self.execute_candidate_source_root(&root)?;
                }
            } else {
                let internal = self.batch.scc_plan().internal_uses(component).map_err(|_| exhausted())?;
                let mut uses = Vec::new();
                uses.try_reserve_exact(internal.len()).map_err(|_| exhausted())?;
                uses.extend(internal.iter().cloned());
                for id in &uses { self.route_candidate_open_use(id)?; }
            }
            let mut source_frontier = Vec::new();
            if self.batch.candidate_source.scoped_experiment {
                source_frontier.try_reserve_exact(members.len()).map_err(|_| exhausted())?;
                for member in &members {
                    let root = &self.batch.definitions[member.ordinal() as usize].root;
                    source_frontier.push(*self.batch.candidate_source.definition_regions.get(root).ok_or_else(exhausted)?);
                }
            }
            for member in &members {
                let position = member.ordinal() as usize;
                let root = self.batch.definitions[position].root.clone();
                let component = self.batch.root_component_positions[&root].component;
                staged.push((
                    position,
                    self.capture_candidate_graph_owned(self.live_components[component].ordinal, 0, &source_frontier)?,
                ));
            }
            // Every member graph is valid before any becomes visible to uses.
            let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
            let addition = staged.iter().try_fold(0usize, |total, (_, graph)| {
                total.checked_add(graph.bytes()?).ok_or_else(exhausted)
            })?;
            let retained = state
                .retained_bytes
                .checked_add(addition)
                .ok_or_else(exhausted)?;
            for (position, graph) in staged {
                state.graphs[position] = Some(graph);
            }
            state.retained_bytes = retained;
            state.scratch_bytes = 0;
            state.intrusion.active_roots.clear();
            state.intrusion.active_uses.clear();
            self.sample_f4_resources(ResourceBoundary::AllDrafts)?;
            if self.batch.candidate_source.active { continue; }
            let count = self
                .batch
                .scc_component_incoming_uses(&component)
                .map_err(|_| exhausted())?
                .len();
            for i in 0..count {
                let id = self
                    .batch
                    .scc_component_incoming_uses(&component)
                    .map_err(|_| exhausted())?[i]
                    .clone();
                self.route_incoming(&id)?;
            }
        }
        self.candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .orchestration_bytes = 0;
        Ok(())
    }
    pub(super) fn route_candidate_open_use(&mut self, id: &DefinitionUseId) -> Result<usize, SolveAvailabilityError> {
        let record = Self::validated_route_use(&self.batch, id)?.clone();
        let state = &self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion;
        if !state.active_uses.contains(id) || !state.active_roots.contains_key(&record.parent) || !state.active_roots.contains_key(&record.target) { return Err(exhausted()); }
        // The original occurrence and cause enter the ordinary route owner;
        // the fresh occurrence row remains distinct from the live target root.
        self.route_internal(id)
    }

    pub(super) fn route_candidate_graph(
        &mut self,
        id: &DefinitionUseId,
        record: DefinitionUse,
    ) -> Result<usize, SolveAvailabilityError> {
        let target = record.target.ordinal() as usize;
        let stored = self.candidate_graph.as_ref()
            .and_then(|state| state.graphs[target].as_ref())
            .ok_or_else(exhausted)?;
        let (root, boundary) = (stored.live_root, stored.boundary);
        let mut source_frontier = Vec::new(); source_frontier.try_reserve_exact(stored.source_frontier.len()).map_err(|_| exhausted())?;
        source_frontier.extend_from_slice(&stored.source_frontier);
        let frontier_scratch = bytes::<candidate_source::SourceRegionId>(source_frontier.capacity())?;
        self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.scope_inventory.note_scratch(frontier_scratch);
        let entry_scratch = self.candidate_graph.as_ref().unwrap().scratch_bytes;
        let result = (|| {
            let graph = if source_frontier.is_empty() { self.capture_candidate_graph(root, boundary)? }
                else { self.capture_candidate_graph_owned(root, boundary, &source_frontier)? };
            self.instantiate_candidate_graph(id, &record, graph, entry_scratch)
        })();
        self.candidate_graph.as_mut().ok_or_else(exhausted)?.scratch_bytes = entry_scratch;
        result
    }
    pub(super) fn freshen_candidate_graph(
        &mut self, graph: &Graph, use_level: u32,
        occurrence: &ConstraintOccurrenceId, cause: &CauseId,
    ) -> Result<(Term, Vec<RowKey>), SolveAvailabilityError> {
        let entry = self.candidate_graph.as_ref().ok_or_else(exhausted)?.scratch_bytes;
        let result = (|| {
            let caller = self.batch.candidate_source.occurrence_regions.get(occurrence.occurrence()).copied();
            let fresh = self.prepare_candidate_fresh_use(graph, use_level, caller)?;
            for index in 0..graph.bounds.len() {
                let restoration = self.begin_candidate_fresh_bound(graph, &fresh, index, occurrence, cause)?;
                self.candidate_drive_bound_restoration(restoration)?;
            }
            #[cfg(test)]
            if let Some(census) = &mut self.candidate_graph.as_mut().unwrap().local_use_census {
                if census.requested.contains(occurrence.occurrence()) {
                    census.module_uses.push((occurrence.occurrence().clone(), fresh.context_use));
                }
            }
            Ok((fresh.terms[graph.root].ok_or_else(exhausted)?, fresh.rows))
        })();
        self.candidate_graph.as_mut().ok_or_else(exhausted)?.scratch_bytes = entry;
        result
    }
    fn prepare_candidate_fresh_use(
        &mut self, graph: &Graph, use_level: u32, caller: Option<candidate_source::SourceRegionId>,
    ) -> Result<FreshUse, SolveAvailabilityError> {
        let context_use = self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra.context.begin_use()?;
        let scope_remap = if self.batch.candidate_source.scoped_experiment {
            self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.scope_inventory.fresh(&graph.owned_regions, caller.ok_or_else(exhausted)?, graph.nodes.len(), graph.bounds.len())?
        } else { candidate_source::ScopeRemap::default() };
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(scope_remap.bytes()?).ok_or_else(exhausted)?;
        let mut canonical_rows = HashMap::new();
        canonical_rows.try_reserve(graph.rows.len()).map_err(|_| exhausted())?;
        let mut rows = Vec::new();
        rows.try_reserve_exact(graph.rows.len())
            .map_err(|_| exhausted())?;
        let mut terms = Vec::new();
        terms
            .try_reserve_exact(graph.nodes.len())
            .map_err(|_| exhausted())?;
        terms.resize(graph.nodes.len(), None);
        let mut work = Vec::new();
        work.try_reserve_exact(graph.nodes.len().checked_mul(5).ok_or_else(exhausted)?)
            .map_err(|_| exhausted())?;
        let scratch = sum(&[
            bytes::<RowKey>(rows.capacity())?,
            bytes::<(RowKey, RowKey)>(canonical_rows.capacity())?,
            bytes::<Option<Term>>(terms.capacity())?,
            bytes::<(usize, bool)>(work.capacity())?,
        ])?;
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        state.scratch_bytes = state.scratch_bytes.checked_add(scratch).ok_or_else(exhausted)?;
        state.use_peak_bytes = state.use_peak_bytes.max(state.scratch_bytes);
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        for row in &graph.rows {
            let source = self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.rep(row.key);
            let (level, metadata) = match source { RowKey::Value(i) => (self.value_levels[i as usize], self.value_metadata[i as usize]), RowKey::Effect(i) => (self.effect_levels[i as usize], self.effect_metadata[i as usize]) };
            let key = if let Some(&existing) = canonical_rows.get(&source) { existing }
            else {
                let key = if row.local && level > graph.boundary && !metadata.non_generic {
                    match source { RowKey::Value(_) => RowKey::Value(self.fresh_value_at_level(use_level)?), RowKey::Effect(_) => RowKey::Effect(self.fresh_effect_at_level(use_level)?) }
                } else { source };
                canonical_rows.insert(source, key);
                key
            };
            rows.push(key);
        }
        let mut bundle_remap = HashMap::new();
        bundle_remap.try_reserve(graph.attachment_bundles.len()).map_err(|_| exhausted())?;
        let bundle_scratch = bytes::<(candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId)>(bundle_remap.capacity())?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(bundle_scratch).ok_or_else(exhausted)?;
        for &(_, old) in &graph.attachment_bundles {
            if bundle_remap.contains_key(&old) { continue; }
            let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
            let original = &state.bundles[old.0];
            let mut sets = Vec::new();
            sets.try_reserve_exact(original.sets.len()).map_err(|_| exhausted())?;
            sets.extend_from_slice(&original.sets);
            let bundle = candidate_context::AttachmentBundle { occurrence: original.occurrence.clone(), sets };
            let fresh = state.retain_bundle(bundle, false)?;
            bundle_remap.insert(old, fresh);
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        let mut view_remap = HashMap::new();
        view_remap.try_reserve(graph.nodes.len().checked_add(graph.context_views.len()).ok_or_else(exhausted)?).map_err(|_| exhausted())?;
        let view_scratch = bytes::<((u32, Option<u32>), u32)>(view_remap.capacity())?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(view_scratch).ok_or_else(exhausted)?;
        let mut effect_operands = HashMap::new();
        effect_operands.try_reserve(graph.nodes.len()).map_err(|_| exhausted())?;
        let operand_scratch = bytes::<(usize, EffectEndpointKey)>(effect_operands.capacity())?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(operand_scratch).ok_or_else(exhausted)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        for (index, node) in graph.nodes.iter().enumerate() {
            if let Node::EffectOperand { endpoint, tail, .. } = *node {
                let endpoint = match endpoint {
                    EffectEndpointKey::Allowance(id) | EffectEndpointKey::Support(id) => {
                        let tail = tail.map(|index| match graph.nodes[index] {
                            Node::Row { row, .. } => match rows[row] { RowKey::Effect(row) => Ok(row), _ => Err(exhausted()) },
                            _ => Err(exhausted()),
                        }).transpose()?;
                        { let copy = self.candidate_remapped_effect_view(id, tail, &mut view_remap)?;
                            if matches!(endpoint, EffectEndpointKey::Support(_)) { EffectEndpointKey::Support(copy) } else { EffectEndpointKey::Allowance(copy) } }
                    }
                    EffectEndpointKey::AnnotationMember(id, member) => {
                        let tail = tail.map(|index| match graph.nodes[index] {
                            Node::Row { row, .. } => match rows[row] { RowKey::Effect(row) => Ok(row), _ => Err(exhausted()) },
                            _ => Err(exhausted()),
                        }).transpose()?;
                        EffectEndpointKey::AnnotationMember(self.candidate_remapped_effect_view(id, tail, &mut view_remap)?, member)
                    }
                    EffectEndpointKey::Contribution(id) => {
                        let atom = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.contributions[id as usize];
                        let (effect, origin) = (atom.effect.clone(), atom.origin.clone());
                        self.candidate_effect_contribution(effect, origin)?
                    }
                    _ => return Err(exhausted()),
                };
                effect_operands.insert(index, endpoint);
            }
        }
        let mut weight_remap = HashMap::new();
        weight_remap.try_reserve(graph.context_views.len()).map_err(|_| exhausted())?;
        let mut roots = Vec::new();
        roots.try_reserve_exact(graph.bounds.len()).map_err(|_| exhausted())?;
        for bound in &graph.bounds {
            if let Some(parent) = bound.relation {
                roots.push(self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.relation_context(parent)?);
            }
        }
        let mut context_remap = HashMap::new();
        let extra = sum(&[
            bytes::<(candidate_context::LocalWeightId, candidate_context::LocalWeightId)>(weight_remap.capacity())?,
            bytes::<candidate_context::ContextId>(roots.capacity())?,
        ])?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(extra).ok_or_else(exhausted)?;
        for &(weight, id, tail) in &graph.context_views {
            let tail = tail.map(|index| match graph.nodes.get(index) {
                Some(Node::Row { row, .. }) => match rows[*row] { RowKey::Effect(row) => Ok(row), _ => Err(exhausted()) },
                _ => Err(exhausted()),
            }).transpose()?;
            let algebra = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            let source = algebra.views.get(id as usize).ok_or_else(exhausted)?;
            algebra.context.validate_payload_view(weight, id, source)?;
            let copy = self.candidate_remapped_effect_view(id, tail, &mut view_remap)?;
            let algebra = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            let view = algebra.views.get(copy as usize).ok_or_else(exhausted)?;
            let mapped = view.source_weight.ok_or_else(exhausted)?;
            algebra.context.validate_payload_view(mapped, copy, view)?;
            weight_remap.insert(weight, mapped);
        }
        {
            let state = self.candidate_graph.as_mut().unwrap();
            state.intrusion.effect_algebra.context.rename_fresh_contexts(&roots, &weight_remap, &mut context_remap, &mut state.scratch_bytes, &mut state.use_peak_bytes)?;
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        // Structural Function nodes form a DAG. Cycles run through rows,
        // whose preallocated identities terminate structural reconstruction.
        for root in 0..graph.nodes.len() {
            if terms[root].is_some() {
                continue;
            }
            push(&mut work, (root, false))?;
            while let Some((index, finish)) = work.pop() {
                if terms[index].is_some() {
                    continue;
                }
                let term = match graph.nodes[index] {
                    Node::EffectOperand { .. } => continue,
                    Node::Leaf(atom) => match atom {
                        Atom::Bottom => self.positive_bottom_term()?,
                        Atom::Top => self.negative_top_term()?,
                        Atom::NegativeBottom => self.negative_bottom_term()?,
                        Atom::IntPositive => self.batch.collected_leaf_term(Leaf::IntPositive),
                        Atom::UnitPositive => self.batch.collected_leaf_term(Leaf::UnitPositive),
                        Atom::BoolPositive => self.batch.collected_leaf_term(Leaf::BoolPositive),
                        Atom::StrPositive => self.batch.collected_leaf_term(Leaf::StrPositive),
                        Atom::IntNegative => self.batch.collected_leaf_term(Leaf::IntNegative),
                        Atom::UnitNegative => self.batch.collected_leaf_term(Leaf::UnitNegative),
                        Atom::BoolNegative => self.batch.collected_leaf_term(Leaf::BoolNegative),
                        Atom::StrNegative => self.batch.collected_leaf_term(Leaf::StrNegative),
                        Atom::EffectBottom => {
                            self.batch.collected_leaf_term(Leaf::EffectBottomPositive)
                        }
                        Atom::EmptyEffect => {
                            self.batch.collected_leaf_term(Leaf::EmptyEffectNegative)
                        }
                    },
                    Node::Row { row, polarity } => match rows[row] {
                        RowKey::Value(i) => self.live_value_term(polarity, i)?,
                        RowKey::Effect(i) => self.live_effect_term(polarity, i)?,
                    },
                    Node::Function { polarity, children } => {
                        if !finish {
                            push(&mut work, (index, true))?;
                            for child in children.into_iter().rev() {
                                if terms[child].is_none() {
                                    push(&mut work, (child, false))?;
                                }
                            }
                            continue;
                        }
                        let [a, ae, re, r] = children
                            .map(|child| terms[child].expect("validated structural dependency"));
                        if polarity == Polarity::Positive {
                            self.positive_function_term(a, ae, re, r)?
                        } else {
                            self.negative_function_term(a, ae, re, r)?
                        }
                    }
                };
                terms[index] = Some(term);
            }
        }
        let mut scoped_relations = HashMap::new();
        if self.batch.candidate_source.scoped_experiment {
            scoped_relations.try_reserve(graph.bounds.len()).map_err(|_| exhausted())?;
            for bound in &graph.bounds {
                let Some(parent) = bound.relation else { continue; };
                if scoped_relations.contains_key(&parent) { continue; }
                let context = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                let mut flow = context.scoped_flow(parent)?;
                if flow.transformer != 0 {
                    context.prepare_scope_remap(flow.transformer)?;
                    let renamed = context.scope_transformer(flow.transformer)?.remap(
                        |id| scope_remap.scopes.get(&id).copied().unwrap_or(id),
                        |id| scope_remap.inputs.get(&id).copied().unwrap_or(id))?;
                    flow.transformer = context.intern_scope(renamed)?;
                }
                if let Some(demand) = &mut flow.demand {
                    let local = scope_remap.inputs.contains_key(&demand.input);
                    demand.output_scope = scope_remap.scopes.get(&demand.output_scope).copied().unwrap_or(demand.output_scope);
                    demand.input = scope_remap.inputs.get(&demand.input).copied().unwrap_or(demand.input);
                    let index = graph.negative_functions.get(&demand.root).copied().ok_or(SolveAvailabilityError::ReceiptMismatch)?;
                    demand.root = terms[index].ok_or_else(exhausted)?;
                    if local { demand.use_instance = context_use; }
                }
                scoped_relations.insert(parent, flow);
            }
        }
        let extra_scoped = bytes::<(candidate_context::RelationId, candidate_context::ScopedFlow)>(scoped_relations.capacity())?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(extra_scoped).ok_or_else(exhausted)?;
        let mut evidence_remap = Vec::new();
        let reserve_count = graph.bound_evidence.len();
        #[cfg(test)]
        let reserve_count = if self.candidate_graph.as_ref().unwrap().evidence_failure == Some(candidate_context::EvidenceFailurePoint::ImportReserve) {
            // Exercise the real capacity-overflow error without allocating.
            usize::MAX
        } else { reserve_count };
        let reserved = evidence_remap.try_reserve_exact(reserve_count);
        let evidence_scratch = bytes::<candidate_context::EvidenceSnapshotId>(evidence_remap.capacity())?;
        let state = self.candidate_graph.as_mut().unwrap();
        #[cfg(test)]
        { state.import_evidence_peak_capacity = state.import_evidence_peak_capacity.max(evidence_remap.capacity()); }
        state.scratch_bytes = state.scratch_bytes.checked_add(evidence_scratch).ok_or_else(exhausted)?;
        state.use_peak_bytes = state.use_peak_bytes.max(state.scratch_bytes);
        let reservation = reserved.map_err(|_| exhausted());
        let sampled = self.sample_f4_resources(ResourceBoundary::IncomingRoute);
        if let Err(error) = reservation {
            #[cfg(test)]
            {
                let state = self.candidate_graph.as_mut().unwrap();
                state.import_failure_sample = Some((state.scratch_bytes, self.resource_ledger.inference_session_retained_bytes, sampled.is_ok()));
                if state.evidence_failure == Some(candidate_context::EvidenceFailurePoint::ImportReserve) {
                    state.evidence_failure = None;
                    state.failed_evidence_point = Some(candidate_context::EvidenceFailurePoint::ImportReserve);
                    state.failed_evidence_sample = Some((candidate_context::EvidenceFailurePoint::ImportReserve, state.scratch_bytes, self.resource_ledger.inference_session_retained_bytes));
                    state.failed_import_count = Some(evidence_remap.len());
                }
            }
            return Err(error);
        }
        sampled?;
        let imported = (|| {
            for &snapshot in &graph.bound_evidence {
                let id = self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.import_evidence(snapshot)?;
                evidence_remap.push(id);
                #[cfg(test)]
                if evidence_remap.len() == 1 && evidence_remap.len() < graph.bound_evidence.len()
                    && self.candidate_graph.as_ref().unwrap().evidence_failure == Some(candidate_context::EvidenceFailurePoint::ImportedSnapshot) {
                    self.candidate_graph.as_mut().unwrap().failed_import_count = Some(evidence_remap.len());
                    self.candidate_evidence_failure(candidate_context::EvidenceFailurePoint::ImportedSnapshot)?;
                }
            }
            Ok::<(), SolveAvailabilityError>(())
        })();
        if let Err(error) = imported {
            // The remap is still alive and charged at this error sample.
            let sampled = self.sample_f4_resources(ResourceBoundary::IncomingRoute);
            #[cfg(test)]
            {
                let state = self.candidate_graph.as_mut().unwrap();
                state.import_failure_sample = Some((state.scratch_bytes, self.resource_ledger.inference_session_retained_bytes, sampled.is_ok()));
            }
            let _ = sampled;
            return Err(error);
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(FreshUse { scope_remap, scoped_relations, context_use, rows, terms, effect_operands, bundle_remap, context_remap, evidence_remap })
    }
    fn begin_candidate_fresh_bound(
        &mut self, graph: &Graph, fresh: &FreshUse, index: usize,
        occurrence: &ConstraintOccurrenceId, cause: &CauseId,
    ) -> Result<candidate_context::ReplayOperationId, SolveAvailabilityError> {
        // Preserve captured owner orientation and construct transport only once,
        // immediately before this bound's physical admission.
        let bound = graph.bounds.get(index).ok_or_else(exhausted)?;
        let (lower, upper) = match bound.kind {
            ComponentKind::Value => {
                let lower = fresh.terms[bound.lower].ok_or_else(exhausted)?;
                let upper = fresh.terms[bound.upper].ok_or_else(exhausted)?;
                (ExtrusionEndpoint::Value(self.value_endpoint(lower, Polarity::Positive)),
                 ExtrusionEndpoint::Value(self.value_endpoint(upper, Polarity::Negative)))
            }
            ComponentKind::Effect => {
                let lower = if let Some(&operand) = fresh.effect_operands.get(&bound.lower) { operand }
                    else { self.effect_endpoint(fresh.terms[bound.lower].ok_or_else(exhausted)?, Polarity::Positive) };
                let upper = if let Some(&operand) = fresh.effect_operands.get(&bound.upper) { operand }
                    else { self.effect_endpoint(fresh.terms[bound.upper].ok_or_else(exhausted)?, Polarity::Negative) };
                (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper))
            }
        };
        let (owner, item) = if bound.side == Polarity::Positive {
            (upper, lower)
        } else {
            (lower, upper)
        };
        let mut mapped_relation = None;
        if let Some(parent) = bound.relation {
            // One reconstruction route shares all captured relation inputs.
            // Independent uses retain independent transport origins even
            // when an older, nongeneric coordinate is shared.
            let root = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.relation_context(parent)?;
            let child = self.candidate_context_fresh_transport_scoped(parent, candidate_effect::BoundKey(owner, bound.side, item),
                fresh.context_use, *fresh.context_remap.get(&root).ok_or_else(exhausted)?, bound.source_bound,
                fresh.scoped_relations.get(&parent).copied())?;
            mapped_relation = Some(child);
            if let Some(&(start, length)) = graph.attachment_spans.get(&parent) {
                for &(_, old) in &graph.attachment_bundles[start..start + length] {
                    self.candidate_context_fresh_bundle(child, fresh.bundle_remap[&old])?;
                }
            }
        }
        let antecedent = *fresh.evidence_remap.get(bound.evidence.0).ok_or_else(exhausted)?;
        self.candidate_begin_bound_restoration(owner, bound.side, item, occurrence, cause,
            candidate_context::BoundAdmissionCause::FreshUse { antecedent, use_origin: fresh.context_use,
                source_bound: bound.source_bound, mapped_relation })
    }
    fn instantiate_candidate_graph(
        &mut self,
        id: &DefinitionUseId,
        record: &DefinitionUse,
        graph: Graph,
        entry_scratch: usize,
    ) -> Result<usize, SolveAvailabilityError> {
        let occurrence = ConstraintOccurrenceId::new(record.occurrence.clone(), 0);
        let cause = CauseId::for_occurrence(occurrence.clone());
        let (lower, rows) = self.freshen_candidate_graph(&graph, record.use_level, &occurrence, &cause)?;
        let upper = self.batch.component_term_at(record.use_value_component);
        let key = CanonicalValuePairKey {
            lower: self.value_endpoint(lower, Polarity::Positive),
            upper: ValueEndpointKey::ValueRow(
                self.live_components[record.use_value_component].ordinal,
            ),
        };
        // Capture allocation and accounting failure precede route publication.
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        let old_capacity = state.routes.capacity();
        state.routes.try_reserve(1).map_err(|_| exhausted())?;
        let growth = bytes::<FreshRoute>(state.routes.capacity() - old_capacity)?;
        let retained = sum(&[state.retained_bytes, growth, graph.bytes()?,
            bytes::<RowKey>(rows.capacity())?])?;
        state.retained_bytes = state
            .retained_bytes
            .checked_add(growth)
            .ok_or_else(exhausted)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        let transitions = self.route(
            id,
            record,
            lower,
            upper,
            key,
            RoutedUseKind::IncomingStructured,
        )?;
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        state.routes.push(FreshRoute {
            use_id: id.clone(),
            graph,
            rows,
        });
        state.retained_bytes = retained;
        state.scratch_bytes = entry_scratch;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(transitions)
    }
    pub(super) fn install_candidate_local(&mut self, slot: usize, endpoint: shadow_apply::CandidateEndpoint, boundary: u32) -> Result<(), SolveAvailabilityError> {
        let term = self.candidate_endpoint(endpoint, Polarity::Positive)?;
        self.install_candidate_local_term(slot, term, boundary)
    }
    pub(super) fn install_candidate_local_term(&mut self, slot: usize, term: Term, boundary: u32) -> Result<(), SolveAvailabilityError> {
        let ValueEndpointKey::ValueRow(root) = self.value_endpoint(term, Polarity::Positive) else { return Err(exhausted()); };
        let id = self.batch.candidate_source.locals.get(slot).ok_or_else(exhausted)?.clone();
        if self.candidate_graph.as_ref().and_then(|state| state.locals.get(slot)).is_none_or(Option::is_some) {
            return Err(exhausted());
        }
        #[cfg(feature = "shadow-apply-candidate")]
        if let Some(journal) = &mut self.route_journal {
            journal.candidate_local_slots.try_reserve(1).map_err(|_| exhausted())?;
            journal.candidate_local_slots.push(slot);
        }
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        let destination = state.locals.get_mut(slot).ok_or_else(exhausted)?;
        let capture_region = self.batch.candidate_source.local_regions.get(&id).copied();
        *destination = Some(LocalScheme { capture_region, id, root, boundary });
        self.sample_f4_resources(ResourceBoundary::SourceDrafts)?;
        Ok(())
    }
    pub(super) fn admit_candidate_value_link(&mut self, source: &HirOccurrenceId, slot: u8, lower: Term, upper: Term) -> Result<(), SolveAvailabilityError> {
        let id = ConstraintOccurrenceId::new(source.clone(), slot);
        let cause = CauseId::for_occurrence(id.clone());
        self.store.admit_and_record_provenance(&ConstraintOccurrence { id: id.clone(), cause: cause.clone(), lower, upper })
            .map_err(SolveAvailabilityError::from)?;
        let key = CanonicalValuePairKey { lower: self.value_endpoint(lower, Polarity::Positive), upper: self.value_endpoint(upper, Polarity::Negative) };
        self.constrain_live_value(key, &id, &cause)?;
        Ok(())
    }
    pub(super) fn route_candidate_local(&mut self, slot: usize, occurrence: &HirOccurrenceId, value: usize, level: u32) -> Result<(), SolveAvailabilityError> {
        match self.route_candidate_local_run(slot, occurrence, value, level, None)? {
            LocalRun::Complete => Ok(()),
            LocalRun::Paused => unreachable!("production local routing cannot inject a pause"),
        }
    }
    // A pause budget is supplied only by the enclosed test script. This is not
    // authenticated support, incidence deferral, or a production suspension API.
    fn route_candidate_local_run(&mut self, slot: usize, occurrence: &HirOccurrenceId, value: usize, level: u32,
        pause_after: Option<usize>) -> Result<LocalRun, SolveAvailabilityError> {
        #[cfg(not(test))]
        assert!(pause_after.is_none());
        self.incoming_route_accounting_active = true;
        self.route_attempt_physical_change = false;
        self.incoming_route_event_sample_failed = false;
        let result = self.begin_route_transaction().and_then(|()| self.finish_route_transaction_with_candidate_accounting(|session| {
            if session.candidate_graph.as_ref().ok_or_else(exhausted)?.local_use.is_empty() {
                let (root, boundary, local, capture_region) = {
                    let scheme = session.candidate_graph.as_ref().and_then(|state| state.locals.get(slot)).and_then(Option::as_ref).ok_or_else(exhausted)?;
                    (scheme.root, scheme.boundary, scheme.id.clone(), scheme.capture_region)
                };
                let state = session.candidate_graph.as_mut().unwrap();
                let old_capacity = state.local_use.capacity();
                state.local_use.try_reserve(1).map_err(|_| exhausted())?;
                state.retained_bytes = state.retained_bytes.checked_add(bytes::<LocalUse>(state.local_use.capacity() - old_capacity)?).ok_or_else(exhausted)?;
                session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
                // Capture and construction remain atomic; no child has started.
                let frontier = capture_region.as_slice();
                let graph = session.capture_candidate_graph_owned(root, boundary, frontier)?;
                let caller = session.batch.candidate_source.occurrence_regions.get(occurrence).copied();
                let fresh = session.prepare_candidate_fresh_use(&graph, level, caller)?;
                let retained = sum(&[session.candidate_graph.as_ref().unwrap().retained_bytes, graph.bytes()?, fresh.bytes()?])?;
                let state = session.candidate_graph.as_mut().unwrap();
                state.local_use.push(LocalUse { slot, local, occurrence: occurrence.clone(), value, level,
                    graph, fresh, cursor: LocalUseCursor::default() });
                state.scratch_bytes = 0;
                state.retained_bytes = retained;
                session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            }
            {
                let frame = session.candidate_graph.as_ref().unwrap().local_use.last().ok_or_else(exhausted)?;
                if frame.slot != slot || &frame.occurrence != occurrence || frame.value != value || frame.level != level {
                    return Err(exhausted());
                }
            }
            let mut steps = 0;
            loop {
                // Ownership is transferred temporarily during an atomic owner
                // step and restored before every fallible return or pause.
                let mut frame = session.candidate_graph.as_mut().unwrap().local_use.pop().unwrap();
                let result = session.step_candidate_local_use(&mut frame);
                let complete = frame.cursor.complete;
                session.candidate_graph.as_mut().unwrap().local_use.push(frame);
                result?;
                if session.incoming_route_event_sample_failed { return Err(exhausted()); }
                if complete { return Ok(LocalRun::Complete); }
                steps += 1;
                if pause_after == Some(steps) { return Ok(LocalRun::Paused); }
            }
        }, true));
        self.incoming_route_accounting_active = false;
        self.route_attempt_physical_change = false;
        self.incoming_route_event_sample_failed = false;
        if let Some(state) = &mut self.candidate_graph { state.scratch_bytes = 0; }
        result
    }
    #[cfg(test)]
    pub(super) fn candidate_test_local_script(&mut self, script: &[LocalScriptStep]) -> Result<Vec<LocalScriptObservation>, SolveAvailabilityError> {
        let source = self.candidate_graph.as_ref().and_then(|state| state.source).ok_or_else(exhausted)?;
        if source.stage != candidate_source::Stage::Execute { return Err(exhausted()); }
        let actions = match source.schedule {
            candidate_source::Schedule::Loose => &self.batch.candidate_source.loose,
            candidate_source::Schedule::Root(index) => {
                let root = &self.batch.definitions.get(index).ok_or_else(exhausted)?.root;
                self.batch.candidate_source.schedules.get(root).ok_or_else(exhausted)?
            }
        };
        let Some(candidate_source::Action::Local { slot, occurrence, value, level }) = actions.get(source.next).cloned() else { return Err(exhausted()); };
        let mut observations = Vec::new();
        observations.try_reserve_exact(script.len()).map_err(|_| exhausted())?;
        for step in script {
            match step {
                LocalScriptStep::DriveOne => {
                    if self.route_candidate_local_run(slot, &occurrence, value, level, Some(1))? != LocalRun::Paused { return Err(exhausted()); }
                }
                LocalScriptStep::Idle => {
                    if self.candidate_graph.as_ref().unwrap().local_use.is_empty() { return Err(exhausted()); }
                }
                LocalScriptStep::FailOne => {
                    let result = self.begin_route_transaction().and_then(|()| self.finish_route_transaction_with_candidate_accounting(|session| {
                        let mut frame = session.candidate_graph.as_mut().unwrap().local_use.pop().ok_or_else(exhausted)?;
                        let result = session.step_candidate_local_use(&mut frame);
                        session.candidate_graph.as_mut().unwrap().local_use.push(frame);
                        result?;
                        Err::<(), _>(exhausted())
                    }, true));
                    if result != Err(exhausted()) { return Err(exhausted()); }
                }
                LocalScriptStep::Complete => {
                    if self.route_candidate_local_run(slot, &occurrence, value, level, None)? != LocalRun::Complete { return Err(exhausted()); }
                    self.candidate_graph.as_mut().unwrap().source.as_mut().unwrap().next += 1;
                }
            }
            // Test-only enumeration checks incremental frame/publication charges
            // after both commit and rollback; production has no route rescan.
            let graph = self.candidate_graph.as_mut().unwrap();
            let tracked = graph.retained_bytes;
            graph.refresh_bytes()?;
            assert_eq!(graph.retained_bytes, tracked, "local continuation retained accounting");
            let context = &graph.intrusion.effect_algebra.context;
            assert_eq!(context.bytes()?, context.enumerated_bytes(), "owner operation and undo accounting");
            if !context.typed_drains.is_empty() || !self.typed_worklist.is_empty() { return Err(exhausted()); }
            let frame = graph.local_use.last();
            let restoration = frame.and_then(|frame| frame.cursor.restoration)
                .map(|id| context.restoration(id).cloned()).transpose()?;
            observations.push(LocalScriptObservation { source_next: graph.source.unwrap().next,
                use_origin: frame.map(|frame| frame.fresh.context_use), cursor: frame.map(|frame| frame.cursor),
                restoration, checkpoint: context.checkpoint(), retained_bytes: graph.retained_bytes,
                routes: graph.local_routes.len(), facts: self.store.facts.len(), typed_drains: context.typed_drains.len() });
        }
        Ok(observations)
    }
    #[cfg(test)]
    pub(super) fn candidate_test_retained_local_step(&mut self, fail_after: bool) -> Result<(), SolveAvailabilityError> {
        if self.route_journal.is_some() { return Err(exhausted()); }
        let state = self.candidate_graph.as_ref().ok_or_else(exhausted)?;
        if state.local_use.len() != 1 || state.local_use[0].cursor.complete { return Err(exhausted()); }
        self.begin_route_transaction_for(RoutePurpose::RetainedResume)?;
        self.finish_route_transaction(|session| {
            let restoration = session.candidate_graph.as_ref().unwrap().local_use[0].cursor.restoration;
            if let Some(restoration) = restoration {
                let state = session.candidate_graph.as_ref().unwrap();
                let operation = state.intrusion.effect_algebra.context.restoration(restoration)?;
                let occurrence = ConstraintOccurrenceId::new(state.local_use[0].occurrence.clone(), 0);
                if operation.occurrence != occurrence || operation.cause != CauseId::for_occurrence(occurrence) { return Err(exhausted()); }
                // The Local remains in its owner vector throughout child execution
                // and receipt delivery, including all fallible returns.
                if session.candidate_step_bound_restoration_child(restoration, true)?.is_some() {
                    let frame = &mut session.candidate_graph.as_mut().unwrap().local_use[0];
                    frame.cursor.restoration = None;
                    frame.cursor.next_bound += 1;
                }
            } else {
                if !session.typed_worklist.is_empty()
                    || !session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.typed_drains.is_empty() {
                    return Err(exhausted());
                }
                let mut frame = session.candidate_graph.as_mut().unwrap().local_use.pop().unwrap();
                let result = session.step_candidate_local_use(&mut frame);
                session.candidate_graph.as_mut().unwrap().local_use.push(frame);
                result?;
            }
            if fail_after { return Err(exhausted()); }
            Ok(())
        })
    }
    fn step_candidate_local_use(&mut self, frame: &mut LocalUse) -> Result<(), SolveAvailabilityError> {
        if frame.cursor.complete { return Err(exhausted()); }
        let id = ConstraintOccurrenceId::new(frame.occurrence.clone(), 0);
        let cause = CauseId::for_occurrence(id.clone());
        if let Some(restoration) = frame.cursor.restoration {
            if self.candidate_step_bound_restoration(restoration)?.is_some() {
                frame.cursor.restoration = None;
                frame.cursor.next_bound += 1;
            }
            return Ok(());
        }
        if frame.cursor.next_bound < frame.graph.bounds.len() {
            let restoration = self.begin_candidate_fresh_bound(&frame.graph, &frame.fresh, frame.cursor.next_bound, &id, &cause)?;
            frame.cursor.restoration = Some(restoration);
            return Ok(());
        }
        let lower = frame.fresh.terms[frame.graph.root].ok_or_else(exhausted)?;
        let upper = self.batch.component_term_at(frame.value);
        self.admit_candidate_value_link(&frame.occurrence, 0, lower, upper)?;
        let state = self.candidate_graph.as_mut().unwrap();
        let old = state.local_routes.capacity();
        if state.local_routes.len() == old {
            // Keep the original allocation in undo. Moving the existing entries
            // avoids cloning their graphs/rows, and rollback can move them back
            // without allocating. Geometric growth keeps publication amortized.
            let capacity = old.checked_mul(2).ok_or_else(exhausted)?.max(4);
            let mut replacement = Vec::new();
            replacement.try_reserve_exact(capacity).map_err(|_| exhausted())?;
            let retained_bytes = state.retained_bytes.checked_add(
                bytes::<LocalFreshRoute>(replacement.capacity() - old)?).ok_or_else(exhausted)?;
            let journal = self.route_journal.as_mut().ok_or_else(exhausted)?;
            if journal.candidate_local_routes_allocation.is_some() { return Err(exhausted()); }
            replacement.append(&mut state.local_routes);
            journal.candidate_local_routes_allocation = Some(std::mem::replace(&mut state.local_routes, replacement));
            state.retained_bytes = retained_bytes;
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        frame.cursor.complete = true;
        Ok(())
    }
}

#[cfg(test)]
mod authentic_demand_capture_tests {
    use super::*;

    #[test]
    fn structural_bound_scoped_payload_authentic_capture_uses_shared_reconstruction() {
        let text: Arc<yu_syntax::SourceText> = Arc::from(
            "my outer z = { my local h x = h z; local }\nmy first = outer 0\nmy second = outer 1",
        );
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("latent-demand", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true).unwrap(),
        ).unwrap();
        session.execute().unwrap();
        let owner = session.batch.hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "outer" => Some(binding.definition_root().clone()),
            _ => None,
        }).unwrap();
        let source = session.batch.hir.local_source(&owner).unwrap().unwrap();
        let initializer = source.bindings().iter().find(|binding| binding.spelling.as_ref() == "local").unwrap().id.clone();
        let original_call = session.batch.candidate_calls.calls.iter().enumerate().find_map(|(index, call)| {
            if call.owner != owner { return None; }
            let name = session.batch.candidate_calls.names.get(call.formal_name?)?;
            let registration = &session.batch.candidate_calls.formals[name.registration];
            let lambda = &source.expressions()[registration.lambda];
            let yu_hir::shadow::LocalSourceForm::Lambda { parameter, .. } = &lambda.form else { return None; };
            (parameter.spelling.as_ref() == "h").then_some(index)
        }).unwrap();
        let local = session.candidate_graph.as_ref().unwrap().locals.iter().flatten().find(|local| local.id == initializer).unwrap();
        let (root, boundary, capture_region) = (local.root, local.boundary, local.capture_region);
        let graph = session.capture_candidate_graph_owned(root, boundary, capture_region.as_slice()).unwrap();
        let context = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        // Strict latent-only reachability is not established for this source.
        // This control selects an authentic local-formal demand and its real scheme.
        let demands: Vec<_> = graph.bounds.iter().filter_map(|bound| {
            let relation = bound.relation?;
            let demand = context.scoped_flow(relation).unwrap().demand?;
            if demand.original_call != original_call { return None; }
            assert!(matches!(bound.source_bound, candidate_effect::BoundKey(_, Polarity::Negative,
                ExtrusionEndpoint::Value(ValueEndpointKey::NegativeFunction(root))) if root == demand.root));
            assert_eq!(bound.upper, graph.negative_functions[&demand.root]);
            Some((relation, demand))
        }).collect();
        assert!(!demands.is_empty());
        assert_eq!(graph.nodes.iter().filter(|node| matches!(node,
            Node::Function { polarity: Polarity::Negative, .. })).count(), graph.negative_functions.len(),
            "structural and latent discovery share the same interned Function nodes");
        for row in &graph.rows {
            let ordinal = row.key.ordinal() as usize;
            let (level, non_generic) = match row.key {
                RowKey::Value(_) => (session.value_levels[ordinal], session.value_metadata[ordinal].non_generic),
                RowKey::Effect(_) => (session.effect_levels[ordinal], session.effect_metadata[ordinal].non_generic),
            };
            assert_eq!(row.local, level > graph.boundary && !non_generic);
        }
        assert!(graph.rows.iter().any(|row| !row.local), "the local h demand retains borrowed outer z rows");
        let caller = capture_region.unwrap();
        let first = session.prepare_candidate_fresh_use(&graph, 1, Some(caller)).unwrap();
        let second = session.prepare_candidate_fresh_use(&graph, 1, Some(caller)).unwrap();
        assert_ne!(first.context_use, second.context_use);
        for fresh in [&first, &second] {
            for (index, row) in graph.rows.iter().enumerate() {
                if !row.local { assert_eq!(fresh.rows[index], row.key, "borrowed coordinates stay shared with later constraints"); }
            }
            for (relation, demand) in &demands {
                let index = graph.negative_functions[&demand.root];
                let Node::Function { polarity: Polarity::Negative, children } = graph.nodes[index] else { panic!("negative demand root"); };
                let term = fresh.terms[index].unwrap();
                let TermView::NegativeFunction { argument, argument_effect, result_effect, result } = session.store.term_view(term).unwrap() else { panic!("reconstructed demand"); };
                assert_eq!([argument, argument_effect, result_effect, result], children.map(|child| fresh.terms[child].unwrap()),
                    "all four ports use the common reconstruction map");
                let copied = fresh.scoped_relations[relation].demand.unwrap();
                assert_eq!(copied.original_call, demand.original_call);
                assert_eq!(copied.root, term);
                assert_eq!(copied.output_scope, fresh.scope_remap.scopes.get(&demand.output_scope).copied().unwrap_or(demand.output_scope));
                assert_eq!(copied.input, fresh.scope_remap.inputs.get(&demand.input).copied().unwrap_or(demand.input));
                assert_eq!(copied.use_instance, fresh.context_use);
                let first_copy = first.scoped_relations[relation].demand.unwrap();
                let second_copy = second.scoped_relations[relation].demand.unwrap();
                assert_ne!(first_copy.output_scope, second_copy.output_scope);
                assert_ne!(first_copy.input, second_copy.input);
            }
        }
    }
}
