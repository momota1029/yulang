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
    pub retained_bytes: usize,
    pub scratch_bytes: usize,
    pub orchestration_bytes: usize,
    pub capture_peak_bytes: usize,
    pub use_peak_bytes: usize,
}

#[derive(Debug)]
pub(super) struct Graph {
    pub nodes: Vec<Node>,
    pub rows: Vec<Row>,
    pub bounds: Vec<Bound>,
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
    UnitNegative,
    EffectBottom,
    EmptyEffect,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct Bound {
    pub relation: Option<candidate_context::RelationId>,
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
            bytes::<Node>(self.nodes.capacity())?,
            bytes::<Row>(self.rows.capacity())?,
            bytes::<Bound>(self.bounds.capacity())?,
        ])
    }
}
impl GraphState {
    pub fn refresh_bytes(&mut self) -> Result<(), SolveAvailabilityError> {
        let mut total = sum(&[
            bytes::<Option<Graph>>(self.graphs.capacity())?,
            bytes::<FreshRoute>(self.routes.capacity())?,
            bytes::<Option<LocalScheme>>(self.locals.capacity())?,
            bytes::<LocalFreshRoute>(self.local_routes.capacity())?,
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
        self.retained_bytes = total;
        Ok(())
    }
}
struct Capture<'a> {
    session: &'a InferenceSession,
    graph: Graph,
    endpoints: HashMap<Endpoint, usize>,
    rows: HashMap<RowKey, usize>,
    pending: Vec<Endpoint>,
    bound_keys: HashSet<(ComponentKind, Polarity, usize, usize)>,
    boundary: u32,
}
impl<'a> Capture<'a> {
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
            Endpoint::Value(V::IntNegative, Polarity::Negative) => Node::Leaf(Atom::IntNegative),
            Endpoint::Value(V::UnitNegative, Polarity::Negative) => Node::Leaf(Atom::UnitNegative),
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
        let relation = self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound(candidate_effect::BoundKey(owner, side, item));
        let lower = self.intern(lower)?;
        let upper = self.intern(upper)?;
        let key = (kind, side, lower, upper);
        if self.bound_keys.contains(&key) { return Ok(()); }
        self.bound_keys.try_reserve(1).map_err(|_| exhausted())?;
        push(&mut self.graph.bounds, Bound { relation, kind, side, lower, upper })?;
        self.bound_keys.insert(key);
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
        let mut capture = Capture {
            session: self,
            graph: Graph {
                nodes: Vec::new(),
                rows: Vec::new(),
                bounds: Vec::new(),
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
        while !capture.pending.is_empty() || row_cursor < capture.graph.rows.len() {
            while let Some(endpoint) = capture.pending.pop() {
                capture.expand_node(endpoint)?;
            }
            if row_cursor < capture.graph.rows.len() {
                capture.expand_row(row_cursor)?;
                row_cursor += 1;
            }
        }
        let scratch = sum(&[
            bytes::<(Endpoint, usize)>(capture.endpoints.capacity())?,
            bytes::<(RowKey, usize)>(capture.rows.capacity())?,
            bytes::<Endpoint>(capture.pending.capacity())?,
            bytes::<(ComponentKind, Polarity, usize, usize)>(capture.bound_keys.capacity())?,
        ])?;
        let graph_bytes = capture.graph.bytes()?;
        let Capture {
            graph,
            endpoints,
            rows,
            pending,
            bound_keys,
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
        drop((endpoints, rows, pending, bound_keys));
        self.candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .scratch_bytes -= scratch;
        sampled?;
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
            for member in &members {
                let position = member.ordinal() as usize;
                let root = self.batch.definitions[position].root.clone();
                let component = self.batch.root_component_positions[&root].component;
                staged.push((
                    position,
                    self.capture_candidate_graph(self.live_components[component].ordinal, 0)?,
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
        let entry_scratch = self.candidate_graph.as_ref().unwrap().scratch_bytes;
        let result = (|| {
            let graph = self.capture_candidate_graph(root, boundary)?;
            self.instantiate_candidate_graph(id, &record, graph, entry_scratch)
        })();
        self.candidate_graph.as_mut().ok_or_else(exhausted)?.scratch_bytes = entry_scratch;
        result
    }
    pub(super) fn freshen_candidate_graph(
        &mut self, graph: &Graph, use_level: u32,
        occurrence: &ConstraintOccurrenceId, cause: &CauseId,
    ) -> Result<(Term, Vec<RowKey>), SolveAvailabilityError> {
        let context_use = self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra.context.begin_use()?;
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
        let mut view_remap = HashMap::new();
        view_remap.try_reserve(graph.nodes.len()).map_err(|_| exhausted())?;
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
                        Atom::IntNegative => self.batch.collected_leaf_term(Leaf::IntNegative),
                        Atom::UnitNegative => self.batch.collected_leaf_term(Leaf::UnitNegative),
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
        // Replay preserves the captured owner side even when fresh rows
        // share a level. Induced comparisons run on the ordinary worklist.
        for bound in &graph.bounds {
            let (lower, upper) = match bound.kind {
                ComponentKind::Value => {
                    let lower = terms[bound.lower].ok_or_else(exhausted)?;
                    let upper = terms[bound.upper].ok_or_else(exhausted)?;
                    (ExtrusionEndpoint::Value(self.value_endpoint(lower, Polarity::Positive)),
                     ExtrusionEndpoint::Value(self.value_endpoint(upper, Polarity::Negative)))
                }
                ComponentKind::Effect => {
                    let lower = if let Some(&operand) = effect_operands.get(&bound.lower) { operand }
                        else { self.effect_endpoint(terms[bound.lower].ok_or_else(exhausted)?, Polarity::Positive) };
                    let upper = if let Some(&operand) = effect_operands.get(&bound.upper) { operand }
                        else { self.effect_endpoint(terms[bound.upper].ok_or_else(exhausted)?, Polarity::Negative) };
                    (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper))
                }
            };
            let (owner, item) = if bound.side == Polarity::Positive {
                (upper, lower)
            } else {
                (lower, upper)
            };
            if let Some(parent) = bound.relation {
                // One reconstruction route shares all captured relation inputs.
                // Independent uses retain independent transport origins even
                // when an older, nongeneric coordinate is shared.
                self.candidate_context_transport(parent, candidate_effect::BoundKey(owner, bound.side, item),
                    context_use)?;
            }
            self.candidate_restore_bound(owner, bound.side, item, occurrence, cause)?;
        }
        let lower = terms[graph.root].ok_or_else(exhausted)?;
        Ok((lower, rows))
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
        *destination = Some(LocalScheme { id, root, boundary });
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
        let (root, boundary, local) = {
            let scheme = self.candidate_graph.as_ref().and_then(|state| state.locals.get(slot)).and_then(Option::as_ref).ok_or_else(exhausted)?;
            (scheme.root, scheme.boundary, scheme.id.clone())
        };
        self.incoming_route_accounting_active = true;
        self.route_attempt_physical_change = false;
        self.incoming_route_event_sample_failed = false;
        let result = self.with_route_transaction(|session| {
            // This graph is a use-time observation of a live scheme, never the
            // binding's authority or a promise that anchors are fully solved.
            let graph = session.capture_candidate_graph(root, boundary)?;
            let id = ConstraintOccurrenceId::new(occurrence.clone(), 0);
            let cause = CauseId::for_occurrence(id.clone());
            let (lower, rows) = session.freshen_candidate_graph(&graph, level, &id, &cause)?;
            let upper = session.batch.component_term_at(value);
            session.admit_candidate_value_link(occurrence, 0, lower, upper)?;
            let state = session.candidate_graph.as_mut().ok_or_else(exhausted)?;
            let old_capacity = state.local_routes.capacity();
            state.local_routes.try_reserve(1).map_err(|_| exhausted())?;
            let growth = bytes::<LocalFreshRoute>(state.local_routes.capacity() - old_capacity)?;
            let retained = sum(&[state.retained_bytes, growth,
                bytes::<RowKey>(rows.capacity())?, graph.bytes()?])?;
            state.retained_bytes = state.retained_bytes.checked_add(growth).ok_or_else(exhausted)?;
            session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            let state = session.candidate_graph.as_mut().ok_or_else(exhausted)?;
            state.local_routes.push(LocalFreshRoute { slot, local: local.clone(), occurrence: occurrence.clone(), graph, rows });
            state.retained_bytes = retained;
            state.scratch_bytes = 0;
            session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            if session.incoming_route_event_sample_failed { return Err(exhausted()); }
            Ok(())
        });
        self.incoming_route_accounting_active = false;
        self.route_attempt_physical_change = false;
        self.incoming_route_event_sample_failed = false;
        if let Some(state) = &mut self.candidate_graph { state.scratch_bytes = 0; }
        result
    }

}
