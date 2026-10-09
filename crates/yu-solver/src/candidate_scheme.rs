//! Private top-level successor graph capture and per-use reconstruction.
//! This retains live algebra, not a closed F5 scheme or a Call certificate.
use crate::*;

#[derive(Debug, Default)]
pub(super) struct GraphState {
    pub graphs: Vec<Option<Graph>>,
    pub routes: Vec<FreshRoute>,
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
    EffectBottom,
    EmptyEffect,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct Bound {
    pub kind: ComponentKind,
    pub side: Polarity,
    pub lower: usize,
    pub upper: usize,
}
#[derive(Debug)]
pub(super) struct FreshRoute {
    pub use_id: DefinitionUseId,
    pub target: usize,
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
        ])?;
        for graph in self.graphs.iter().flatten() {
            total = total.checked_add(graph.bytes()?).ok_or_else(exhausted)?;
        }
        for route in &self.routes {
            total = total
                .checked_add(bytes::<RowKey>(route.rows.capacity())?)
                .ok_or_else(exhausted)?;
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
    anchor_dependencies: Vec<usize>,
}
impl<'a> Capture<'a> {
    fn intern(&mut self, endpoint: Endpoint) -> Result<usize, SolveAvailabilityError> {
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
        // The only publication boundary admitted by this entrypoint is the
        // existing module boundary zero. Origin and ordinal never determine it.
        let local = level > 0 && !metadata.non_generic;
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
            TermView::Leaf(Leaf::IntNegative)
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::IntNegative, polarity)
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
            Endpoint::Value(V::IntNegative, Polarity::Negative) => Node::Leaf(Atom::IntNegative),
            Endpoint::Effect(E::BottomPositive, Polarity::Positive) => {
                Node::Leaf(Atom::EffectBottom)
            }
            Endpoint::Effect(E::EmptyNegative, Polarity::Negative) => Node::Leaf(Atom::EmptyEffect),
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
        let lower = self.intern(lower)?;
        let upper = self.intern(upper)?;
        push(
            &mut self.graph.bounds,
            Bound { kind, side, lower, upper },
        )
    }
    fn expand_row(&mut self, index: usize) -> Result<(), SolveAvailabilityError> {
        let Row { key, local } = self.graph.rows[index];
        let session = self.session;
        // An anchor retains its actual session row. Its installed bounds are
        // already active; cloning them would rerun an established contract.
        if !local {
            match key {
                RowKey::Value(i) => {
                    let bounds = session.bounds.get(i as usize).ok_or_else(exhausted)?;
                    for &bound in &bounds.exact_non_variable_lowers {
                        let node = self.intern(Endpoint::Value(bound, Polarity::Positive))?;
                        push(&mut self.anchor_dependencies, node)?;
                    }
                    for &bound in &bounds.exact_non_variable_uppers {
                        let node = self.intern(Endpoint::Value(bound, Polarity::Negative))?;
                        push(&mut self.anchor_dependencies, node)?;
                    }
                }
                RowKey::Effect(i) => {
                    let bounds = session
                        .effect_bounds
                        .get(i as usize)
                        .ok_or_else(exhausted)?;
                    for &bound in &bounds.exact_non_variable_lowers {
                        let node = self.intern(Endpoint::Effect(bound, Polarity::Positive))?;
                        push(&mut self.anchor_dependencies, node)?;
                    }
                    for &bound in &bounds.exact_non_variable_uppers {
                        let node = self.intern(Endpoint::Effect(bound, Polarity::Negative))?;
                        push(&mut self.anchor_dependencies, node)?;
                    }
                }
            }
            return Ok(());
        }
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
        state
            .graphs
            .try_reserve_exact(self.batch.definitions.len())
            .map_err(|_| exhausted())?;
        state
            .graphs
            .resize_with(self.batch.definitions.len(), || None);
        state.refresh_bytes()?;
        self.candidate_graph = Some(state);
        Ok(())
    }
    fn capture_candidate_graph(&mut self, row: u32) -> Result<Graph, SolveAvailabilityError> {
        let mut capture = Capture {
            session: self,
            graph: Graph {
                nodes: Vec::new(),
                rows: Vec::new(),
                bounds: Vec::new(),
                root: 0,
            },
            endpoints: HashMap::new(),
            rows: HashMap::new(),
            pending: Vec::new(),
            anchor_dependencies: Vec::new(),
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
        let mut checked = Vec::new();
        checked
            .try_reserve_exact(capture.graph.nodes.len())
            .map_err(|_| exhausted())?;
        checked.resize(capture.graph.nodes.len(), false);
        let mut dependencies = std::mem::take(&mut capture.anchor_dependencies);
        while let Some(index) = dependencies.pop() {
            if checked[index] {
                continue;
            }
            checked[index] = true;
            match capture.graph.nodes[index] {
                Node::Row { row, .. } if capture.graph.rows[row].local => return Err(exhausted()),
                Node::Function { children, .. } => {
                    for child in children {
                        push(&mut dependencies, child)?;
                    }
                }
                _ => {}
            }
        }
        let scratch = sum(&[
            bytes::<bool>(checked.capacity())?,
            bytes::<usize>(dependencies.capacity())?,
            bytes::<(Endpoint, usize)>(capture.endpoints.capacity())?,
            bytes::<(RowKey, usize)>(capture.rows.capacity())?,
            bytes::<Endpoint>(capture.pending.capacity())?,
        ])?;
        let graph_bytes = capture.graph.bytes()?;
        let Capture {
            graph,
            endpoints,
            rows,
            pending,
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
        drop((endpoints, rows, pending, checked, dependencies));
        self.candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .scratch_bytes -= scratch;
        sampled?;
        Ok(graph)
    }
    pub(super) fn execute_candidate_graph_plan(&mut self) -> Result<(), SolveAvailabilityError> {
        // Candidate admission disallows internal source SCC uses. The graph
        // itself nevertheless retains arbitrary cycles of variable bounds.
        let mut components = Vec::new();
        for component in self.batch.scc_plan().components_in_dependency_first_order() {
            push(&mut components, component.clone())?;
        }
        let component_bytes = vec_bytes(&components)?;
        for component in &components {
            if !self
                .batch
                .scc_component_internal_uses(&component)
                .map_err(|_| exhausted())?
                .is_empty()
            {
                return Err(exhausted());
            }
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
            for member in &members {
                let position = member.ordinal() as usize;
                let root = &self.batch.definitions[position].root;
                let component = self.batch.root_component_positions[root].component;
                staged.push((
                    position,
                    self.capture_candidate_graph(self.live_components[component].ordinal)?,
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
            self.sample_f4_resources(ResourceBoundary::AllDrafts)?;
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
    pub(super) fn route_candidate_graph(
        &mut self,
        id: &DefinitionUseId,
        record: DefinitionUse,
    ) -> Result<usize, SolveAvailabilityError> {
        let target = record.target.ordinal() as usize;
        let graph = self
            .candidate_graph
            .as_mut()
            .and_then(|state| state.graphs[target].take())
            .ok_or_else(exhausted)?;
        let result = self.instantiate_candidate_graph(id, &record, &graph);
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        state.graphs[target] = Some(graph);
        state.scratch_bytes = 0;
        result
    }
    fn instantiate_candidate_graph(
        &mut self,
        id: &DefinitionUseId,
        record: &DefinitionUse,
        graph: &Graph,
    ) -> Result<usize, SolveAvailabilityError> {
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
            bytes::<Option<Term>>(terms.capacity())?,
            bytes::<(usize, bool)>(work.capacity())?,
        ])?;
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        state.scratch_bytes = scratch;
        state.use_peak_bytes = state.use_peak_bytes.max(scratch);
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        for row in &graph.rows {
            let key = if row.local {
                match row.key {
                    RowKey::Value(_) => RowKey::Value(self.fresh_value_at_level(record.use_level)?),
                    RowKey::Effect(_) => {
                        RowKey::Effect(self.fresh_effect_at_level(record.use_level)?)
                    }
                }
            } else {
                row.key
            };
            rows.push(key);
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
                    Node::Leaf(atom) => match atom {
                        Atom::Bottom => self.positive_bottom_term()?,
                        Atom::Top => self.negative_top_term()?,
                        Atom::NegativeBottom => self.negative_bottom_term()?,
                        Atom::IntPositive => self.batch.collected_leaf_term(Leaf::IntPositive),
                        Atom::IntNegative => self.batch.collected_leaf_term(Leaf::IntNegative),
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
        let occurrence = ConstraintOccurrenceId::new(record.occurrence.clone(), 0);
        let cause = CauseId::for_occurrence(occurrence.clone());
        // Replay preserves the captured owner side even when fresh rows
        // share a level. Induced comparisons run on the ordinary worklist.
        for bound in &graph.bounds {
            let lower = terms[bound.lower].ok_or_else(exhausted)?;
            let upper = terms[bound.upper].ok_or_else(exhausted)?;
            let (lower, upper) = match bound.kind {
                ComponentKind::Value => (
                    ExtrusionEndpoint::Value(self.value_endpoint(lower, Polarity::Positive)),
                    ExtrusionEndpoint::Value(self.value_endpoint(upper, Polarity::Negative)),
                ),
                ComponentKind::Effect => (
                    ExtrusionEndpoint::Effect(self.effect_endpoint(lower, Polarity::Positive)),
                    ExtrusionEndpoint::Effect(self.effect_endpoint(upper, Polarity::Negative)),
                ),
            };
            let (owner, item) = if bound.side == Polarity::Positive {
                (upper, lower)
            } else {
                (lower, upper)
            };
            self.candidate_restore_bound(owner, bound.side, item, &occurrence, &cause)?;
        }
        let lower = terms[graph.root].ok_or_else(exhausted)?;
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
        let retained = state
            .retained_bytes
            .checked_add(growth)
            .and_then(|n| n.checked_add(bytes::<RowKey>(rows.capacity()).ok()?))
            .ok_or_else(exhausted)?;
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
            target: record.target.ordinal() as usize,
            rows,
        });
        state.retained_bytes = retained;
        Ok(transitions)
    }
}
