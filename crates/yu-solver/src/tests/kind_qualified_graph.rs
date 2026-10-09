//! Research-only characterization of a live four-port graph. This fixture is
//! not an original-source Call derivation, a satisfiability decision, an export,
//! or a production successor generalizer. The failure below belongs to the
//! current private boxed F5 representation's pure-effect check.
//! The executed graph scope is RAW-EXTRACT/RAW-FRESH. Runtime realization,
//! partial reverse-incidence extraction, an attached residual/scope fixture,
//! nonempty parameter recipes and distinct equal-shape committed term handles
//! are not exercised by these four tests.

use super::*;

struct FourPortFixture {
    session: InferenceSession,
    r: u32,
    alpha: u32,
    beta: u32,
    e: u32,
    demand: Term,
    outer: Term,
    occurrence: ConstraintOccurrenceId,
    cause: CauseId,
}

impl FourPortFixture {
    fn new() -> Self {
        let batch = collect(module("my fixture = 1", "kind-qualified-live-graph"));
        let mut session = InferenceSession::new(batch);
        let r = session.fresh_value_at_level(1).unwrap();
        let alpha = session.fresh_value_at_level(1).unwrap();
        let beta = session.fresh_value_at_level(1).unwrap();
        let e = session.fresh_effect_at_level(1).unwrap();
        let e_negative = session.live_effect_term(Polarity::Negative, e).unwrap();
        let beta_negative = session.live_value_term(Polarity::Negative, beta).unwrap();
        let demand = session
            .negative_function_term(
                session.batch.collected_leaf_term(Leaf::IntPositive),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                e_negative,
                beta_negative,
            )
            .unwrap();
        let alpha_negative = session.live_value_term(Polarity::Negative, alpha).unwrap();
        let beta_positive = session.live_value_term(Polarity::Positive, beta).unwrap();
        let outer = session
            .positive_function_term(
                alpha_negative,
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                beta_positive,
            )
            .unwrap();
        let occurrence =
            ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 242);
        let cause = CauseId::for_occurrence(occurrence.clone());
        let mut fixture = Self {
            session,
            r,
            alpha,
            beta,
            e,
            demand,
            outer,
            occurrence,
            cause,
        };
        fixture.constrain(
            ValueEndpointKey::ValueRow(alpha),
            ValueEndpointKey::NegativeFunction(demand),
        );
        fixture.constrain(
            ValueEndpointKey::PositiveFunction(outer),
            ValueEndpointKey::ValueRow(r),
        );
        fixture
    }

    fn constrain(&mut self, lower: ValueEndpointKey, upper: ValueEndpointKey) {
        self.session
            .constrain_live_value(
                CanonicalValuePairKey { lower, upper },
                &self.occurrence,
                &self.cause,
            )
            .unwrap();
    }
}

#[test]
fn current_private_f5_representation_limit_on_unbounded_negative_effect() {
    let fixture = FourPortFixture::new();
    let session = &fixture.session;
    assert_eq!(
        session.bounds[fixture.alpha as usize].exact_non_variable_uppers,
        [ValueEndpointKey::NegativeFunction(fixture.demand)]
    );
    assert_eq!(
        session.bounds[fixture.r as usize].exact_non_variable_lowers,
        [ValueEndpointKey::PositiveFunction(fixture.outer)]
    );
    assert_eq!(
        session.effect_bounds[fixture.e as usize],
        EffectBounds::default()
    );

    // The real boxed walker follows r+ -> outer+ -> alpha- -> demand-.
    // Its effect-port check sees e- without the two pure-effect flags.
    let meter = DraftHeapMeter::default();
    let mut walker = F5cGeneralizer::with_source_meter(session, &meter);
    walker.positive_row(fixture.r, true).unwrap();
    assert!(
        walker.invalid_effects,
        "the failure is caused by the effect-port check"
    );
    drop(walker);
    let mut builder = F5cGeneralizer::with_source_meter(session, &meter);
    assert!(matches!(
        builder.build(fixture.r),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert!(builder.invalid_effects);
}

#[test]
fn live_provider_replay_preserves_four_ports_and_effect_edge() {
    let mut fixture = FourPortFixture::new();
    let q = fixture.session.fresh_effect_at_level(1).unwrap();
    let q_positive = fixture
        .session
        .live_effect_term(Polarity::Positive, q)
        .unwrap();
    let provider = fixture
        .session
        .positive_function_term(
            fixture.session.batch.collected_leaf_term(Leaf::IntNegative),
            fixture
                .session
                .batch
                .collected_leaf_term(Leaf::EmptyEffectNegative),
            q_positive,
            fixture.session.batch.collected_leaf_term(Leaf::IntPositive),
        )
        .unwrap();
    fixture.constrain(
        ValueEndpointKey::PositiveFunction(provider),
        ValueEndpointKey::ValueRow(fixture.alpha),
    );
    let session = &fixture.session;
    assert_eq!(
        session.bounds[fixture.alpha as usize].exact_non_variable_lowers,
        [ValueEndpointKey::PositiveFunction(provider)]
    );
    assert_eq!(
        session.bounds[fixture.alpha as usize].exact_non_variable_uppers,
        [ValueEndpointKey::NegativeFunction(fixture.demand)]
    );
    assert_eq!(
        session.effect_bounds[q as usize].direct_upper_rows,
        [fixture.e]
    );
    assert_eq!(
        session.effect_bounds[fixture.e as usize].direct_lower_rows,
        [q]
    );
    assert!(
        session.effect_bounds[q as usize]
            .direct_lower_rows
            .is_empty()
    );
    assert!(
        session.effect_bounds[fixture.e as usize]
            .direct_upper_rows
            .is_empty()
    );
    for row in [q, fixture.e] {
        let bounds = &session.effect_bounds[row as usize];
        assert!(!bounds.has_bottom_lower);
        assert!(!bounds.has_empty_upper);
        assert!(bounds.exact_non_variable_lowers.is_empty());
        assert!(bounds.exact_non_variable_uppers.is_empty());
    }
    assert_eq!(
        session.bounds[fixture.beta as usize].exact_non_variable_lowers,
        [ValueEndpointKey::IntPositive]
    );
    assert!(session.bounds[fixture.beta as usize].has_int_positive_lower);
}

// Immutable complete active scalar projection only. No diagnostic memo payload,
// store receipts, operational continuation, source eligibility, or Call evidence.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ResearchRowKey {
    frame: u64,
    kind: ComponentKind,
    ordinal: u32,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ResearchTermId {
    Original(Term),
    Fresh { frame: u64, ordinal: usize },
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum GraphEndpoint {
    ValueAtom(ValueEndpointKey),
    EffectAtom(EffectEndpointKey),
    Row(ResearchRowKey),
    Function(Polarity, ResearchTermId),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RowRecord {
    level: u32,
    metadata: LiveVariableMetadata,
    direct_lower: Vec<ResearchRowKey>,
    direct_upper: Vec<ResearchRowKey>,
    exact_lower: Vec<GraphEndpoint>,
    exact_upper: Vec<GraphEndpoint>,
    // Value: (has_int_positive_lower, false); Effect: (bottom, empty).
    flags: (bool, bool),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum TermRecord {
    Leaf(Leaf),
    Component(ComponentId, ResearchRowKey),
    Live(ResearchRowKey, Polarity),
    PositiveBottom,
    NegativeTop,
    NegativeBottom,
    Function {
        polarity: Polarity,
        children: [ResearchTermId; 4],
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct GraphRecord {
    rows: HashMap<ResearchRowKey, RowRecord>,
    terms: HashMap<ResearchTermId, TermRecord>,
    // Original admitted keys are nominal labels; the endpoint fields are mapped.
    pairs: HashMap<TypedPairKey, (GraphEndpoint, GraphEndpoint)>,
    components: Vec<ResearchRowKey>,
    parameter_live_base: u32,
    parameters: Vec<(HirParameterId, ResearchRowKey)>,
    roots: Vec<ResearchTermId>,
}

fn opposite(p: Polarity) -> Polarity {
    match p {
        Polarity::Positive => Polarity::Negative,
        Polarity::Negative => Polarity::Positive,
    }
}

fn row_key(frame: u64, kind: ComponentKind, ordinal: u32) -> ResearchRowKey {
    ResearchRowKey {
        frame,
        kind,
        ordinal,
    }
}

fn value_graph_endpoint(
    frame: u64,
    endpoint: ValueEndpointKey,
    polarity: Polarity,
) -> GraphEndpoint {
    match endpoint {
        ValueEndpointKey::ValueRow(n) => {
            GraphEndpoint::Row(row_key(frame, ComponentKind::Value, n))
        }
        ValueEndpointKey::PositiveFunction(t) => {
            assert_eq!(polarity, Polarity::Positive);
            GraphEndpoint::Function(polarity, ResearchTermId::Original(t))
        }
        ValueEndpointKey::NegativeFunction(t) => {
            assert_eq!(polarity, Polarity::Negative);
            GraphEndpoint::Function(polarity, ResearchTermId::Original(t))
        }
        atom => {
            let actual = match atom {
                ValueEndpointKey::BottomPositive
                | ValueEndpointKey::IntPositive
                | ValueEndpointKey::UnitPositive => {
                    Polarity::Positive
                }
                ValueEndpointKey::BottomNegative
                | ValueEndpointKey::TopNegative
                | ValueEndpointKey::IntNegative
                | ValueEndpointKey::UnitNegative => Polarity::Negative,
                _ => unreachable!(),
            };
            assert_eq!(actual, polarity);
            GraphEndpoint::ValueAtom(atom)
        }
    }
}

fn effect_graph_endpoint(
    frame: u64,
    endpoint: EffectEndpointKey,
    polarity: Polarity,
) -> GraphEndpoint {
    match endpoint {
        EffectEndpointKey::EffectRow(n) => {
            GraphEndpoint::Row(row_key(frame, ComponentKind::Effect, n))
        }
        atom => {
            assert_eq!(
                polarity,
                match atom {
                    EffectEndpointKey::BottomPositive => Polarity::Positive,
                    EffectEndpointKey::EmptyNegative => Polarity::Negative,
                    _ => unreachable!(),
                }
            );
            GraphEndpoint::EffectAtom(atom)
        }
    }
}

impl GraphRecord {
    // Panics are explicit malformed-input failures in this bounded test helper.
    fn extract(session: &InferenceSession, frame: u64, roots: &[Term]) -> Self {
        assert!(session.typed_worklist.is_empty());
        assert_eq!(session.bounds.len(), session.value_levels.len());
        assert_eq!(session.bounds.len(), session.value_metadata.len());
        assert_eq!(session.effect_bounds.len(), session.effect_levels.len());
        assert_eq!(session.effect_bounds.len(), session.effect_metadata.len());
        let mut graph = Self {
            rows: HashMap::new(),
            terms: HashMap::new(),
            pairs: HashMap::new(),
            components: Vec::new(),
            parameter_live_base: session.parameter_live_base,
            parameters: Vec::new(),
            roots: roots
                .iter()
                .copied()
                .map(ResearchTermId::Original)
                .collect(),
        };
        for (n, bounds) in session.bounds.iter().enumerate() {
            let key = row_key(frame, ComponentKind::Value, u32::try_from(n).unwrap());
            graph.rows.insert(
                key,
                RowRecord {
                    level: session.value_levels[n],
                    metadata: session.value_metadata[n],
                    direct_lower: bounds
                        .direct_lower_rows
                        .iter()
                        .map(|&n| row_key(frame, key.kind, n))
                        .collect(),
                    direct_upper: bounds
                        .direct_upper_rows
                        .iter()
                        .map(|&n| row_key(frame, key.kind, n))
                        .collect(),
                    exact_lower: bounds
                        .exact_non_variable_lowers
                        .iter()
                        .map(|&e| value_graph_endpoint(frame, e, Polarity::Positive))
                        .collect(),
                    exact_upper: bounds
                        .exact_non_variable_uppers
                        .iter()
                        .map(|&e| value_graph_endpoint(frame, e, Polarity::Negative))
                        .collect(),
                    flags: (bounds.has_int_positive_lower, false),
                },
            );
        }
        for (n, bounds) in session.effect_bounds.iter().enumerate() {
            let key = row_key(frame, ComponentKind::Effect, u32::try_from(n).unwrap());
            graph.rows.insert(
                key,
                RowRecord {
                    level: session.effect_levels[n],
                    metadata: session.effect_metadata[n],
                    direct_lower: bounds
                        .direct_lower_rows
                        .iter()
                        .map(|&n| row_key(frame, key.kind, n))
                        .collect(),
                    direct_upper: bounds
                        .direct_upper_rows
                        .iter()
                        .map(|&n| row_key(frame, key.kind, n))
                        .collect(),
                    exact_lower: bounds
                        .exact_non_variable_lowers
                        .iter()
                        .map(|&e| effect_graph_endpoint(frame, e, Polarity::Positive))
                        .collect(),
                    exact_upper: bounds
                        .exact_non_variable_uppers
                        .iter()
                        .map(|&e| effect_graph_endpoint(frame, e, Polarity::Negative))
                        .collect(),
                    flags: (bounds.has_bottom_lower, bounds.has_empty_upper),
                },
            );
        }
        for component in &session.live_components {
            graph
                .components
                .push(row_key(frame, component.kind, component.ordinal));
        }
        for (position, parameter) in session.batch.parameter_recipes.iter().enumerate() {
            let ordinal = session
                .parameter_live_base
                .checked_add(u32::try_from(position).unwrap())
                .unwrap();
            graph.parameters.push((
                parameter.clone(),
                row_key(frame, ComponentKind::Value, ordinal),
            ));
        }
        for &key in session.typed_pairs.keys() {
            let endpoints = match key {
                TypedPairKey::Value(pair) => (
                    value_graph_endpoint(frame, pair.lower, Polarity::Positive),
                    value_graph_endpoint(frame, pair.upper, Polarity::Negative),
                ),
                TypedPairKey::Effect { lower, upper } => (
                    effect_graph_endpoint(frame, lower, Polarity::Positive),
                    effect_graph_endpoint(frame, upper, Polarity::Negative),
                ),
            };
            graph.pairs.insert(key, endpoints);
        }
        let mut pending = roots.to_vec();
        for endpoint in graph
            .rows
            .values()
            .flat_map(|r| r.exact_lower.iter().chain(&r.exact_upper))
            .chain(graph.pairs.values().flat_map(|(a, b)| [a, b]))
        {
            if let GraphEndpoint::Function(_, ResearchTermId::Original(term)) = endpoint {
                pending.push(*term);
            }
        }
        while let Some(term) = pending.pop() {
            let id = ResearchTermId::Original(term);
            if graph.terms.contains_key(&id) {
                continue;
            }
            let record = match session
                .store
                .term_view(term)
                .expect("actual committed term handle")
            {
                TermView::Leaf(leaf) => TermRecord::Leaf(leaf),
                TermView::Component(component) => {
                    let position = *session
                        .batch
                        .component_term_positions
                        .get(&term)
                        .expect("actual component recipe position");
                    let live = session
                        .live_components
                        .get(position)
                        .expect("component live translation");
                    assert_eq!(component.kind(), live.kind);
                    TermRecord::Component(
                        component.clone(),
                        row_key(frame, live.kind, live.ordinal),
                    )
                }
                TermView::LiveVariable(live) => {
                    TermRecord::Live(row_key(frame, live.kind(), live.ordinal()), live.polarity())
                }
                TermView::PositiveBottom => TermRecord::PositiveBottom,
                TermView::NegativeTop => TermRecord::NegativeTop,
                TermView::NegativeBottom => TermRecord::NegativeBottom,
                TermView::PositiveFunction {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } => {
                    pending.extend([argument, argument_effect, result_effect, result]);
                    TermRecord::Function {
                        polarity: Polarity::Positive,
                        children: [argument, argument_effect, result_effect, result]
                            .map(ResearchTermId::Original),
                    }
                }
                TermView::NegativeFunction {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } => {
                    pending.extend([argument, argument_effect, result_effect, result]);
                    TermRecord::Function {
                        polarity: Polarity::Negative,
                        children: [argument, argument_effect, result_effect, result]
                            .map(ResearchTermId::Original),
                    }
                }
            };
            graph.terms.insert(id, record);
        }
        graph.validate();
        graph
    }

    fn term_sort(&self, id: ResearchTermId) -> Option<(ComponentKind, Polarity)> {
        Some(match self.terms.get(&id).expect("referenced term record") {
            TermRecord::Leaf(Leaf::IntPositive) => (ComponentKind::Value, Polarity::Positive),
            TermRecord::Leaf(Leaf::IntNegative) => (ComponentKind::Value, Polarity::Negative),
            TermRecord::Leaf(Leaf::UnitPositive) => (ComponentKind::Value, Polarity::Positive),
            TermRecord::Leaf(Leaf::UnitNegative) => (ComponentKind::Value, Polarity::Negative),
            TermRecord::Leaf(Leaf::EffectBottomPositive) => {
                (ComponentKind::Effect, Polarity::Positive)
            }
            TermRecord::Leaf(Leaf::EmptyEffectNegative) => {
                (ComponentKind::Effect, Polarity::Negative)
            }
            TermRecord::Live(key, polarity) => (key.kind, *polarity),
            TermRecord::PositiveBottom => (ComponentKind::Value, Polarity::Positive),
            TermRecord::NegativeTop | TermRecord::NegativeBottom => {
                (ComponentKind::Value, Polarity::Negative)
            }
            TermRecord::Function { polarity, .. } => (ComponentKind::Value, *polarity),
            TermRecord::Component(..) => return None,
        })
    }

    fn validate(&self) {
        let endpoint_check = |endpoint: &GraphEndpoint, kind, polarity| match endpoint {
            GraphEndpoint::Row(key) => {
                assert_eq!(key.kind, kind);
                assert!(self.rows.contains_key(key));
            }
            GraphEndpoint::Function(p, id) => {
                assert_eq!(kind, ComponentKind::Value);
                assert_eq!(*p, polarity);
                assert!(
                    matches!(self.terms.get(id), Some(TermRecord::Function { polarity: actual, .. }) if actual == p)
                );
            }
            GraphEndpoint::ValueAtom(atom) => {
                assert_eq!(kind, ComponentKind::Value);
                assert_eq!(*endpoint, value_graph_endpoint(0, *atom, polarity));
            }
            GraphEndpoint::EffectAtom(atom) => {
                assert_eq!(kind, ComponentKind::Effect);
                assert_eq!(*endpoint, effect_graph_endpoint(0, *atom, polarity));
            }
        };
        for (key, row) in &self.rows {
            for (side, reverse) in [(&row.direct_upper, true), (&row.direct_lower, false)] {
                for target in side {
                    assert_eq!(key.kind, target.kind);
                    let other = self.rows.get(target).expect("direct target row");
                    let paired = if reverse {
                        &other.direct_lower
                    } else {
                        &other.direct_upper
                    };
                    assert_eq!(
                        side.iter().filter(|x| *x == target).count(),
                        paired.iter().filter(|x| *x == key).count()
                    );
                }
            }
            for endpoint in &row.exact_lower {
                endpoint_check(endpoint, key.kind, Polarity::Positive);
            }
            for endpoint in &row.exact_upper {
                endpoint_check(endpoint, key.kind, Polarity::Negative);
            }
        }
        for (key, (lower, upper)) in &self.pairs {
            let kind = match key {
                TypedPairKey::Value(_) => ComponentKind::Value,
                TypedPairKey::Effect { .. } => ComponentKind::Effect,
            };
            endpoint_check(lower, kind, Polarity::Positive);
            endpoint_check(upper, kind, Polarity::Negative);
        }
        for key in self
            .components
            .iter()
            .chain(self.parameters.iter().map(|(_, key)| key))
        {
            assert!(self.rows.contains_key(key));
        }
        for (id, record) in &self.terms {
            match record {
                TermRecord::Live(key, _) | TermRecord::Component(_, key) => {
                    assert!(self.rows.contains_key(key));
                }
                TermRecord::Function { polarity, children } => {
                    let sorts = [
                        (ComponentKind::Value, opposite(*polarity)),
                        (ComponentKind::Effect, opposite(*polarity)),
                        (ComponentKind::Effect, *polarity),
                        (ComponentKind::Value, *polarity),
                    ];
                    for (child, expected) in children.iter().zip(sorts) {
                        assert_eq!(self.term_sort(*child), Some(expected));
                    }
                }
                _ => {}
            }
            // Iterative gray/black traversal rejects structural cycles; row cycles
            // remain references and never enter this structural traversal.
            let mut stack = vec![(*id, false)];
            let mut gray = HashSet::new();
            let mut black = HashSet::new();
            while let Some((term, exit)) = stack.pop() {
                if exit {
                    gray.remove(&term);
                    black.insert(term);
                    continue;
                }
                if black.contains(&term) {
                    continue;
                }
                assert!(gray.insert(term), "structural term cycle");
                stack.push((term, true));
                if let TermRecord::Function { children, .. } = &self.terms[&term] {
                    stack.extend(children.iter().map(|&child| (child, false)));
                }
            }
        }
        for root in &self.roots {
            assert!(self.terms.contains_key(root));
        }
    }

    fn map(
        &self,
        rows: &HashMap<ResearchRowKey, ResearchRowKey>,
        terms: &HashMap<ResearchTermId, ResearchTermId>,
    ) -> Self {
        let endpoint = |e: &GraphEndpoint| match e {
            GraphEndpoint::Row(r) => GraphEndpoint::Row(rows[r]),
            GraphEndpoint::Function(p, t) => GraphEndpoint::Function(*p, terms[t]),
            atom => atom.clone(),
        };
        let result = Self {
            rows: self
                .rows
                .iter()
                .map(|(key, row)| {
                    (
                        rows[key],
                        RowRecord {
                            level: row.level,
                            metadata: row.metadata,
                            flags: row.flags,
                            direct_lower: row.direct_lower.iter().map(|r| rows[r]).collect(),
                            direct_upper: row.direct_upper.iter().map(|r| rows[r]).collect(),
                            exact_lower: row.exact_lower.iter().map(&endpoint).collect(),
                            exact_upper: row.exact_upper.iter().map(&endpoint).collect(),
                        },
                    )
                })
                .collect(),
            terms: self
                .terms
                .iter()
                .map(|(id, record)| {
                    (
                        terms[id],
                        match record {
                            TermRecord::Live(r, p) => TermRecord::Live(rows[r], *p),
                            TermRecord::Component(c, r) => {
                                TermRecord::Component(c.clone(), rows[r])
                            }
                            TermRecord::Function { polarity, children } => TermRecord::Function {
                                polarity: *polarity,
                                children: children.map(|t| terms[&t]),
                            },
                            other => other.clone(),
                        },
                    )
                })
                .collect(),
            pairs: self
                .pairs
                .iter()
                .map(|(key, (a, b))| (*key, (endpoint(a), endpoint(b))))
                .collect(),
            components: self.components.iter().map(|r| rows[r]).collect(),
            parameter_live_base: self.parameter_live_base,
            parameters: self
                .parameters
                .iter()
                .map(|(p, r)| (p.clone(), rows[r]))
                .collect(),
            roots: self.roots.iter().map(|t| terms[t]).collect(),
        };
        result.validate();
        result
    }
}

struct FreshGraph {
    graph: Arc<GraphRecord>,
    rows: HashMap<ResearchRowKey, ResearchRowKey>,
    terms: HashMap<ResearchTermId, ResearchTermId>,
    row_inverse: HashMap<ResearchRowKey, ResearchRowKey>,
    term_inverse: HashMap<ResearchTermId, ResearchTermId>,
}

impl FreshGraph {
    fn new(original: &GraphRecord, frame: u64) -> Self {
        assert!(original.rows.keys().all(|key| key.frame != frame));
        let rows: HashMap<_, _> = original
            .rows
            .keys()
            .map(|&key| (key, row_key(frame, key.kind, key.ordinal)))
            .collect();
        let terms: HashMap<_, _> = original
            .terms
            .keys()
            .enumerate()
            .map(|(ordinal, &key)| (key, ResearchTermId::Fresh { frame, ordinal }))
            .collect();
        let row_inverse: HashMap<_, _> = rows.iter().map(|(&a, &b)| (b, a)).collect();
        let term_inverse: HashMap<_, _> = terms.iter().map(|(&a, &b)| (b, a)).collect();
        assert_eq!(rows.len(), row_inverse.len());
        assert_eq!(terms.len(), term_inverse.len());
        Self {
            graph: Arc::new(original.map(&rows, &terms)),
            rows,
            terms,
            row_inverse,
            term_inverse,
        }
    }
    fn decode(&self) -> GraphRecord {
        self.graph.map(&self.row_inverse, &self.term_inverse)
    }
}

#[test]
fn complete_active_graph_keeps_unbounded_rows_pair_keys_and_actual_roots() {
    let mut fixture = FourPortFixture::new();
    let disconnected = fixture.session.fresh_effect_at_level(3).unwrap();
    let row_free = CanonicalValuePairKey {
        lower: ValueEndpointKey::IntPositive,
        upper: ValueEndpointKey::IntNegative,
    };
    fixture.constrain(row_free.lower, row_free.upper);
    let root = fixture
        .session
        .live_value_term(Polarity::Positive, fixture.r)
        .unwrap();
    let component = fixture.session.batch.component_term_at(0);
    let original = GraphRecord::extract(&fixture.session, 10, &[root, component, fixture.outer]);
    assert_eq!(
        original.rows.len(),
        fixture.session.bounds.len() + fixture.session.effect_bounds.len()
    );
    assert_eq!(original.pairs.len(), fixture.session.typed_pairs.len());
    assert!(original.pairs.contains_key(&TypedPairKey::Value(row_free)));
    let e = row_key(10, ComponentKind::Effect, fixture.e);
    assert_eq!(original.rows[&e].flags, (false, false));
    assert!(original.rows[&e].exact_lower.is_empty());
    assert!(original.rows[&e].exact_upper.is_empty());
    assert_eq!(
        original.rows[&row_key(10, ComponentKind::Effect, disconnected)].level,
        3
    );
    let TermRecord::Component(_, translation) =
        &original.terms[&ResearchTermId::Original(component)]
    else {
        panic!("retained nominal component");
    };
    assert_eq!(*translation, original.components[0]);
    let live = fixture.session.live_components[0];
    assert_eq!(*translation, row_key(10, live.kind, live.ordinal));
    let TermRecord::Function { children, .. } =
        &original.terms[&ResearchTermId::Original(fixture.demand)]
    else {
        panic!("retained demand");
    };
    assert_eq!(
        original.terms[&children[2]],
        TermRecord::Live(e, Polarity::Negative)
    );
    let fresh = FreshGraph::new(&original, 11);
    assert_eq!(fresh.decode(), original);
    assert_eq!(fresh.graph.roots.len(), 3);
}

#[test]
fn finite_effect_cycle_opposite_ports_fresh_frames_and_alias_round_trip() {
    let mut fixture = FourPortFixture::new();
    let q = fixture.session.fresh_effect_at_level(1).unwrap();
    let q_positive = fixture
        .session
        .live_effect_term(Polarity::Positive, q)
        .unwrap();
    let provider = fixture
        .session
        .positive_function_term(
            fixture.session.batch.collected_leaf_term(Leaf::IntNegative),
            fixture
                .session
                .batch
                .collected_leaf_term(Leaf::EmptyEffectNegative),
            q_positive,
            fixture.session.batch.collected_leaf_term(Leaf::IntPositive),
        )
        .unwrap();
    fixture.constrain(
        ValueEndpointKey::PositiveFunction(provider),
        ValueEndpointKey::ValueRow(fixture.alpha),
    );
    // Close a real direct effect cycle through the existing scalar engine.
    fixture
        .session
        .constrain_live(
            LiveConstraintTask::Effect(
                EffectEndpointKey::EffectRow(fixture.e),
                EffectEndpointKey::EffectRow(q),
            ),
            &fixture.occurrence,
            &fixture.cause,
        )
        .unwrap();
    let e_negative = fixture
        .session
        .live_effect_term(Polarity::Negative, fixture.e)
        .unwrap();
    let e_positive = fixture
        .session
        .live_effect_term(Polarity::Positive, fixture.e)
        .unwrap();
    let shared_effect = fixture
        .session
        .positive_function_term(
            fixture.session.batch.collected_leaf_term(Leaf::IntNegative),
            e_negative,
            e_positive,
            fixture.session.batch.collected_leaf_term(Leaf::IntPositive),
        )
        .unwrap();
    let shared_nested = fixture
        .session
        .positive_function_term(
            fixture.demand,
            fixture
                .session
                .batch
                .collected_leaf_term(Leaf::EmptyEffectNegative),
            fixture
                .session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            fixture.outer,
        )
        .unwrap();
    let graph = GraphRecord::extract(
        &fixture.session,
        20,
        &[shared_effect, shared_nested, fixture.outer, fixture.outer],
    );
    let e = row_key(20, ComponentKind::Effect, fixture.e);
    let q_key = row_key(20, ComponentKind::Effect, q);
    assert_eq!(graph.rows[&q_key].direct_upper, [e]);
    assert_eq!(graph.rows[&e].direct_lower, [q_key]);
    assert_eq!(graph.rows[&e].direct_upper, [q_key]);
    assert_eq!(graph.rows[&q_key].direct_lower, [e]);
    let v0 = row_key(20, ComponentKind::Value, 0);
    let e0 = row_key(20, ComponentKind::Effect, 0);
    assert_ne!(v0, e0);
    assert!(graph.rows.contains_key(&v0) && graph.rows.contains_key(&e0));
    let first = FreshGraph::new(&graph, 21);
    let second = FreshGraph::new(&graph, 22);
    assert_ne!(first.rows[&v0], first.rows[&e0]);
    assert!(
        first
            .rows
            .values()
            .all(|id| !second.row_inverse.contains_key(id))
    );
    assert!(
        first
            .terms
            .values()
            .all(|id| !second.term_inverse.contains_key(id))
    );
    let alias = Arc::clone(&first.graph);
    assert!(Arc::ptr_eq(&alias, &first.graph));
    let TermRecord::Function { children, .. } =
        &first.graph.terms[&first.terms[&ResearchTermId::Original(shared_effect)]]
    else {
        panic!("all four effect ports retained");
    };
    assert_eq!(
        first.graph.terms[&children[1]],
        TermRecord::Live(first.rows[&e], Polarity::Negative)
    );
    assert_eq!(
        first.graph.terms[&children[2]],
        TermRecord::Live(first.rows[&e], Polarity::Positive)
    );
    assert_eq!(first.graph.roots[2], first.graph.roots[3]);
    let TermRecord::Function { children, .. } = &first.graph.terms[&first.graph.roots[1]] else {
        panic!("shared nested Function retained");
    };
    assert_eq!(children[3], first.graph.roots[2]);
    assert_eq!(first.decode(), graph);
    assert_eq!(second.decode(), graph);
}
