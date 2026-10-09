//! Research-only new wrapper implementing the candidate ROW/PATH seam.
//!
//! Synthetic nominal keys stand for supplied indexed references; they are not
//! authentic source scope certificates. Original edges are unsolved proof-slot
//! references, never witnesses. The opaque whole residual is retained without
//! inspection. This is neither production authority nor full Call inference.
//! Only same-level row/row constraints enter a dedicated actual core session.
use super::*;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum EndpointRole {
    Flexible,
    Fixed,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct SyntheticFamilyScope(u32);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct EndpointKey {
    family_scope: SyntheticFamilyScope,
    nominal_reference: u32,
    role: EndpointRole,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct OriginalEdge {
    source: EndpointKey,
    target: EndpointKey,
    proof_slot: usize,
}

#[derive(Debug)]
enum AdapterError {
    CrossFamily {
        source: SyntheticFamilyScope,
        target: SyntheticFamilyScope,
    },
    Availability(SolveAvailabilityError),
}

impl std::fmt::Display for AdapterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CrossFamily { source, target } => {
                write!(f, "cross-family adapter edge: {source:?} -> {target:?}")
            }
            Self::Availability(error) => write!(f, "core availability: {error:?}"),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
enum PathView {
    // An empty recipe represents Refl; a nonempty recipe folds Original
    // occurrence references using Compose. Neither chooses slot inhabitants.
    Refl,
    OriginalCompose(Vec<usize>),
    // Only excludes this finite Refl/Original/Compose language.
    NoPath,
}

struct CompleteBoundStore<R> {
    residual: Arc<R>,
    original_edges: Vec<OriginalEdge>,
    rows: HashMap<EndpointKey, u32>,
    level: u32,
    session: InferenceSession,
}

fn complete_bound_session() -> InferenceSession {
    let source: Arc<yu_syntax::SourceText> = Arc::from("1");
    let parsed = yu_syntax::parse_file(
        source.clone(),
        Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()),
    );
    let hir = yu_hir::lower_module(
        yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
            "research",
            "complete-bound-row-only",
        ))),
        &parsed,
        yu_hir::SemanticImports::empty(),
    )
    .unwrap();
    InferenceSession::new(ConstraintBatch::collect(Arc::new(hir)).unwrap())
}

impl<R> CompleteBoundStore<R> {
    fn new(residual: Arc<R>, level: u32) -> Self {
        let session = complete_bound_session();
        assert!(session.typed_pairs.is_empty());
        assert!(
            session
                .bounds
                .iter()
                .all(|row| *row == VariableBounds::default())
        );
        Self {
            residual,
            original_edges: Vec::new(),
            rows: HashMap::new(),
            level,
            session,
        }
    }

    fn row(&mut self, key: EndpointKey) -> Result<u32, AdapterError> {
        if let Some(row) = self.rows.get(&key) {
            return Ok(*row);
        }
        let row = self
            .session
            .fresh_value_at_level(self.level)
            .map_err(AdapterError::Availability)?;
        self.rows.insert(key, row);
        Ok(row)
    }

    fn submit(&mut self, edge: OriginalEdge) -> Result<(), AdapterError> {
        // Validate before allocating either endpoint, recording the occurrence,
        // or touching any core state. This is an adapter error, not rejection.
        if edge.source.family_scope != edge.target.family_scope {
            return Err(AdapterError::CrossFamily {
                source: edge.source.family_scope,
                target: edge.target.family_scope,
            });
        }
        let local_slot = u8::try_from(self.original_edges.len())
            .map_err(|_| AdapterError::Availability(SolveAvailabilityError::IdentityExhausted))?;
        let lower = self.row(edge.source)?;
        let upper = self.row(edge.target)?;
        self.original_edges.push(edge);
        let occurrence =
            ConstraintOccurrenceId::new(self.session.batch.projection_order[0].clone(), local_slot);
        let cause = CauseId::for_occurrence(occurrence.clone());
        self.session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(lower),
                    upper: ValueEndpointKey::ValueRow(upper),
                },
                &occurrence,
                &cause,
            )
            .map(|_| ())
            .map_err(AdapterError::Availability)
    }

    fn path(&self, source: EndpointKey, target: EndpointKey) -> PathView {
        if source.family_scope != target.family_scope {
            return PathView::NoPath;
        }
        if source == target {
            return PathView::Refl;
        }
        let (Some(&start), Some(&finish)) = (self.rows.get(&source), self.rows.get(&target)) else {
            return PathView::NoPath;
        };
        let mut queue = VecDeque::from([start]);
        let mut seen = HashSet::from([start]);
        let mut predecessor = HashMap::new();
        while let Some(row) = queue.pop_front() {
            // Search the actual core direct graph, not a parallel graph model.
            for &next in &self.session.bounds[row as usize].direct_upper_rows {
                if !seen.insert(next) {
                    continue;
                }
                let occurrence = self
                    .original_edges
                    .iter()
                    .position(|edge| {
                        self.rows[&edge.source] == row && self.rows[&edge.target] == next
                    })
                    .expect("every core direct edge has an original occurrence");
                let edge = self.original_edges[occurrence];
                assert_eq!(edge.source.family_scope, source.family_scope);
                assert_eq!(edge.target.family_scope, source.family_scope);
                predecessor.insert(next, (row, occurrence));
                if next == finish {
                    let mut recipe = Vec::new();
                    let mut cursor = finish;
                    while cursor != start {
                        let &(previous, occurrence) = &predecessor[&cursor];
                        recipe.push(occurrence);
                        cursor = previous;
                    }
                    recipe.reverse();
                    return PathView::OriginalCompose(recipe);
                }
                queue.push_back(next);
            }
        }
        PathView::NoPath
    }

    fn assert_row_only(&self) {
        for &row in self.rows.values() {
            assert_eq!(self.session.value_levels[row as usize], self.level);
            let bounds = &self.session.bounds[row as usize];
            assert!(bounds.exact_non_variable_lowers.is_empty());
            assert!(bounds.exact_non_variable_uppers.is_empty());
            assert!(!bounds.has_int_positive_lower);
        }
        assert!(
            self.session
                .effect_bounds
                .iter()
                .all(|row| *row == EffectBounds::default())
        );
        for pair in self.session.typed_pairs.keys() {
            assert!(matches!(
                pair,
                TypedPairKey::Value(CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(_),
                    upper: ValueEndpointKey::ValueRow(_),
                })
            ));
        }
        assert!(self.session.errors.is_empty());
        assert!(self.session.typed_worklist.is_empty());
    }
}

// Deliberately not Clone. These finite tags discriminate erasure/mutation;
// they are NOT authentic Call certificates, semantic models or witnesses.
struct SyntheticResidual {
    ordered_proof_choices: [u32; 2],
    provider: u32,
    world: u32,
    dependent_tail: [u32; 3],
}

fn synthetic_residual() -> Arc<SyntheticResidual> {
    Arc::new(SyntheticResidual {
        ordered_proof_choices: [91, 37],
        provider: 12,
        world: 24,
        dependent_tail: [91, 37, 63],
    })
}

fn endpoint(scope: u32, reference: u32, role: EndpointRole) -> EndpointKey {
    EndpointKey {
        family_scope: SyntheticFamilyScope(scope),
        nominal_reference: reference,
        role,
    }
}

fn original(source: EndpointKey, target: EndpointKey, proof_slot: usize) -> OriginalEdge {
    OriginalEdge {
        source,
        target,
        proof_slot,
    }
}

#[test]
fn complete_bound_constraints_store_unknown_formal_and_retain_duplicate_slots() {
    let residual = synthetic_residual();
    let mut store = CompleteBoundStore::new(residual.clone(), 3);
    let a = endpoint(1, 10, EndpointRole::Flexible);
    let f = endpoint(1, 20, EndpointRole::Fixed);
    let l = endpoint(1, 30, EndpointRole::Fixed);
    store.submit(original(a, f, 71)).unwrap();
    assert!(
        store.session.bounds[store.rows[&a] as usize]
            .direct_lower_rows
            .is_empty()
    );
    store.assert_row_only();
    store.submit(original(l, a, 72)).unwrap();
    let pairs = store.session.typed_pairs.len();
    let bounds = store.session.bounds.clone();
    store.submit(original(a, f, 73)).unwrap();
    assert_eq!(store.session.typed_pairs.len(), pairs);
    assert_eq!(store.session.bounds, bounds);
    assert_eq!(
        store.original_edges,
        vec![original(a, f, 71), original(l, a, 72), original(a, f, 73)]
    );
    assert_eq!(
        store.session.bounds[store.rows[&a] as usize].direct_upper_rows,
        vec![store.rows[&f]]
    );
    assert_eq!(
        store.session.bounds[store.rows[&f] as usize].direct_lower_rows,
        vec![store.rows[&a]]
    );
    assert_eq!(
        store.session.bounds[store.rows[&l] as usize].direct_upper_rows,
        vec![store.rows[&a]]
    );
    assert_eq!(store.path(l, f), PathView::OriginalCompose(vec![1, 0]));
    let PathView::OriginalCompose(recipe) = store.path(l, f) else {
        panic!("path");
    };
    assert_eq!(
        recipe
            .iter()
            .map(|&i| store.original_edges[i].proof_slot)
            .collect::<Vec<_>>(),
        vec![72, 71]
    );
    assert!(Arc::ptr_eq(&store.residual, &residual));
    assert_eq!(residual.ordered_proof_choices, [91, 37]);
    assert_eq!(
        (residual.provider, residual.world, residual.dependent_tail),
        (12, 24, [91, 37, 63])
    );
    assert_eq!(store.rows.len(), 3);
    assert_eq!(
        store.rows.values().copied().collect::<HashSet<_>>().len(),
        3
    );
    store.assert_row_only();
}

#[test]
fn complete_bound_constraints_cycle_scope_identity_and_atomic_family_guard() {
    let residual = synthetic_residual();
    let mut store = CompleteBoundStore::new(residual.clone(), 4);
    let a = endpoint(1, 10, EndpointRole::Flexible);
    let b = endpoint(1, 20, EndpointRole::Flexible);
    let c = endpoint(1, 30, EndpointRole::Fixed);
    for edge in [original(a, b, 81), original(b, a, 82), original(b, c, 83)] {
        store.submit(edge).unwrap();
    }
    assert_ne!(store.rows[&a], store.rows[&b]);
    assert_eq!(store.path(a, c), PathView::OriginalCompose(vec![0, 2]));
    assert_eq!(store.path(b, a), PathView::OriginalCompose(vec![1]));
    assert_eq!(store.path(a, a), PathView::Refl);
    assert_eq!(store.path(c, a), PathView::NoPath);
    let scoped_b = endpoint(2, 20, EndpointRole::Flexible);
    let scoped_c = endpoint(2, 30, EndpointRole::Fixed);
    store.submit(original(scoped_b, scoped_c, 84)).unwrap();
    assert_ne!(store.rows[&b], store.rows[&scoped_b]);
    assert_eq!(store.path(a, scoped_c), PathView::NoPath);
    let fixed_b = endpoint(1, 20, EndpointRole::Fixed);
    store.submit(original(fixed_b, c, 85)).unwrap();
    assert_ne!(store.rows[&b], store.rows[&fixed_b]);
    assert_eq!(store.path(a, fixed_b), PathView::NoPath);

    let edges = store.original_edges.clone();
    let rows = store.rows.clone();
    let bounds = store.session.bounds.clone();
    let effects = store.session.effect_bounds.clone();
    let levels = store.session.value_levels.clone();
    let effect_levels = store.session.effect_levels.clone();
    let memos = store.session.typed_pairs.clone();
    let original_residual = store.residual.clone();
    let new_source = endpoint(3, 40, EndpointRole::Flexible);
    let new_target = endpoint(4, 50, EndpointRole::Fixed);
    let error = store
        .submit(original(new_source, new_target, 86))
        .unwrap_err();
    assert!(matches!(
        error,
        AdapterError::CrossFamily {
            source: SyntheticFamilyScope(3),
            target: SyntheticFamilyScope(4),
        }
    ));
    assert_eq!(store.original_edges, edges);
    assert_eq!(store.rows, rows);
    assert_eq!(store.session.bounds, bounds);
    assert_eq!(store.session.effect_bounds, effects);
    assert_eq!(store.session.value_levels, levels);
    assert_eq!(store.session.effect_levels, effect_levels);
    assert_eq!(store.session.typed_pairs, memos);
    assert!(Arc::ptr_eq(&store.residual, &original_residual));
    assert!(Arc::ptr_eq(&store.residual, &residual));
    store.assert_row_only();
}
