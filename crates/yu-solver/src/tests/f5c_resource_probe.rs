use super::*;

#[cfg(feature = "f5c_resource_probe")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum F5cMatrixFamily {
    IndependentIdentities,
    IdentityAliases,
    SharedAcyclic,
    IndependentAcyclic,
    GuardedCycle,
    Normalization,
    ArenaFactor,
}

#[cfg(feature = "f5c_resource_probe")]
impl F5cMatrixFamily {
    const ALL: [Self; 7] = [Self::IndependentIdentities, Self::IdentityAliases,
        Self::SharedAcyclic, Self::IndependentAcyclic, Self::GuardedCycle,
        Self::Normalization, Self::ArenaFactor];

    fn parse(name: &str) -> Option<Self> {
        Some(match name {
            "independent_identities" => Self::IndependentIdentities,
            "identity_aliases" => Self::IdentityAliases,
            "shared_acyclic" => Self::SharedAcyclic,
            "independent_acyclic" => Self::IndependentAcyclic,
            "guarded_cycle" => Self::GuardedCycle,
            "normalization" => Self::Normalization,
            "arena_factor" => Self::ArenaFactor,
            _ => return None,
        })
    }
}

#[cfg(feature = "f5c_resource_probe")]
#[derive(Clone, Copy, Debug)]
struct F5cMatrixCase {
    family: F5cMatrixFamily,
    dimension: char,
    size: usize,
    companion: Option<usize>,
    emit: bool,
}

#[cfg(feature = "f5c_resource_probe")]
impl F5cMatrixCase {
    fn from_env() -> Self {
        let required = |name| std::env::var(name).unwrap_or_else(|_| panic!("missing {name}"));
        let family = F5cMatrixFamily::parse(&required("F5C_RESOURCE_MATRIX_FAMILY"))
            .expect("unknown F5c matrix family");
        let dimension = match required("F5C_RESOURCE_MATRIX_DIMENSION").as_str() {
            "D" => 'D', "K" => 'K', "M" => 'M', "U" => 'U',
            _ => panic!("unknown F5c matrix dimension"),
        };
        let size = match required("F5C_RESOURCE_MATRIX_SIZE").as_str() {
            "1000" => 1000, "2000" => 2000, "4000" => 4000,
            _ => panic!("F5c matrix size must be 1000, 2000, or 4000"),
        };
        let companion = match required("F5C_RESOURCE_MATRIX_COMPANION").as_str() {
            "none" => None, "8" => Some(8), "1000" => Some(1000),
            "4000" => Some(4000),
            _ => panic!("invalid F5c matrix companion"),
        };
        let valid = match family {
            F5cMatrixFamily::IndependentIdentities => dimension == 'D' && companion.is_none(),
            F5cMatrixFamily::IdentityAliases => dimension == 'U' && companion.is_none(),
            F5cMatrixFamily::SharedAcyclic | F5cMatrixFamily::IndependentAcyclic
            | F5cMatrixFamily::Normalization => {
                matches!(dimension, 'D' | 'K') && companion == Some(8)
            }
            F5cMatrixFamily::GuardedCycle => match dimension {
                'D' => companion == Some(4000),
                'K' => companion == Some(8),
                _ => false,
            },
            F5cMatrixFamily::ArenaFactor => matches!(dimension, 'M' | 'U') && companion == Some(1000),
        };
        assert!(valid, "tuple is outside the approved F5c matrix");
        Self { family, dimension, size, companion, emit: true }
    }

    fn parameters(self) -> (usize, usize) {
        match self.companion {
            None => (self.size, 0),
            Some(other) if matches!(self.dimension, 'D' | 'M') => (self.size, other),
            Some(other) => (other, self.size),
        }
    }
}

struct CandidateProbeResult {
    schemes: Vec<Option<Vec<u64>>>,
    normalization: [usize; 4],
}

impl CandidateProbeResult {
    fn assert_parity(&self, other: &Self) {
        assert_eq!(self.normalization, other.normalization);
        assert_eq!(self.schemes.len(), other.schemes.len());
        assert_eq!(self.schemes, other.schemes, "boxed and flat schemes differ");
    }

    fn retained_bytes(&self) -> usize {
        let outer = self
            .schemes
            .capacity()
            .checked_mul(std::mem::size_of::<Option<Vec<u64>>>())
            .and_then(|bytes| bytes.checked_add(std::mem::size_of::<Self>()))
            .expect("parity result capacity fits");
        self.schemes.iter().flatten().fold(outer, |bytes, tokens| {
            bytes
                .checked_add(
                    tokens
                        .capacity()
                        .checked_mul(std::mem::size_of::<u64>())
                        .expect("parity token capacity fits"),
                )
                .expect("parity result capacity fits")
        })
    }
}

// The token stream follows yu-types::alpha_eq's bound-first, then predicate,
// ordered traversal. Each binder gets its first-seen ordinal in its own class.
// This is an exact canonical form for that ordered alpha-equivalence relation.
fn candidate_scheme_tokens(view: yu_types::ClosedValueSchemeView<'_>) -> Vec<u64> {
    use yu_types::{NegativeValueView as N, PositiveValueView as P};
    enum Visit {
        Positive(yu_types::PositiveValueId),
        Negative(yu_types::NegativeValueId),
        Bind(u32),
    }
    let mut tokens = vec![
        view.quantifier_count() as u64,
        view.recursive_bounds().len() as u64,
    ];
    let mut quantifiers = std::collections::HashMap::new();
    let mut recursive = std::collections::HashMap::new();
    let mut roots = Vec::new();
    for bound in view.recursive_bounds() {
        let yu_types::NeutralValueView::Bounds { lower, upper } =
            view.neutral_value(bound.bounds()).unwrap();
        roots.push(Visit::Bind(bound.binder().ordinal()));
        roots.push(Visit::Positive(lower));
        roots.push(Visit::Negative(upper));
    }
    roots.push(Visit::Positive(view.predicate()));
    let mut pending: Vec<_> = roots.into_iter().rev().collect();
    while let Some(next) = pending.pop() {
        match next {
            Visit::Bind(ordinal) => {
                let next = recursive.len() as u64;
                tokens.push(*recursive.entry(ordinal).or_insert(next));
            }
            Visit::Positive(id) => match view.positive_value(id).unwrap() {
                P::Bottom => tokens.push(1),
                P::Int => tokens.push(2),
                P::Quantified(id) => {
                    tokens.push(3);
                    let next = quantifiers.len() as u64;
                    tokens.push(*quantifiers.entry(id.ordinal()).or_insert(next));
                }
                P::Recursive(id) => {
                    tokens.push(4);
                    let next = recursive.len() as u64;
                    tokens.push(*recursive.entry(id.ordinal()).or_insert(next));
                }
                P::Function {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } => {
                    assert!(matches!(
                        view.negative_effect(argument_effect),
                        Ok(yu_types::NegativeEffectView::Empty)
                    ));
                    assert!(matches!(
                        view.positive_effect(result_effect),
                        Ok(yu_types::PositiveEffectView::Bottom)
                    ));
                    tokens.push(5);
                    pending.push(Visit::Positive(result));
                    pending.push(Visit::Negative(argument));
                }
                P::Union(children) => {
                    tokens.extend([6, children.len() as u64]);
                    pending.extend(children.iter().rev().copied().map(Visit::Positive));
                }
            },
            Visit::Negative(id) => match view.negative_value(id).unwrap() {
                N::Top => tokens.push(7),
                N::Bottom => tokens.push(8),
                N::Int => tokens.push(9),
                N::Quantified(id) => {
                    tokens.push(10);
                    let next = quantifiers.len() as u64;
                    tokens.push(*quantifiers.entry(id.ordinal()).or_insert(next));
                }
                N::Recursive(id) => {
                    tokens.push(11);
                    let next = recursive.len() as u64;
                    tokens.push(*recursive.entry(id.ordinal()).or_insert(next));
                }
                N::Function {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } => {
                    assert!(matches!(
                        view.positive_effect(argument_effect),
                        Ok(yu_types::PositiveEffectView::Bottom)
                    ));
                    assert!(matches!(
                        view.negative_effect(result_effect),
                        Ok(yu_types::NegativeEffectView::Empty)
                    ));
                    tokens.push(12);
                    pending.push(Visit::Negative(result));
                    pending.push(Visit::Positive(argument));
                }
                N::Intersection(children) => {
                    tokens.extend([13, children.len() as u64]);
                    pending.extend(children.iter().rev().copied().map(Visit::Negative));
                }
            },
        }
    }
    tokens
}

fn candidate_result(session: &InferenceSession) -> CandidateProbeResult {
    let finalization = session.finalization.as_ref().unwrap();
    let schemes = session
        .schemes
        .iter()
        .map(|scheme| {
            scheme
                .as_ref()
                .map(|scheme| candidate_scheme_tokens(finalization.scheme_view(scheme).unwrap()))
        })
        .collect();
    let counters = &session.execution_counters;
    CandidateProbeResult {
        schemes,
        normalization: [
            counters.closed_normalized_key_writes,
            counters.closed_normalization_child_comparisons,
            counters.closed_normalization_descriptor_words,
            counters.closed_normalization_word_comparisons,
        ],
    }
}

fn candidate_probe_run(
    name: &str,
    source: &str,
    flat: bool,
    normalization_failure_after: Option<usize>,
    precommit_failure: Option<FlatCandidatePrecommitFailure>,
    paired_parity_bytes: usize,
) -> CandidateProbeResult {
    let capture = flat.then(|| {
        F5cCandidateCapture::with_reserved_history()
            .expect("candidate capture incomplete: history reservation failed")
    });
    let batch = collect(module(source, name));
    let max_scc_members = batch.counters.scc_maximum_component_size;
    let mut session = InferenceSession::new(batch);
    session.flat_candidate_enabled = flat;
    session.flat_candidate_normalization_failure_after = normalization_failure_after;
    session.flat_candidate_precommit_failure = precommit_failure;
    session.f5c_candidate_capture = capture;
    session.admit_all_collected_facts().unwrap();
    let result = session.execute_scc_plan();
    assert_eq!(
        result.is_err(),
        normalization_failure_after.is_some() || precommit_failure.is_some()
    );
    if result.is_err() {
        assert!(session.schemes.iter().all(Option::is_none));
        assert_eq!(session.resource_ledger.flat_all_drafts_members, 0);
        assert!(session.resource_ledger.flat_transfer_peak_bytes > 0);
    }
    if let Some(capture) = session.f5c_candidate_capture.take() {
        if result.is_err() {
            let mut expected = capture
                .transactional_counter_baseline
                .as_ref()
                .unwrap()
                .clone();
            let actual = &session.execution_counters;
            assert!(actual.semantic_arena_peak_bytes >= expected.semantic_arena_peak_bytes);
            assert!(actual.inference_session_peak_bytes >= expected.inference_session_peak_bytes);
            assert!(
                actual.component_expansion_memo_requested_slots
                    > expected.component_expansion_memo_requested_slots
            );
            assert!(
                actual.component_expansion_memo_capacity_growths
                    > expected.component_expansion_memo_capacity_growths
            );
            assert!(
                actual.component_expansion_memo_peak_bytes
                    > expected.component_expansion_memo_peak_bytes
            );
            assert_eq!(actual.component_expansion_memo_actual_capacity, 0);
            assert_eq!(actual.component_expansion_memo_retained_bytes, 0);
            expected.semantic_arena_peak_bytes = actual.semantic_arena_peak_bytes;
            expected.inference_session_peak_bytes = actual.inference_session_peak_bytes;
            expected.component_expansion_memo_requested_slots =
                actual.component_expansion_memo_requested_slots;
            expected.component_expansion_memo_capacity_growths =
                actual.component_expansion_memo_capacity_growths;
            expected.component_expansion_memo_peak_bytes =
                actual.component_expansion_memo_peak_bytes;
            assert_eq!(
                *actual, expected,
                "transactional counters changed on failure"
            );
            assert_eq!(
                session
                    .resource_ledger
                    .component_expansion_memo_actual_capacity,
                0
            );
            assert_eq!(
                session
                    .resource_ledger
                    .component_expansion_memo_retained_bytes,
                0
            );
            let event = capture.records.last().expect("failure event sample");
            assert!(event.boundary.is_none());
            assert!(event.failure_site.is_some());
            assert_eq!(
                event.last_successful_boundary,
                Some(ResourceBoundary::SourceDrafts)
            );
            let retained = &session.resource_ledger;
            for (before, after) in event.memo_lanes.iter().zip([
                &retained.component_expansion_memo_roots,
                &retained.component_expansion_memo_nodes,
                &retained.component_expansion_memo_children,
                &retained.component_expansion_memo_index,
                &retained.component_expansion_memo_scratch,
            ]) {
                assert!(after.peak_capacity >= before.peak_capacity);
                assert!(after.peak_bytes >= before.peak_bytes);
            }
            for (before, after) in event
                .walker_lanes
                .iter()
                .zip(&retained.generalization_walker_lanes)
            {
                assert!(after.peak_capacity >= before.peak_capacity);
                assert!(after.peak_bytes >= before.peak_bytes);
            }
            for (before, after) in event
                .index_lanes
                .iter()
                .zip(&retained.closed_normalization_index_lanes)
            {
                assert!(after.peak_capacity >= before.peak_capacity);
                assert!(after.peak_bytes >= before.peak_bytes);
            }
        }
        eprintln!(
            "F5C_CANDIDATE_SUMMARY\tcase={name}\tsource_bytes={}\tmax_scc_members={max_scc_members}\tpaired_parity_capacity_bytes={paired_parity_bytes}\ttest_capture_inline_bytes={}\tcapture_record_capacity_bytes={}\tboundary_order_capacity_bytes={}\tboundary_samples_capacity_bytes={}\tnormalizer_physical_samples_capacity_bytes={}\tmember_output_length_samples_capacity_bytes={}",
            source.len(),
            std::mem::size_of::<F5cCandidateCapture>(),
            capture.bytes(),
            session.resource_ledger.boundary_order.capacity()
                * std::mem::size_of::<ResourceBoundary>(),
            capture.diagnostic_capacity_bytes[0],
            capture.diagnostic_capacity_bytes[1],
            capture.diagnostic_capacity_bytes[2]
        );
        for record in &capture.records {
            record.emit(name);
        }
        eprintln!(
            "F5C_CANDIDATE_OUTPUT_LENGTHS\tcase={name}\tsamples={:?}",
            &capture.output_lengths[..capture.output_length_count]
        );
    }
    candidate_result(&session)
}

struct SourceLambdaCase {
    name: String,
    source: String,
    bytes: usize,
    definitions: usize,
    components: usize,
    max_members: usize,
    uses: usize,
    internal_uses: usize,
    recursive: bool,
}

fn source_lambda_cases() -> Vec<SourceLambdaCase> {
    let mut cases = vec![
        ("identity", "my f x = x", 10, 1, 1, 1, 0, 0, false),
        ("constant", "my k x = 42", 11, 1, 1, 1, 0, 0, false),
        (
            "name_body",
            "my n = 42; my f x = n",
            21,
            2,
            2,
            1,
            1,
            0,
            false,
        ),
        ("self_recursive", "my f x = f", 10, 1, 1, 1, 1, 1, true),
    ]
    .into_iter()
    .map(
        |(
            name,
            source,
            bytes,
            definitions,
            components,
            max_members,
            uses,
            internal_uses,
            recursive,
        )| SourceLambdaCase {
            name: name.into(),
            source: source.into(),
            bytes,
            definitions,
            components,
            max_members,
            uses,
            internal_uses,
            recursive,
        },
    )
    .collect::<Vec<_>>();
    for (n, bytes) in [(2, 26), (4, 54), (8, 110), (16, 234)] {
        cases.push(SourceLambdaCase {
            name: format!("function_ring_{n}"),
            source: (0..n)
                .map(|i| format!("my n{i} x = n{}", (i + 1) % n))
                .collect::<Vec<_>>()
                .join("; "),
            bytes,
            definitions: n,
            components: 1,
            max_members: n,
            uses: n,
            internal_uses: n,
            recursive: true,
        });
    }
    cases
}

fn checked_source_lambda_batch(case: &SourceLambdaCase) -> ConstraintBatch {
    assert_eq!(case.source.len(), case.bytes, "{} UTF-8 bytes", case.name);
    let hir = module(&case.source, &case.name);
    assert!(
        hir.diagnostics().is_empty(),
        "{} HIR diagnostics",
        case.name
    );
    let batch = collect(hir);
    assert_eq!(batch.definitions().len(), case.definitions);
    assert!(
        batch
            .definitions()
            .iter()
            .all(|definition| definition.body_status() == CollectedBodyStatus::Complete)
    );
    assert_eq!(
        batch.lambda_recipes.len(),
        if case.name == "name_body" {
            1
        } else {
            case.definitions
        }
    );
    assert_eq!(batch.definition_uses().len(), case.uses);
    let components = batch
        .scc_components_in_dependency_first_order()
        .collect::<Vec<_>>();
    assert_eq!(components.len(), case.components);
    assert_eq!(
        components
            .iter()
            .map(|component| batch.scc_component_members(component).unwrap().len())
            .max(),
        Some(case.max_members)
    );
    assert_eq!(
        components
            .iter()
            .map(|component| batch.scc_component_internal_uses(component).unwrap().len())
            .sum::<usize>(),
        case.internal_uses
    );
    if case.name == "name_body" {
        assert_eq!(
            components
                .iter()
                .map(|component| batch.scc_component_incoming_uses(component).unwrap().len())
                .sum::<usize>(),
            1
        );
    }
    batch
}

fn source_lambda_run(
    case: &SourceLambdaCase,
    flat: bool,
    capture_enabled: bool,
    fail: bool,
    paired_parity_bytes: usize,
) -> CandidateProbeResult {
    let batch = checked_source_lambda_batch(case);
    let mut session = InferenceSession::new(batch);
    session.flat_candidate_enabled = flat;
    session.flat_candidate_normalization_failure_after = fail.then_some(0);
    session.f5c_candidate_capture = (flat && capture_enabled).then(|| {
        F5cCandidateCapture::with_reserved_history().expect("candidate capture history reservation")
    });
    session.admit_all_collected_facts().unwrap();
    let execution = session.execute_scc_plan();
    if fail {
        assert_eq!(execution, Err(SolveAvailabilityError::IdentityExhausted));
    } else {
        execution.unwrap();
    }
    if fail {
        assert!(session.schemes.iter().all(Option::is_none));
    } else {
        assert_eq!(session.schemes.iter().flatten().count(), case.definitions);
        if case.recursive {
            for scheme in session.schemes.iter().flatten() {
                let view = session
                    .finalization
                    .as_ref()
                    .unwrap()
                    .scheme_view(scheme)
                    .unwrap();
                assert!(
                    !view.recursive_bounds().is_empty(),
                    "{} recursive bounds",
                    case.name
                );
                assert!(
                    matches!(
                        view.positive_value(view.predicate()).unwrap(),
                        yu_types::PositiveValueView::Function { .. }
                    ),
                    "{} productive Function",
                    case.name
                );
            }
        }
    }
    if let Some(capture) = session.f5c_candidate_capture.take() {
        let expected = if fail {
            2
        } else {
            2 * case.components + 3 * case.definitions
        };
        assert!(expected <= 64);
        assert_eq!(
            capture.records.len(),
            expected,
            "{} capture cardinality",
            case.name
        );
        if fail {
            let mut expected = capture
                .transactional_counter_baseline
                .as_ref()
                .unwrap()
                .clone();
            let actual = &session.execution_counters;
            assert!(actual.semantic_arena_peak_bytes >= expected.semantic_arena_peak_bytes);
            assert!(actual.inference_session_peak_bytes >= expected.inference_session_peak_bytes);
            assert!(
                actual.component_expansion_memo_requested_slots
                    > expected.component_expansion_memo_requested_slots
            );
            assert!(
                actual.component_expansion_memo_capacity_growths
                    > expected.component_expansion_memo_capacity_growths
            );
            assert!(
                actual.component_expansion_memo_peak_bytes
                    > expected.component_expansion_memo_peak_bytes
            );
            assert_eq!(actual.component_expansion_memo_actual_capacity, 0);
            assert_eq!(actual.component_expansion_memo_retained_bytes, 0);
            expected.semantic_arena_peak_bytes = actual.semantic_arena_peak_bytes;
            expected.inference_session_peak_bytes = actual.inference_session_peak_bytes;
            expected.component_expansion_memo_requested_slots =
                actual.component_expansion_memo_requested_slots;
            expected.component_expansion_memo_capacity_growths =
                actual.component_expansion_memo_capacity_growths;
            expected.component_expansion_memo_peak_bytes =
                actual.component_expansion_memo_peak_bytes;
            assert_eq!(
                *actual, expected,
                "transactional counters changed on failure"
            );
            assert_eq!(
                session
                    .resource_ledger
                    .component_expansion_memo_actual_capacity,
                0
            );
            assert_eq!(
                session
                    .resource_ledger
                    .component_expansion_memo_retained_bytes,
                0
            );
            assert_eq!(
                capture.records[0].boundary,
                Some(ResourceBoundary::SourceDrafts)
            );
            assert_eq!(capture.records[0].component, 1);
            assert_eq!(capture.records[0].member, None);
            assert_eq!(capture.records[0].failure_site, None);
            let event = &capture.records[1];
            assert_eq!(event.boundary, None);
            assert_eq!(event.failure_site, Some("batch_normalization"));
            assert_eq!(event.component, 1);
            assert_eq!(event.member, None);
            assert_eq!(
                event.last_successful_boundary,
                Some(ResourceBoundary::SourceDrafts)
            );
            let retained = &session.resource_ledger;
            for (before, after) in event.memo_lanes.iter().zip([
                &retained.component_expansion_memo_roots,
                &retained.component_expansion_memo_nodes,
                &retained.component_expansion_memo_children,
                &retained.component_expansion_memo_index,
                &retained.component_expansion_memo_scratch,
            ]) {
                assert!(after.peak_capacity >= before.peak_capacity);
                assert!(after.peak_bytes >= before.peak_bytes);
            }
            for (before, after) in event
                .walker_lanes
                .iter()
                .zip(&retained.generalization_walker_lanes)
            {
                assert!(after.peak_capacity >= before.peak_capacity);
                assert!(after.peak_bytes >= before.peak_bytes);
            }
            for (before, after) in event
                .index_lanes
                .iter()
                .zip(&retained.closed_normalization_index_lanes)
            {
                assert!(after.peak_capacity >= before.peak_capacity);
                assert!(after.peak_bytes >= before.peak_bytes);
            }
        } else {
            let member_counts = if case.name == "name_body" {
                vec![1, 1]
            } else {
                vec![case.definitions]
            };
            let mut records = capture.records.iter();
            let mut previous = None;
            for (component, members) in member_counts.into_iter().enumerate() {
                let component = component + 1;
                for boundary in [ResourceBoundary::SourceDrafts, ResourceBoundary::AllDrafts] {
                    let record = records.next().unwrap();
                    assert_eq!(record.boundary, Some(boundary));
                    assert_eq!(record.component, component);
                    assert_eq!(record.member, None);
                    assert_eq!(record.failure_site, None);
                    assert_eq!(record.last_successful_boundary, previous);
                    previous = Some(boundary);
                }
                for member in 0..members {
                    for boundary in [
                        ResourceBoundary::IndexedMapping,
                        ResourceBoundary::DraftMember,
                    ] {
                        let record = records.next().unwrap();
                        assert_eq!(record.boundary, Some(boundary));
                        assert_eq!(record.component, component);
                        assert_eq!(record.member, Some(member));
                        assert_eq!(record.failure_site, None);
                        assert_eq!(record.last_successful_boundary, previous);
                        previous = Some(boundary);
                    }
                }
                for member in 0..members {
                    let record = records.next().unwrap();
                    assert_eq!(record.boundary, Some(ResourceBoundary::SchemeInstall));
                    assert_eq!(record.component, component);
                    assert_eq!(record.member, Some(member));
                    assert_eq!(record.failure_site, None);
                    assert_eq!(record.last_successful_boundary, previous);
                    previous = Some(ResourceBoundary::SchemeInstall);
                }
            }
            assert!(records.next().is_none());
        }
        eprintln!(
            "F5C_CANDIDATE_SUMMARY\tcase={}\tsource_bytes={}\tmax_scc_members={}\tpaired_parity_capacity_bytes={}\ttest_capture_inline_bytes={}\tcapture_record_capacity_bytes={}\tboundary_order_capacity_bytes={}\tboundary_samples_capacity_bytes={}\tnormalizer_physical_samples_capacity_bytes={}\tmember_output_length_samples_capacity_bytes={}",
            case.name,
            case.bytes,
            case.max_members,
            paired_parity_bytes,
            std::mem::size_of::<F5cCandidateCapture>(),
            capture.bytes(),
            session.resource_ledger.boundary_order.capacity()
                * std::mem::size_of::<ResourceBoundary>(),
            capture.diagnostic_capacity_bytes[0],
            capture.diagnostic_capacity_bytes[1],
            capture.diagnostic_capacity_bytes[2]
        );
        for record in &capture.records {
            record.emit(&case.name);
        }
        eprintln!(
            "F5C_CANDIDATE_OUTPUT_LENGTHS\tcase={}\tsamples={:?}",
            case.name,
            &capture.output_lengths[..capture.output_length_count]
        );
    }
    candidate_result(&session)
}

#[test]
fn f5c_source_lambda_function_correctness() {
    for case in source_lambda_cases() {
        let boxed = source_lambda_run(&case, false, false, false, 0);
        let flat = source_lambda_run(&case, true, false, false, 0);
        boxed.assert_parity(&flat);
    }
}

#[test]
#[ignore = "manual F5c source Function resource capture"]
fn f5c_candidate_resource_probe_source_functions() {
    let cases = source_lambda_cases();
    for case in &cases {
        let boxed = source_lambda_run(case, false, false, false, 0);
        let flat = source_lambda_run(case, true, true, false, boxed.retained_bytes());
        boxed.assert_parity(&flat);
    }
    let ring = &cases[4];
    source_lambda_run(ring, true, true, true, 0);
    let boxed = source_lambda_run(ring, false, false, false, 0);
    let retry = source_lambda_run(ring, true, true, false, boxed.retained_bytes());
    boxed.assert_parity(&retry);
}

#[test]
fn flat_precommit_failure_releases_memo_without_losing_physical_history() {
    let batch = collect(module(
        "my left = right; my right = left",
        "f5c-flat-failure-release",
    ));
    let mut session = InferenceSession::new(batch);
    session.flat_candidate_enabled = true;
    session.flat_candidate_precommit_failure =
        Some(FlatCandidatePrecommitFailure::LedgerAfterStage);
    session.admit_all_collected_facts().unwrap();
    assert_eq!(
        session.execute_scc_plan(),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert!(session.schemes.iter().all(Option::is_none));
    assert_eq!(session.successful_finalizations, 0);
    let mut before = session
        .flat_candidate_precommit_counter_baseline
        .take()
        .expect("injected failure has an in-batch counter baseline");
    let actual = &session.execution_counters;
    assert_eq!(actual.component_expansion_memo_actual_capacity, 0);
    assert_eq!(actual.component_expansion_memo_retained_bytes, 0);
    assert!(actual.semantic_arena_peak_bytes >= before.semantic_arena_peak_bytes);
    assert!(actual.inference_session_peak_bytes >= before.inference_session_peak_bytes);
    assert!(
        actual.component_expansion_memo_requested_slots
            > before.component_expansion_memo_requested_slots
    );
    assert!(
        actual.component_expansion_memo_capacity_growths
            > before.component_expansion_memo_capacity_growths
    );
    assert!(
        actual.component_expansion_memo_peak_bytes > before.component_expansion_memo_peak_bytes
    );
    before.semantic_arena_peak_bytes = actual.semantic_arena_peak_bytes;
    before.inference_session_peak_bytes = actual.inference_session_peak_bytes;
    before.component_expansion_memo_requested_slots =
        actual.component_expansion_memo_requested_slots;
    before.component_expansion_memo_capacity_growths =
        actual.component_expansion_memo_capacity_growths;
    before.component_expansion_memo_peak_bytes = actual.component_expansion_memo_peak_bytes;
    assert_eq!(*actual, before, "transactional counters changed on failure");
    let ledger = &session.resource_ledger;
    assert_eq!(ledger.component_expansion_memo_actual_capacity, 0);
    assert_eq!(ledger.component_expansion_memo_retained_bytes, 0);
    assert!(ledger.component_expansion_memo_peak_bytes > 0);
    let memo_lanes = [
        &ledger.component_expansion_memo_roots,
        &ledger.component_expansion_memo_nodes,
        &ledger.component_expansion_memo_children,
        &ledger.component_expansion_memo_index,
        &ledger.component_expansion_memo_scratch,
    ];
    for lane in &memo_lanes {
        assert_eq!(lane.actual_capacity, 0);
        assert_eq!(lane.retained_bytes, 0);
    }
    assert!(memo_lanes.iter().any(|lane| lane.requested_slots > 0));
    assert!(memo_lanes.iter().any(|lane| lane.capacity_growths > 0));
    assert!(memo_lanes.iter().any(|lane| lane.peak_bytes > 0));
}

fn candidate_seeded_compound_fixture(depth: usize, width: usize, flat: bool) -> InferenceSession {
    let batch = collect(module(
        "my left = right; my right = left",
        "f5c-candidate-seeded",
    ));
    let mut session = InferenceSession::new(batch);
    session.flat_candidate_enabled = flat;
    session.admit_all_collected_facts().unwrap();
    let component = session
        .batch
        .scc_components_in_dependency_first_order()
        .find(|component| {
            session
                .batch
                .scc_component_members(component)
                .unwrap()
                .len()
                == 2
        })
        .unwrap()
        .clone();
    let members = session
        .batch
        .scc_component_members(&component)
        .unwrap()
        .to_vec();
    let mut seen_roots = std::collections::HashSet::new();
    for member in members {
        let verified = InferenceSession::verified_scheme_definition(&session.batch, &member);
        let position = session
            .batch
            .root_component_positions
            .get(&verified.record.root)
            .unwrap()
            .component;
        if !seen_roots.insert(position) {
            continue;
        }
        let root = session.fresh_value_at_level(1).unwrap();
        session.live_components[position].ordinal = root;
        let relay = session.fresh_value_at_level(1).unwrap();
        let quantified = session.fresh_value_at_level(1).unwrap();
        let first = session.fresh_value_at_level(1).unwrap();
        let second = session.fresh_value_at_level(1).unwrap();
        session.bounds[first as usize]
            .exact_non_variable_lowers
            .push(ValueEndpointKey::IntPositive);
        session.bounds[second as usize]
            .exact_non_variable_uppers
            .push(ValueEndpointKey::IntNegative);
        session.bounds[root as usize]
            .direct_lower_rows
            .push(quantified);
        session.bounds[root as usize]
            .direct_upper_rows
            .push(quantified);
        session.bounds[relay as usize].direct_lower_rows.push(root);
        let mut result = session.live_value_term(Polarity::Positive, relay).unwrap();
        for _ in 0..depth {
            let argument = session.negative_top_term().unwrap();
            result = session
                .positive_function_term(
                    argument,
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    result,
                )
                .unwrap();
        }
        session.bounds[root as usize]
            .exact_non_variable_lowers
            .push(ValueEndpointKey::ValueRow(first));
        session.bounds[root as usize]
            .exact_non_variable_lowers
            .extend(std::iter::repeat_n(
                ValueEndpointKey::PositiveFunction(result),
                width,
            ));
        session.bounds[root as usize]
            .exact_non_variable_uppers
            .extend([
                ValueEndpointKey::TopNegative,
                ValueEndpointKey::ValueRow(second),
            ]);
    }
    assert_eq!(seen_roots.len(), 2);
    session
}

fn candidate_seeded_run(
    name: &str,
    depth: usize,
    width: usize,
    flat: bool,
    paired_parity_bytes: usize,
    capture_enabled: bool,
) -> CandidateProbeResult {
    let capture = (flat && capture_enabled).then(|| {
        F5cCandidateCapture::with_reserved_history()
            .expect("candidate capture incomplete: history reservation failed")
    });
    let mut session = candidate_seeded_compound_fixture(depth, width, flat);
    session.f5c_candidate_capture = capture;
    session.execute_scc_plan().unwrap();
    for scheme in session.schemes.iter().flatten() {
        let view = session
            .finalization
            .as_ref()
            .unwrap()
            .scheme_view(scheme)
            .unwrap();
        assert!(view.quantifier_count() > 0);
        assert!(!view.recursive_bounds().is_empty());
        let mut pending = vec![(view.predicate(), 0usize)];
        pending.extend(view.recursive_bounds().iter().map(|bound| {
            let yu_types::NeutralValueView::Bounds { lower, .. } =
                view.neutral_value(bound.bounds()).unwrap();
            (lower, 0)
        }));
        if width > 1 {
            assert!(
                matches!(
                    view.positive_value(view.predicate()).unwrap(),
                    yu_types::PositiveValueView::Union(_)
                ),
                "predicate retains the width union"
            );
            for &(lower, _) in pending.iter().skip(1) {
                assert!(
                    matches!(
                        view.positive_value(lower).unwrap(),
                        yu_types::PositiveValueView::Union(_)
                    ),
                    "recursive lower bound retains the width union"
                );
            }
        }
        let mut maximum_function_depth = 0;
        while let Some((id, function_depth)) = pending.pop() {
            match view.positive_value(id).unwrap() {
                yu_types::PositiveValueView::Function { result, .. } => {
                    maximum_function_depth = maximum_function_depth.max(function_depth + 1);
                    pending.push((result, function_depth + 1));
                }
                yu_types::PositiveValueView::Union(children) => {
                    let mut unique = std::collections::HashSet::new();
                    assert!(
                        children.iter().all(|child| unique.insert(*child)),
                        "normalized union retains duplicate child IDs"
                    );
                    if width > 1 {
                        let quantified = children
                            .iter()
                            .filter(|child| {
                                matches!(
                                    view.positive_value(**child).unwrap(),
                                    yu_types::PositiveValueView::Quantified(_)
                                )
                            })
                            .count();
                        assert_eq!(children.len(), 2 + quantified);
                        assert!(
                            quantified <= 1,
                            "only the fixture's quantified row may remain"
                        );
                        assert_eq!(
                            children
                                .iter()
                                .filter(|child| matches!(
                                    view.positive_value(**child).unwrap(),
                                    yu_types::PositiveValueView::Int
                                ))
                                .count(),
                            1
                        );
                        assert_eq!(
                            children
                                .iter()
                                .filter(|child| matches!(
                                    view.positive_value(**child).unwrap(),
                                    yu_types::PositiveValueView::Function { .. }
                                ))
                                .count(),
                            1
                        );
                    }
                    pending.extend(children.iter().map(|child| (*child, function_depth)));
                }
                _ => {}
            }
        }
        assert!(
            maximum_function_depth >= depth,
            "seeded Function result chain was not retained"
        );
    }
    if let Some(capture) = session.f5c_candidate_capture.take() {
        eprintln!(
            "F5C_CANDIDATE_SUMMARY\tcase={name}\tinput=synthetic_seeded_term\tdepth={depth}\tduplicate_width={width}\tpaired_parity_capacity_bytes={paired_parity_bytes}\ttest_capture_inline_bytes={}\tcapture_record_capacity_bytes={}\tboundary_order_capacity_bytes={}\tboundary_samples_capacity_bytes={}\tnormalizer_physical_samples_capacity_bytes={}\tmember_output_length_samples_capacity_bytes={}",
            std::mem::size_of::<F5cCandidateCapture>(),
            capture.bytes(),
            session.resource_ledger.boundary_order.capacity()
                * std::mem::size_of::<ResourceBoundary>(),
            capture.diagnostic_capacity_bytes[0],
            capture.diagnostic_capacity_bytes[1],
            capture.diagnostic_capacity_bytes[2]
        );
        for record in &capture.records {
            record.emit(name);
        }
        eprintln!(
            "F5C_CANDIDATE_OUTPUT_LENGTHS\tcase={name}\tsamples={:?}",
            &capture.output_lengths[..capture.output_length_count]
        );
    }
    candidate_result(&session)
}

#[test]
fn f5c_candidate_seeded_width_normalizes_distinct_members() {
    let boxed = candidate_seeded_run("seeded_width_correctness_boxed", 1, 8, false, 0, false);
    let flat = candidate_seeded_run("seeded_width_correctness_flat", 1, 8, true, 0, false);
    boxed.assert_parity(&flat);
}

#[test]
#[ignore = "manual F5c candidate resource capture"]
fn f5c_candidate_resource_probe_scale() {
    for n in [2usize, 4, 8, 16] {
        let source = if n == 2 {
            "my left = right; my right = left".to_owned()
        } else {
            (0..n)
                .map(|index| format!("my n{index} = n{};", (index + 1) % n))
                .collect::<Vec<_>>()
                .join(" ")
        };
        let batch = collect(module(&source, "f5c-candidate-source-ring"));
        assert_eq!(batch.counters.scc_maximum_component_size, n);
        candidate_probe_run(&format!("source_ring_{n}"), &source, true, None, None, 0);
    }
    for depth in [8usize, 32, 64, 256] {
        let boxed = candidate_seeded_run(
            &format!("seeded_depth_{depth}_boxed"),
            depth,
            1,
            false,
            0,
            true,
        );
        let flat = candidate_seeded_run(
            &format!("seeded_depth_{depth}_flat"),
            depth,
            1,
            true,
            boxed.retained_bytes(),
            true,
        );
        boxed.assert_parity(&flat);
    }
    for width in [8usize, 32, 64] {
        let boxed = candidate_seeded_run(
            &format!("seeded_width_{width}_boxed"),
            1,
            width,
            false,
            0,
            true,
        );
        let flat = candidate_seeded_run(
            &format!("seeded_width_{width}_flat"),
            1,
            width,
            true,
            boxed.retained_bytes(),
            true,
        );
        boxed.assert_parity(&flat);
    }
}

#[test]
#[ignore = "manual F5c candidate resource capture"]
fn f5c_candidate_resource_probe_failures() {
    let source = "my left = right; my right = left";
    candidate_probe_run(
        "post_transfer_failure",
        source,
        true,
        None,
        Some(FlatCandidatePrecommitFailure::LedgerAfterStage),
        0,
    );
    let reference = candidate_probe_run("post_transfer_retry", source, true, None, None, 0);
    candidate_probe_run(
        "batch_normalization_failure",
        source,
        true,
        Some(0),
        None,
        reference.retained_bytes(),
    );
    let retry = candidate_probe_run(
        "batch_normalization_retry",
        source,
        true,
        None,
        None,
        reference.retained_bytes(),
    );
    reference.assert_parity(&retry);
    let (records, capacity_bytes) = f5c_normalization::failed_reserve_retry_probe();
    assert_eq!(records.len(), 2);
    assert!(records[0].1 > 0);
    assert!(records[1].1 > records[0].1);
    assert!(records[1].0.capacity_growths > records[0].0.capacity_growths);
    for (ordinal, (record, actual_capacity, actual_bytes)) in records.iter().enumerate() {
        assert_eq!(record.slot_size, std::mem::size_of::<u8>());
        assert_eq!(record.actual_capacity, *actual_capacity);
        assert_eq!(record.retained_bytes, *actual_bytes);
        eprintln!(
            "F5C_CANDIDATE_RESERVE\tordinal={ordinal}\tlane={record:?}\tphysical_capacity={actual_capacity}\tphysical_slot_bytes={}\tphysical_retained_bytes={actual_bytes}\trecord_capacity_bytes={capacity_bytes}",
            std::mem::size_of::<u8>()
        );
    }
}

fn positive_function<'meter>(
    test_source_meter: &'meter DraftHeapMeter,
    argument: F5cNegative<'meter>,
    result: F5cPositive<'meter>,
) -> F5cPositive<'meter> {
    F5cPositive::Function {
        argument: test_tracked_one(&test_source_meter, argument),
        argument_effect: F5cNegativeEffect::Empty,
        result_effect: F5cPositiveEffect::Bottom,
        result: test_tracked_one(&test_source_meter, result),
    }
}

fn report_normalization<'meter>(
    test_source_meter: &'meter DraftHeapMeter,
    case: &str,
    drafts: &mut [GeneralizationDraft<'meter>],
) -> f5c_normalization::NormalizationStats {
    let stats = f5c_normalization::normalize_component(&test_source_meter, drafts)
        .expect("measurement fixture normalizes");
    let [
        nodes,
        children,
        walk,
        values,
        roots,
        height_counts,
        height_offsets,
        height_nodes,
        sort_scratch,
        descriptor_words,
        output,
        radix_frames,
        radix_workspace,
    ] = stats.index_lanes;
    eprintln!(
        "F5C_RESOURCE_PROBE\tcase={case}\tkey_writes={}\tchild_comparisons={}\tdescriptor_words={}\tword_comparisons={}\tduplicates={}\tnode_slots={}\tchild_slots={}\troot_slots={}\tpeak_scratch_bytes={}\tlanes(nodes,children,walk,values,roots,height_counts,height_offsets,height_nodes,sort_scratch,descriptor_words,output,radix_frames,radix_workspace)={:?}",
        stats.key_writes,
        stats.child_comparisons,
        stats.descriptor_words,
        stats.word_comparisons,
        stats.duplicates,
        nodes.requested_slots,
        children.requested_slots,
        roots.requested_slots,
        stats.index_peak_bytes,
        [
            nodes,
            children,
            walk,
            values,
            roots,
            height_counts,
            height_offsets,
            height_nodes,
            sort_scratch,
            descriptor_words,
            output,
            radix_frames,
            radix_workspace,
        ]
        .map(|lane| (
            lane.requested_slots,
            lane.peak_capacity,
            lane.slot_size,
            lane.peak_bytes
        ))
    );
    assert!(stats.index_peak_bytes > 0);
    stats
}

fn draft(predicate: F5cPositive, quantifier_count: usize) -> GeneralizationDraft {
    GeneralizationDraft {
        quantifier_count: u32::try_from(quantifier_count).unwrap(),
        recursive_bounds: Vec::new(),
        predicate,
    }
}

fn drain_positive_function_chain(mut value: F5cPositive) -> usize {
    let mut depth = 0;
    loop {
        match value {
            F5cPositive::Function {
                argument, result, ..
            } => {
                assert!(matches!(*argument, F5cNegative::Top));
                depth += 1;
                value = result.into_inner();
            }
            F5cPositive::Int => return depth,
            _ => panic!("probe output remains a Function chain"),
        }
    }
}

fn count_positive_union_tree(root: &F5cPositive) -> (usize, usize) {
    let mut pending = vec![root];
    let mut nodes = 0usize;
    let mut edges = 0usize;
    while let Some(value) = pending.pop() {
        nodes += 1;
        match value {
            F5cPositive::Union(children) => {
                edges += children.len();
                pending.extend(children.iter());
            }
            F5cPositive::Int => {}
            _ => panic!("shared-summary probe expands only Union and Int nodes"),
        }
    }
    (nodes, edges)
}

#[test]
#[ignore = "manual resource probe; printed counts are diagnostic, not a limit"]
fn f5c_resource_probe_scale_families() {
    let test_source_meter = DraftHeapMeter::default();
    for depth in [64usize, 256, 1024, 4096] {
        let mut value = F5cPositive::Int;
        for _ in 0..depth {
            value = positive_function(&test_source_meter, F5cNegative::Top, value);
        }
        let mut drafts = [draft(value, 0)];
        report_normalization(
            &test_source_meter,
            &format!("function_chain_depth_{depth}"),
            &mut drafts,
        );
        let value = std::mem::replace(&mut drafts[0].predicate, F5cPositive::Bottom);
        assert_eq!(drain_positive_function_chain(value), depth);
    }

    for width in [16usize, 64, 256, 1024] {
        let members = (0..width)
            .map(|ordinal| F5cPositive::Quantified(ordinal as u32))
            .collect::<Vec<_>>();
        let mut drafts = [draft(
            F5cPositive::Union(test_tracked(&test_source_meter, members)),
            width,
        )];
        report_normalization(
            &test_source_meter,
            &format!("unique_union_width_{width}"),
            &mut drafts,
        );
        let F5cPositive::Union(members) =
            std::mem::replace(&mut drafts[0].predicate, F5cPositive::Bottom)
        else {
            panic!("wide normalized result remains a Union");
        };
        assert_eq!(members.len(), width);
    }

    for width in [16usize, 64, 256, 1024] {
        let members = (0..width)
            .map(|_| positive_function(&test_source_meter, F5cNegative::Top, F5cPositive::Int))
            .collect::<Vec<_>>();
        let mut drafts = [draft(
            F5cPositive::Union(test_tracked(&test_source_meter, members)),
            0,
        )];
        let stats = report_normalization(
            &test_source_meter,
            &format!("duplicate_union_width_{width}"),
            &mut drafts,
        );
        assert_eq!(stats.duplicates, width - 1);
        let F5cPositive::Union(members) =
            std::mem::replace(&mut drafts[0].predicate, F5cPositive::Bottom)
        else {
            panic!("duplicate-heavy normalized result remains a Union");
        };
        assert_eq!(members.len(), 1);
    }

    for root_count in [8usize, 32, 128] {
        let mut drafts = (0..root_count)
            .map(|ordinal| draft(F5cPositive::Quantified(ordinal as u32), root_count))
            .collect::<Vec<_>>();
        report_normalization(
            &test_source_meter,
            &format!("independent_roots_{root_count}"),
            &mut drafts,
        );
        for draft in &mut drafts {
            let value = std::mem::replace(&mut draft.predicate, F5cPositive::Bottom);
            assert!(matches!(value, F5cPositive::Quantified(_)));
        }
    }

    for depth in [4usize, 8, 12] {
        let mut memo = F5cComponentExpansionMemo::default();
        let mut root = memo
            .push_node(F5cSummaryNodeKind::PositiveInt, None)
            .unwrap();
        for _ in 0..depth {
            let (start, len) = memo.push_children(&[root, root]).unwrap();
            root = memo
                .push_node(F5cSummaryNodeKind::PositiveUnion { start, len }, None)
                .unwrap();
        }
        let expanded = memo.positive_value(&test_source_meter, root).unwrap();
        let (output_nodes, output_edges) = count_positive_union_tree(&expanded);
        let tasks = memo.walker_resources.lanes[F5cWalkerLaneKind::MaterializeTasks as usize];
        eprintln!(
            "F5C_RESOURCE_PROBE\tcase=shared_summary_binary_dag_depth_{depth}\tunique_nodes={}\tstored_child_edges={}\tmaterialized_nodes={output_nodes}\tmaterialized_edges={output_edges}\tmaterialize_task_requests={}\tmaterialize_task_peak_bytes={}",
            memo.nodes.len(),
            memo.children.len(),
            tasks.requested_slots,
            tasks.peak_bytes,
        );
    }

    for depth in [64usize, 256, 1024, 4096] {
        let mut value = F5cPositive::Int;
        for _ in 0..depth {
            value = positive_function(&test_source_meter, F5cNegative::Top, value);
        }
        let mut memo = F5cComponentExpansionMemo::default();
        let empty = HashSet::new();
        let output = crate::f5c_replay::replay_positive(
            &test_source_meter,
            &mut memo,
            &value,
            &empty,
            &empty,
            &empty,
        )
        .unwrap();
        let tasks = memo.walker_resources.lanes[F5cWalkerLaneKind::ReplayTasks as usize];
        let values = memo.walker_resources.lanes[F5cWalkerLaneKind::ReplayValues as usize];
        eprintln!(
            "F5C_RESOURCE_PROBE\tcase=replay_function_chain_depth_{depth}\treplay_task_requests={}\treplay_value_requests={}\treplay_task_peak_bytes={}\treplay_value_peak_bytes={}",
            tasks.requested_slots, values.requested_slots, tasks.peak_bytes, values.peak_bytes,
        );
        assert_eq!(drain_positive_function_chain(value), depth);
        assert_eq!(drain_positive_function_chain(output), depth);
    }
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_source(family: F5cMatrixFamily, count: usize) -> String {
    use std::fmt::Write;
    let mut source = String::with_capacity(count.saturating_mul(32).saturating_add(32));
    match family {
        F5cMatrixFamily::IndependentIdentities => {
            for i in 0..count { write!(source, "my n{i} x = x; ").unwrap(); }
        }
        F5cMatrixFamily::IdentityAliases | F5cMatrixFamily::ArenaFactor => {
            source.push_str("my f x = x; ");
            for i in 0..count { write!(source, "my a{i} = f; ").unwrap(); }
        }
        _ => {
            for i in 0..count {
                write!(source, "my n{i} = n{}; ", (i + 1) % count).unwrap();
            }
        }
    }
    source
}

#[cfg(feature = "f5c_resource_probe")]
#[test]
fn f5c_walker_online_shadow_witness() {
    use crate::f5c_draft_heap::{DraftHeapMeter, FlatDraftOwner, PhysicalOwnerKind,
        RawWalkerOwner, TrackedVec, ComponentMemoEvents, InstantiationEvents,
        StructuredPairOwner, StructuredPairChildOwner, NormalizationOwner};
    use crate::f5c_draft::{FlatDraft, PositiveNode, NegativeNode, PositiveId, NegativeId,
        RecursiveBound, NodeRef};

    let sidecar = std::env::var_os("F5C_WALKER_SHADOW_SIDECAR")
        .map(std::path::PathBuf::from).unwrap_or_else(|| std::env::temp_dir().join(format!(
            "f5c-walker-shadow-{}.bin", std::process::id())));
    crate::f5c_draft_heap::open_f5c_resource_events(&sidecar).unwrap();
    let meter = DraftHeapMeter::default();
    {
        let source_kinds = [
            PhysicalOwnerKind::SourceOuter,
            PhysicalOwnerKind::SourceHeldBounds,
            PhysicalOwnerKind::SourceActiveBounds,
            PhysicalOwnerKind::PositiveFunctionArgument,
            PhysicalOwnerKind::PositiveFunctionResult,
            PhysicalOwnerKind::NegativeFunctionArgument,
            PhysicalOwnerKind::NegativeFunctionResult,
            PhysicalOwnerKind::UnionChildren,
            PhysicalOwnerKind::IntersectionChildren,
            PhysicalOwnerKind::StagedOuter,
            PhysicalOwnerKind::IndexedBuffer(0),
            PhysicalOwnerKind::IndexedBuffer(1),
            PhysicalOwnerKind::IndexedBuffer(2),
            PhysicalOwnerKind::IndexedBuffer(3),
            PhysicalOwnerKind::IndexedBuffer(4),
        ];
        let mut source: Vec<_> = source_kinds
            .into_iter()
            .map(|kind| TrackedVec::<u8>::new_with_kind(&meter, kind))
            .collect();
        for owner in &mut source {
            owner.try_reserve_exact(2).unwrap();
            owner.try_push(1).unwrap();
        }
        let before_failed_reserve = source[0].capacity();
        assert_eq!(
            source[0].reserve_with(16, |values, n| {
                values.try_reserve_exact(n).unwrap();
                Err(())
            }),
            Err(())
        );
        let failed_reserve_capacity = source[0].capacity();
        assert!(failed_reserve_capacity > before_failed_reserve);
        assert_eq!(source[0].accounted_bytes(), failed_reserve_capacity);
        let source_after_failure = crate::f5c_draft_heap::f5c_source_shadow_totals()[0];
        let combined_after_failure = crate::f5c_draft_heap::f5c_walker_shadow_totals().6;
        assert!(source_after_failure.current_capacity >= failed_reserve_capacity);
        assert!(combined_after_failure.current_capacity >= failed_reserve_capacity);
        source[0] = TrackedVec::<u8>::new_with_kind(&meter, PhysicalOwnerKind::SourceOuter);
        let source_after_release = crate::f5c_draft_heap::f5c_source_shadow_totals()[0];
        let combined_after_release = crate::f5c_draft_heap::f5c_walker_shadow_totals().6;
        assert_eq!(
            source_after_release.current_capacity,
            source_after_failure.current_capacity - failed_reserve_capacity
        );
        assert_eq!(
            combined_after_release.current_capacity,
            combined_after_failure.current_capacity - failed_reserve_capacity
        );
        assert_eq!(
            source_after_release.peak_capacity,
            source_after_failure.peak_capacity
        );
        assert_eq!(
            combined_after_release.peak_capacity,
            combined_after_failure.peak_capacity
        );
        let mut active_bounds =
            TrackedVec::<u8>::new_with_kind(&meter, PhysicalOwnerKind::SourceActiveBounds);
        active_bounds.try_reserve_exact(2).unwrap();
        active_bounds.try_push(1).unwrap();
        let (bounds_values, mut bounds_token) = active_bounds.into_raw_with_token();
        bounds_token.classify(PhysicalOwnerKind::SourceHeldBounds);
        drop(bounds_values);
        drop(bounds_token);
        let mut live = F5cLiveEventLedger::new([1; 10], 2, 2);
        for lane in 0..10 { live.top(lane, 1, 2); }
        for effect in [false, true] {
            for row in 0..2 {
                for lane in 0..4 { live.row(effect, row, lane, 1, 2); }
            }
        }
        live.top(0, 2, 2); // Request-only shape.
        live.row(false, 0, 0, 2, 4);
        live.truncate_rows(false, 1);
        live.truncate_rows(true, 1);
        assert!(live.capacity > 0);
        let mut comparison = RawWalkerOwner::new(&meter, 54 - 32, 2);
        let mut positive = RawWalkerOwner::new(&meter, 55 - 32, 4);
        let mut negative = RawWalkerOwner::new(&meter, 56 - 32, 8);
        let mut retained = RawWalkerOwner::new(&meter, 116 - 32, 16);
        let mut memo = ComponentMemoEvents::default();
        let mut instantiation = InstantiationEvents::default();
        let mut ordinary = FlatDraftOwner::new_with_component(0, 0, 1);
        comparison.observe(2, 4);
        for lane in 0..20 { memo.observe(lane, 1, 2, lane + 1); }
        for lane in 0..7 { instantiation.observe(lane, 1, 2, lane + 1); }
        instantiation.observe(0, 2, 4, 1);
        instantiation.observe(1, 2, 2, 2); // Request-only shape.
        memo.observe(0, 2, 4, 1);
        memo.observe(1, 0, 0, 2);
        memo.release(2);
        positive.observe(1, 2);
        negative.observe(1, 2);
        retained.observe(1, 2);
        ordinary.observe(2, 4);
        let (_, _, _, _, live_lanes, _, simultaneous) = crate::f5c_draft_heap::f5c_walker_shadow_totals();
        let source_capacity: usize = source.iter().map(TrackedVec::capacity).sum();
        assert_eq!((simultaneous.current_capacity, simultaneous.current_bytes),
            (68 + live.capacity + source_capacity, 538 + live.retained + source_capacity));
        assert!(live_lanes.iter().all(|lane| lane.current_capacity > 0));
        let mut pair_owners: Vec<_> = (0..21).filter(|lane| *lane != 1)
            .map(|lane| StructuredPairOwner::new(lane, lane + 1)).collect();
        for owner in &mut pair_owners { owner.observe(1, 2); }
        pair_owners[0].observe(2, 2); // Request-only top shape.
        pair_owners[0].observe(3, 4); // Grow the same top allocation.
        let mut first_child = StructuredPairChildOwner::new_with_shape(3, 1, 2);
        let mut second_child = StructuredPairChildOwner::new_with_shape(3, 1, 4);
        first_child.observe_shape(2, 2, 3);
        first_child.observe_growth(3, 4, 3);
        comparison.observe(3, 4); // Request-only update keeps the owner shape.
        negative.observe(0, 0);
        negative.observe(1, 4);
        comparison.observe(1, 2);
        let mut values = Vec::<u8>::with_capacity(4);
        values.extend([1, 2]);
        let mut transfer = RawWalkerOwner::new(&meter, 1, 1);
        transfer.observe(values.len(), values.capacity());
        let adopted = TrackedVec::try_adopt_raw_from_walker_with_owner(
            &meter,
            values,
            PhysicalOwnerKind::SourceSidecar,
            transfer,
        )
        .unwrap_or_else(|_| panic!("walker owner transfer failed"));
        drop(adopted);
        for kind in [
            PhysicalOwnerKind::UnionChildren,
            PhysicalOwnerKind::IntersectionChildren,
        ] {
            let mut values = Vec::<u8>::with_capacity(4);
            values.extend([1, 2]);
            let mut transfer = RawWalkerOwner::new(&meter, 1, 1);
            transfer.observe(values.len(), values.capacity());
            let adopted = TrackedVec::try_adopt_raw_from_walker_with_owner(
                &meter, values, kind, transfer)
                .unwrap_or_else(|_| panic!("walker child owner transfer failed"));
            drop(adopted);
        }
        // Each exercised normalization owner is tied to a live allocation.
        let mut normalization: Vec<_> = (0..28).map(|_| NormalizationOwner::default()).collect();
        let mut scratch: Vec<Vec<usize>> = (0..28).map(|_| Vec::new()).collect();
        for lane in 0..28 {
            if lane == 16 || (21..27).contains(&lane) { continue; }
            scratch[lane].reserve_exact(2);
            scratch[lane].push(lane);
            normalization[lane].observe(0, lane, scratch[lane].len(),
                scratch[lane].capacity(), std::mem::size_of_val(&scratch[lane][0]));
        }
        scratch[0].push(0);
        normalization[0].observe(0, 0, scratch[0].len(), scratch[0].capacity(),
            std::mem::size_of_val(&scratch[0][0]));
        scratch[0].reserve_exact(2);
        normalization[0].observe(0, 0, scratch[0].len(), scratch[0].capacity(),
            std::mem::size_of_val(&scratch[0][0]));
        let mut draft = FlatDraft::default();
        draft.attach_normalization_owners(meter.event_component());
        draft.positive_nodes.reserve_exact(2);
        draft.negative_nodes.reserve_exact(2);
        draft.positive_children.reserve_exact(2);
        draft.negative_children.reserve_exact(2);
        draft.recursive_bounds.reserve_exact(2);
        draft.insertion_order.reserve_exact(2);
        draft.sync_owners();
        draft.positive_nodes.push(PositiveNode::Int);
        draft.negative_nodes.push(NegativeNode::Int);
        draft.positive_children.push(PositiveId(0));
        draft.negative_children.push(NegativeId(0));
        draft.recursive_bounds.push(RecursiveBound {
            ordinal: 0, lower: PositiveId(0), upper: NegativeId(0),
        });
        draft.insertion_order.push(NodeRef::Positive(PositiveId(0)));
        draft.sync_owners();
        let normalization_lanes = crate::f5c_draft_heap::f5c_normalization_shadow_totals();
        assert_eq!(normalization_lanes[16].current_capacity, 0);
        assert!(normalization_lanes.iter().enumerate().all(|(lane, totals)|
            lane == 16 || totals.current_capacity > 0));
        let (norm_capacity, norm_bytes, _) = crate::f5c_draft_heap::normalization_event_totals();
        crate::f5c_draft_heap::checkpoint_normalization_events(norm_capacity, norm_bytes);
        let capacities = draft.capacities();
        let requested = [1; 6];
        let sizes = [std::mem::size_of::<PositiveNode>(),
            std::mem::size_of::<NegativeNode>(), std::mem::size_of::<PositiveId>(),
            std::mem::size_of::<NegativeId>(), std::mem::size_of::<RecursiveBound>(),
            std::mem::size_of::<NodeRef>()];
        let bytes = std::array::from_fn(|lane| capacities[lane] * sizes[lane]);
        let combined_before_transfer = crate::f5c_draft_heap::f5c_walker_shadow_totals().6;
        let staged = meter.claim_existing_batch_with_owners(bytes, 0,
            draft.owners.as_mut().unwrap(), requested, capacities, sizes)
            .expect("flat draft owner transfer failed");
        assert!(crate::f5c_draft_heap::f5c_normalization_shadow_totals()[21..27]
            .iter().all(|lane| lane.current_capacity == 0));
        let staged_lanes = crate::f5c_draft_heap::f5c_staged_shadow_totals();
        for lane in 0..6 {
            assert_eq!((staged_lanes[lane].current_capacity, staged_lanes[lane].current_bytes),
                (capacities[lane], bytes[lane]));
        }
        let combined_after_transfer = crate::f5c_draft_heap::f5c_walker_shadow_totals().6;
        assert_eq!((combined_after_transfer.current_capacity, combined_after_transfer.current_bytes,
            combined_after_transfer.peak_capacity, combined_after_transfer.peak_bytes),
            (combined_before_transfer.current_capacity, combined_before_transfer.current_bytes,
                combined_before_transfer.peak_capacity, combined_before_transfer.peak_bytes));
        drop(draft);
        drop(staged);
        assert!(crate::f5c_draft_heap::f5c_staged_shadow_totals().iter().all(|lane|
            lane.current_capacity == 0 && lane.current_bytes == 0 &&
            lane.peak_capacity > 0 && lane.peak_bytes > 0));
        drop(scratch);
        for owner in &mut normalization { owner.release(); }
        let lineage = crate::term::TermBuilder::new().unwrap().seal().unwrap();
        let mut terms = crate::term::BranchTermArena::new(lineage);
        terms.begin_route();
        terms.live_variable(crate::ComponentKind::Value, crate::Polarity::Positive, 1).unwrap();
        terms.commit_route();
        let term_lanes = terms.independent_owner_lanes().unwrap();
        assert!(term_lanes.capacities.iter().all(|capacity| *capacity > 0));
        let (term_capacity, term_bytes, _) = crate::f5c_draft_heap::term_event_totals();
        crate::f5c_draft_heap::checkpoint_term_events(term_capacity, term_bytes);
        terms.transfer_owner_events_to_solved_store();
        drop(terms);
        crate::f5c_draft_heap::checkpoint_live_variable_events(live.capacity, live.retained);
        live.release_all();
        let (pair_capacity, pair_bytes, _) = crate::f5c_draft_heap::structured_pair_event_totals();
        crate::f5c_draft_heap::checkpoint_structured_pair_events(pair_capacity, pair_bytes);
        first_child.release(3);
        second_child.release(3);
        for (index, owner) in pair_owners.iter_mut().enumerate() {
            if index != 18 { owner.release(); }
        }
        pair_owners[18].transfer_same_id();
        pair_owners[18].release();
        drop(memo);
        drop(instantiation);
        drop(ordinary);
        drop(source);
        drop(comparison);
        drop(positive);
        drop(negative);
        let (lanes, component_lanes, term_lanes, instantiation_lanes, live_lanes, pair_lanes, combined) = crate::f5c_draft_heap::f5c_walker_shadow_totals();
        assert_eq!((lanes[116 - 32].current_capacity, combined.current_bytes), (2, 32));
        assert!(component_lanes.iter().all(|lane| lane.current_capacity == 0));
        assert!(term_lanes.iter().all(|lane| lane.current_capacity == 0));
        assert!(instantiation_lanes.iter().all(|lane| lane.current_capacity == 0));
        assert!(live_lanes.iter().all(|lane| lane.current_capacity == 0));
        assert!(pair_lanes.iter().all(|lane| lane.current_capacity == 0));
        drop(retained);
    }
    let (lanes, component_lanes, term_lanes, instantiation_lanes, live_lanes, pair_lanes, combined) = crate::f5c_draft_heap::f5c_walker_shadow_totals();
    assert_eq!((combined.current_capacity, combined.current_bytes), (0, 0));
    assert!(combined.peak_bytes >= 480);
    assert!(component_lanes.iter().all(|lane| lane.peak_capacity > 0));
    assert!(term_lanes.iter().all(|lane| lane.peak_capacity > 0));
    assert!(instantiation_lanes.iter().all(|lane| lane.peak_capacity > 0));
    assert!(live_lanes.iter().all(|lane| lane.peak_capacity > 0));
    assert!(pair_lanes.iter().all(|lane| lane.peak_capacity > 0));
    let normalization_lanes = crate::f5c_draft_heap::f5c_normalization_shadow_totals();
    let source_lanes = crate::f5c_draft_heap::f5c_source_shadow_totals();
    assert!(source_lanes.iter().all(|lane| lane.current_capacity == 0
        && lane.current_bytes == 0
        && lane.peak_capacity > 0
        && lane.peak_bytes > 0));
    assert!(normalization_lanes.iter().enumerate().all(|(lane, totals)|
        (lane == 16 && *totals == Default::default()) ||
        (lane != 16 && totals.current_capacity == 0 && totals.peak_capacity > 0)));
    let (count, checksum) = crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
    let sidecar_bytes = std::fs::read(&sidecar).unwrap();
    assert_eq!(sidecar_bytes.len(), 8 + usize::try_from(count).unwrap() * 64);
    if std::env::var_os("F5C_FULL_WALKER_EVENTS").is_none() {
        let mut excluded_intervals = 0;
        let mut excluded_lanes = 0;
        for event in sidecar_bytes[8..].chunks_exact(64) {
            let word = |index: usize| u64::from_le_bytes(event[index * 8..][..8].try_into().unwrap());
            assert!(word(2) > 7 || !matches!(word(3), 54..=56 | 116),
                "excluded WalkerLane identity was serialized");
            excluded_intervals += usize::from(word(2) == 10);
            excluded_lanes += usize::from(word(2) == 11);
        }
        assert!(excluded_intervals > 0);
        assert_eq!(excluded_lanes, 4);
    }
    if let Some(path) = std::env::var_os("F5C_WALKER_SHADOW_TOTALS") {
        use std::fmt::Write;
        let mut output = format!("{count} {checksum}\n");
        for (lane, totals) in lanes.iter().enumerate() {
            writeln!(
                output,
                "{} {} {} {} {}",
                lane + 150,
                totals.current_capacity,
                totals.peak_capacity,
                totals.current_bytes,
                totals.peak_bytes
            )
            .unwrap();
        }
        for (lane, totals) in component_lanes.iter().enumerate() {
            writeln!(output, "{} {} {} {} {}", lane + 551, totals.current_capacity,
                totals.peak_capacity, totals.current_bytes, totals.peak_bytes).unwrap();
        }
        for (lane, totals) in term_lanes.iter().enumerate() {
            writeln!(output, "{} {} {} {} {}", lane + 571, totals.current_capacity,
                totals.peak_capacity, totals.current_bytes, totals.peak_bytes).unwrap();
        }
        for (lane, totals) in instantiation_lanes.iter().enumerate() {
            writeln!(output, "{} {} {} {} {}", lane + 577, totals.current_capacity,
                totals.peak_capacity, totals.current_bytes, totals.peak_bytes).unwrap();
        }
        for (lane, totals) in live_lanes.iter().enumerate() {
            writeln!(output, "{} {} {} {} {}", lane + 512, totals.current_capacity,
                totals.peak_capacity, totals.current_bytes, totals.peak_bytes).unwrap();
        }
        for (lane, totals) in pair_lanes.iter().enumerate() {
            writeln!(output, "{} {} {} {} {}", lane + 530, totals.current_capacity,
                totals.peak_capacity, totals.current_bytes, totals.peak_bytes).unwrap();
        }
        for (lane, totals) in normalization_lanes.iter().enumerate() {
            writeln!(output, "{} {} {} {} {}", lane + 584, totals.current_capacity,
                totals.peak_capacity, totals.current_bytes, totals.peak_bytes).unwrap();
        }
        for (lane, totals) in crate::f5c_draft_heap::f5c_staged_shadow_totals().iter().enumerate() {
            writeln!(output, "{} {} {} {} {}", lane + 12, totals.current_capacity,
                totals.peak_capacity, totals.current_bytes, totals.peak_bytes).unwrap();
        }
        for (lane, totals) in source_lanes.iter().enumerate() {
            let row = if lane < 10 { 129 + lane } else { 145 + lane - 10 };
            writeln!(
                output,
                "{} {} {} {} {}",
                row,
                totals.current_capacity,
                totals.peak_capacity,
                totals.current_bytes,
                totals.peak_bytes
            )
            .unwrap();
        }
        writeln!(output, "combined {} {} {} {}", combined.current_capacity,
            combined.peak_capacity, combined.current_bytes, combined.peak_bytes).unwrap();
        std::fs::write(path, output).unwrap();
    } else {
        std::fs::remove_file(sidecar).unwrap();
    }
}

#[cfg(feature = "f5c_resource_probe")]
#[test]
fn f5c_joint_session_replay_witness() {
    let sidecar = std::env::var_os("F5C_JOINT_SESSION_SIDECAR")
        .map(std::path::PathBuf::from).unwrap_or_else(|| std::env::temp_dir().join(format!(
            "f5c-joint-session-{}.bin", std::process::id())));
    crate::f5c_draft_heap::open_f5c_resource_events(&sidecar).unwrap();
    let batch = collect(module(
        "my left = right; my right = left; my consumer = left",
        "f5c-joint-session",
    ));
    let mut session = InferenceSession::new(batch);
    session.flat_candidate_enabled = true;
    session.sample_f4_resources(ResourceBoundary::InitialReservation).unwrap();
    session.admit_all_collected_facts().unwrap();
    session.execute_scc_plan().unwrap();
    assert!(session.resource_ledger.flat_finalizer_calls >= 2);
    // Exercise the existing member sample with a live non-owner draft lane rebase.
    let draft_capacity = session.drafts.capacity();
    session.drafts.reserve_exact(draft_capacity + 8);
    assert!(session.drafts.capacity() > draft_capacity);
    session.sample_f4_resources(ResourceBoundary::DraftMember).unwrap();
    session.sample_f4_resources(ResourceBoundary::IncomingRoute).unwrap();
    let route_capacity = session.routed_uses.capacity();
    session.routed_uses.reserve_exact(route_capacity + 8);
    assert!(session.routed_uses.capacity() > route_capacity);
    session.sample_f4_resources(ResourceBoundary::IncomingRoute).unwrap();
    let route_before = session.resource_ledger.route_use_lanes[0].retained_bytes
        + session.resource_ledger.route_use_lanes[1].retained_bytes;
    assert!(route_before > 0);
    session.routed_uses.clear();
    session.routed_uses.shrink_to_fit();
    session.routed_use_positions.clear();
    session.routed_use_positions.shrink_to_fit();
    session.sample_f4_resources(ResourceBoundary::IncomingRoute).unwrap();
    assert_eq!(session.resource_ledger.route_use_lanes[0].retained_bytes
        + session.resource_ledger.route_use_lanes[1].retained_bytes, 0);
    let (current, peak, samples, calls, adjustments) =
        crate::f5c_draft_heap::f5c_session_totals();
    assert!(samples > calls && calls >= 2);
    assert!(adjustments > samples);
    assert!(peak >= current);
    let (count, checksum) = crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
    if let Some(path) = std::env::var_os("F5C_JOINT_SESSION_TOTALS") {
        std::fs::write(path, format!("{count} {checksum} {current} {peak} {samples} {calls} {adjustments}\n"))
            .unwrap();
    } else {
        std::fs::remove_file(sidecar).unwrap();
    }
}

#[cfg(feature = "f5c_resource_probe")]
#[test]
fn f5c_live_variable_events_release_after_returned_error() {
    F5C_LEDGER_AFTER_STAGE_HIT.with(|hit| hit.set(false));
    let mut session = matrix_session_before_admission(
        "my left = right; my right = left", "live-returned-error");
    session.flat_candidate_precommit_failure =
        Some(FlatCandidatePrecommitFailure::LedgerAfterStage);
    assert!(matches!(session.run(), Err(SolveAvailabilityError::IdentityExhausted)));
    assert!(F5C_LEDGER_AFTER_STAGE_HIT.with(|hit| hit.get()),
        "returned error must reach LedgerAfterStage injection");
    let path = F5C_MATRIX_SIDECAR.with(|path| path.borrow_mut().take()).unwrap();
    let (count, _) = crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
    let bytes = std::fs::read(&path).unwrap();
    std::fs::remove_file(path).unwrap();
    let events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
        std::array::from_fn(|index| u64::from_le_bytes(
            event[index * 8..(index + 1) * 8].try_into().unwrap()))
    }).collect();
    assert_eq!(count as usize, events.len());
    let created: Vec<_> = events.iter().filter(|event| event[2] == 1 && (512..530).contains(&event[3]))
        .map(|event| event[1]).collect();
    assert!(events.iter().any(|event| (512..522).contains(&event[3])
        && event[5] > 0), "fixture needs positive top-level family-1 capacity");
    for id in created {
        assert_eq!(events.iter().filter(|event| event[1] == id && event[2] == 5).count(), 1);
    }
    assert!(events.iter().any(|event| (522..530).contains(&event[3])
        && event[5] > 0), "fixture needs positive nested family-1 capacity");
    let mut live = std::collections::HashMap::new();
    for event in &events {
        if !(512..530).contains(&event[3]) { continue; }
        match event[2] {
            1 => { assert!(live.insert(event[1], (event[5], event[5] * event[6])).is_none()); }
            2 | 3 | 4 => { assert!(live.insert(event[1], (event[5], event[5] * event[6])).is_some()); }
            5 => { assert!(live.remove(&event[1]).is_some()); }
            _ => {}
        }
    }
    assert!(live.is_empty(), "returned error must leave zero family-1 live capacity and bytes");
}

#[cfg(feature = "f5c_resource_probe")]
#[test]
fn f5c_live_variable_events_keep_row_identity_and_same_time_peak() {
    let path = std::env::temp_dir().join(format!(
        "f5c-live-events-{}-{:?}.bin", std::process::id(), std::thread::current().id()));
    crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
    let mut live = F5cLiveEventLedger::new([4; 10], 1, 0);
    live.top(0, 1, 4);
    live.row(false, 0, 0, 1, 4);
    let first_peak = live.peak;
    live.row(false, 0, 0, 2, 8);
    assert_eq!(live.peak, live.retained);
    live.row(false, 0, 0, 1, 8);
    live.add_row(false);
    live.row(false, 1, 0, 1, 4);
    assert!(live.peak > first_peak);
    live.truncate_rows(false, 1);
    assert!(live.peak > live.retained);
    crate::f5c_draft_heap::checkpoint_live_variable_events(live.capacity, live.retained);
    live.release_all();
    let (count, _) = crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
    let bytes = std::fs::read(&path).unwrap();
    std::fs::remove_file(path).unwrap();
    let events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
        std::array::from_fn(|index| u64::from_le_bytes(
            event[index * 8..(index + 1) * 8].try_into().unwrap()))
    }).collect();
    assert_eq!(count as usize, events.len());
    let row_ids: Vec<_> = events.iter().filter(|event| event[2] == 1 && event[3] == 522)
        .map(|event| event[1]).collect();
    assert_eq!(row_ids.len(), 2);
    assert_ne!(row_ids[0], row_ids[1]);
    assert!(events.iter().any(|event| event[1] == row_ids[0]
        && event[2] == 3 && event[5] == 8));
    assert!(events.iter().any(|event| event[1] == row_ids[0]
        && event[2] == 5 && event[4] == 0 && event[5] == 0));
    assert!(events.iter().any(|event| event[1] == 0 && event[2] == 6
        && event[3] == 512 && event[5] > 0));
}

#[cfg(feature = "f5c_resource_probe")]
#[test]
fn f5c_live_variable_events_reconcile_terminal_session() {
    let mut session = matrix_session("my f x = x;", "live-terminal");
    session.execute_scc_plan().unwrap();
    matrix_assert_output(&session);
    let solved = session.finish().unwrap();
    let observer = solved.f5c_matrix_observer.as_ref().unwrap();
    assert_eq!(observer.family1_event_terminal,
        (usize::try_from(observer.family_capacity[0]).expect("family-1 capacity"),
            observer.family_retained[0], observer.family_peak[0]));
    assert_eq!(observer.live_events.as_ref().unwrap().capacity, 0);
    let sidecar = F5C_MATRIX_SIDECAR.with(|path| path.borrow_mut().take()).unwrap();
    crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
    std::fs::remove_file(sidecar).unwrap();
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_session(source: &str, name: &str) -> InferenceSession {
    let mut session = matrix_session_before_admission(source, name);
    session.admit_all_collected_facts().unwrap();
    session
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_session_before_admission(source: &str, name: &str) -> InferenceSession {
    let hir = module(source, name);
    assert!(hir.diagnostics().is_empty(), "matrix HIR diagnostics");
    let batch = collect(hir);
    let mut session = InferenceSession::new(batch);
    let sidecar = std::env::var_os("F5C_RESOURCE_SIDECAR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::env::temp_dir().join(format!(
            "f5c-resource-{}-{}.bin", std::process::id(), name)));
    crate::f5c_draft_heap::open_f5c_resource_events(&sidecar)
        .expect("open F5c resource event sidecar before solve");
    session.store.terms.start_owner_events();
    F5C_MATRIX_SIDECAR.with(|path| *path.borrow_mut() = Some(sidecar));
    session.flat_candidate_enabled = true;
    session.f5c_matrix_observer = Some(F5cMatrixObserver::new());
    session.seed_f5c_matrix_live_events();
    session.start_f5c_matrix_route_growth();
    session
}

#[cfg(feature = "f5c_resource_probe")]
thread_local! {
    static F5C_MATRIX_SIDECAR: std::cell::RefCell<Option<std::path::PathBuf>> = const {
        std::cell::RefCell::new(None)
    };
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_assert_output(session: &InferenceSession) {
    assert!(session.errors.is_empty(), "matrix solver diagnostics");
    assert!(session.schemes.iter().all(Option::is_some), "all schemes installed");
    assert!(session.f5c_candidate_capture.is_none());
    assert!(session.resource_ledger.boundary_order.is_empty());
    assert_eq!(session.resource_ledger.semantic_arena_retained_bytes,
        session.execution_counters.semantic_arena_retained_bytes);
    assert_eq!(session.resource_ledger.inference_session_retained_bytes,
        session.execution_counters.inference_session_retained_bytes);
    let observer = session.f5c_matrix_observer.as_ref().unwrap();
    assert_eq!(observer.boundaries.len(), F5C_MATRIX_BOUNDARIES);
    assert!(observer.lane_count > 0);
    assert_eq!(observer.family_ends[7] + 6, observer.lane_count);
    assert!(observer.family_ends.windows(2).all(|pair| pair[0] < pair[1]));
    assert!(observer.boundaries.iter().any(|boundary| boundary.seen > 0));
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_lane_identity(index: usize) -> String {
    const FRONT: [&str; 45] = [
        "live_components", "value_bounds", "effect_bounds", "value_levels",
        "effect_levels", "value_metadata", "effect_metadata", "extrusion_stack",
        "extrusion_value_marks", "extrusion_effect_marks", "value_direct_lower",
        "value_direct_upper", "value_exact_lower", "value_exact_upper",
        "effect_direct_lower", "effect_direct_upper", "effect_exact_lower",
        "effect_exact_upper", "term_0", "term_1", "term_2", "term_3", "term_4",
        "term_5", "typed_pairs", "diagnostic_edges", "typed_worklist",
        "diagnostic_delta", "diagnostic_delta_indices", "diagnostic_reverse_offsets",
        "diagnostic_reverse_edges", "diagnostic_reverse_cursors", "diagnostic_dfs_stack",
        "diagnostic_finish_order", "diagnostic_scc_indices", "diagnostic_scc_nodes",
        "diagnostic_scc_offsets", "diagnostic_scc_pending_children",
        "diagnostic_scc_worklist", "diagnostic_bucket_heads", "diagnostic_bucket_tails",
        "diagnostic_bucket_candidates", "diagnostic_node_witnesses", "errors",
        "reported_errors",
    ];
    let lane = match index {
        0..45 => FRONT[index].to_owned(),
        45..65 => format!("component_memo_{}", index - 45),
        65..73 => format!("closed_arena_{}", index - 65),
        73..90 => format!("closed_scratch_{}", index - 73),
        90..101 => format!("closed_indexed_{}", index - 90),
        101..129 => format!("normalization_{}", index - 101),
        129 => "aggregate_source_draft_slots".to_owned(),
        130 => "aggregate_source_bound_tokens".to_owned(),
        131 => "aggregate_source_recursive_bounds".to_owned(),
        132..138 => format!("source_nested_payload_{}", index - 132),
        138 => "staged_outer".to_owned(),
        139..145 => format!("staged_buffer_{}", index - 139),
        145..150 => format!("indexed_buffer_{}", index - 145),
        150..248 => format!("generalization_walker_{}", index - 150),
        248..255 => format!("instantiation_{}", index - 248),
        255..259 => format!("route_store_{}", index - 255),
        259..261 => format!("routed_use_{}", index - 259),
        _ => panic!("unexpected F5c matrix lane index {index}"),
    };
    let family = match index {
        0..18 => "live_variable_tables",
        18..24 => "inference_type_arena",
        24..45 => "structured_pair_memo",
        45..65 => "component_expansion_memo",
        65..101 => "closed_type_arena",
        101..129 => "closed_normalization_index",
        129..248 => "generalization_scratch",
        248..255 => "instantiation_substitution",
        _ => "outside_family",
    };
    format!("{family}/{lane}")
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_emit(session: &SolvedModule, case: F5cMatrixCase) {
    if !case.emit {
        let (event_count, event_checksum) = crate::f5c_draft_heap::close_f5c_resource_events()
            .expect("flush F5c resource event sidecar");
        let sidecar = F5C_MATRIX_SIDECAR.with(|path| path.borrow_mut().take())
            .expect("F5c resource sidecar path");
        let sidecar_bytes = std::fs::metadata(&sidecar)
            .expect("preflight event sidecar metadata").len();
        let expected_bytes = event_count.checked_mul(64)
            .and_then(|bytes| bytes.checked_add(8))
            .expect("preflight event sidecar length arithmetic");
        assert_eq!(sidecar_bytes, expected_bytes,
            "preflight event sidecar length must match event count");
        eprintln!("F5C_RESOURCE_PREFLIGHT_EVENT\tfamily={:?}\tdimension={}\tsize={}\tcompanion={}\tcount={}\tchecksum={}\tbytes={}",
            case.family, case.dimension, case.size,
            case.companion.map_or_else(|| "none".to_owned(), |n| n.to_string()),
            event_count, event_checksum, sidecar_bytes);
        std::fs::remove_file(sidecar).expect("remove preflight event sidecar");
        return;
    }
    let observer = session.f5c_matrix_observer.as_ref().unwrap();
    // One record per process; the offline checker consumes this after the solve.
    let companion = case.companion.map_or_else(|| "none".to_owned(), |n| n.to_string());
    let lanes = observer.current[..observer.lane_count].iter().enumerate()
        .map(|(index, lane)| format!("{}:{},{},{},{},{},{}", matrix_lane_identity(index), lane.actual_capacity,
            lane.peak_capacity, lane.retained_bytes, lane.observed_retained_bytes,
            lane.peak_bytes, lane.slot_size))
        .collect::<Vec<_>>().join(";");
    let family_totals = observer.family_capacity.iter()
        .zip(observer.family_retained.iter().zip(observer.family_peak.iter()))
        .map(|(capacity, (retained, peak))| format!("{capacity},{retained},{peak}"))
        .collect::<Vec<_>>().join(";");
    let family5_growths = observer.current[101..129].iter()
        .map(|lane| lane.growths.to_string()).collect::<Vec<_>>().join(",");
    let (event_count, event_checksum) =
        crate::f5c_draft_heap::close_f5c_resource_events()
            .expect("flush F5c resource event sidecar");
    let sidecar = F5C_MATRIX_SIDECAR.with(|path| path.borrow_mut().take())
        .expect("F5c resource sidecar path");
    eprintln!("F5C_RESOURCE_MATRIX_ROW\tfamily={:?}\tdimension={}\tsize={}\tcompanion={}\tfamily_ends={:?}\tfamily_totals={}\tfamily1_event={},{},{}\tfamily2_event={},{},{}\tfamily3_event={},{},{}\tfamily4_event={},{},{}\tclosed_type_event={},{},{}\tclosed_type_checkpoint_peak={}\tfamily5_event={},{},{}\tfamily5_growths={}\tfamily8_event={},{},{}\tfamily6_event={},{},{},{},{},{}\tsemantic_retained={}\tsemantic_peak={}\tsession_retained={}\tsession_peak={}\tlanes={}",
        case.family, case.dimension, case.size, companion, observer.family_ends,
        family_totals, observer.family1_event_terminal.0,
        observer.family1_event_terminal.1, observer.family1_event_terminal.2,
        observer.family2_event_terminal.0, observer.family2_event_terminal.1,
        observer.family2_event_terminal.2,
        observer.family3_event_terminal.0, observer.family3_event_terminal.1,
        observer.family3_event_terminal.2,
        observer.family4_event_terminal.0, observer.family4_event_terminal.1,
        observer.family4_event_terminal.2,
        observer.closed_type_event_terminal.0, observer.closed_type_event_terminal.1,
        observer.closed_type_event_terminal.2,
        session.resource_ledger.flat_finalizer_peak_bytes,
        observer.family5_event_terminal.0, observer.family5_event_terminal.1,
        observer.family5_event_terminal.2,
        family5_growths,
        observer.family8_event_terminal.0, observer.family8_event_terminal.1,
        observer.family8_event_terminal.2,
        observer.family6_event_capacity, observer.family6_event_retained,
        observer.family6_event_peak, observer.family6_event_count,
        event_count, event_checksum,
        session.resource_ledger.semantic_arena_retained_bytes,
        session.resource_ledger.semantic_arena_peak_bytes,
        session.resource_ledger.inference_session_retained_bytes,
        session.resource_ledger.inference_session_peak_bytes, lanes);
    eprintln!("F5C_RESOURCE_MATRIX_SIDECAR\tpath={}", sidecar.display());
    eprintln!(
        "F5C_RESOURCE_MATRIX\tfamily={:?}\tdimension={}\tsize={}\tcompanion={:?}\tlanes={}\tfamily_ends={:?}\tsemantic_retained={}\tsemantic_peak={}\tsession_retained={}\tsession_peak={}",
        case.family, case.dimension, case.size, case.companion, observer.lane_count,
        observer.family_ends,
        session.resource_ledger.semantic_arena_retained_bytes,
        session.resource_ledger.semantic_arena_peak_bytes,
        session.resource_ledger.inference_session_retained_bytes,
        session.resource_ledger.inference_session_peak_bytes,
    );
    for (index, boundary) in observer.boundaries.iter().enumerate() {
        if boundary.seen == 0 { continue; }
        eprintln!(
            "F5C_RESOURCE_MATRIX_BOUNDARY\tfamily={:?}\tdimension={}\tsize={}\tboundary={}\tseen={}\tsemantic_retained={}\tsemantic_peak={}\tsession_retained={}\tsession_peak={}\tlanes={:?}",
            case.family, case.dimension, case.size, index, boundary.seen,
            boundary.semantic_retained, boundary.semantic_peak,
            boundary.session_retained, boundary.session_peak,
            &boundary.lanes[..observer.lane_count],
        );
    }
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_finish_and_emit(mut session: InferenceSession, case: F5cMatrixCase) {
    matrix_assert_output(&session);
    session.sample_f4_resources(ResourceBoundary::StoreAccounting).unwrap();
    session.store.finish_accounting();
    session.sample_f4_resources(ResourceBoundary::StoreAccounting).unwrap();
    let solved = session.finish().expect("matrix final output");
    assert!(solved.errors.is_empty());
    let observer = solved.f5c_matrix_observer.as_ref().unwrap();
    assert!(observer.boundaries[ResourceBoundary::FinishOutputWithStaging as usize].seen > 0);
    assert!(observer.boundaries[ResourceBoundary::FinishOutput as usize].seen > 0);
    assert_eq!(solved.resource_ledger.instantiation_substitution_retained_bytes, 0);
    matrix_emit(&solved, case);
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_identity(case: F5cMatrixCase) {
    let (d, _) = case.parameters();
    let source = matrix_source(case.family, d);
    let mut session = matrix_session(&source, "f5c-resource-matrix-identity");
    assert_eq!(session.batch.definitions.len(), d);
    assert_eq!(session.batch.counters.emitted_facts, 5 * d);
    assert!(session.batch.definition_uses.is_empty());
    assert_eq!(session.bounds.len(), 2 * d, "constructed value rows");
    assert_eq!(session.effect_bounds.len(), 2 * d, "constructed effect rows");
    assert_eq!(session.store.facts().len(), 5 * d, "admitted source facts");
    session.execute_scc_plan().unwrap();
    assert_eq!(session.execution_counters.generalization_quantifier_writes, d);
    assert_eq!(session.execution_counters.generalization_recursive_binder_writes, 0);
    assert_eq!(session.execution_counters.generalization_shared_summary_hits, 0);
    matrix_finish_and_emit(session, case);
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_aliases(case: F5cMatrixCase) {
    let (u, _) = case.parameters();
    let source = matrix_source(case.family, u);
    let mut session = matrix_session(&source, "f5c-resource-matrix-aliases");
    assert_eq!(session.batch.definitions.len(), u + 1);
    assert_eq!(session.batch.definition_uses.len(), u);
    session.execute_scc_plan().unwrap();
    assert_eq!(session.execution_counters.scc_execution_incoming_instantiations, u);
    assert_eq!(session.execution_counters.instantiation_fresh_value_variables, u);
    assert_eq!(session.execution_counters.instantiation_fresh_effect_variables, 0);
    assert_eq!(session.execution_counters.instantiation_node_visits, 5 * u);
    matrix_finish_and_emit(session, case);
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_seed_value_bound(session: &mut InferenceSession, row: u32,
    value: ValueEndpointKey, lower: bool) {
    let (slot, accounting, lane_index) = if lower {
        (&mut session.bounds[row as usize].exact_non_variable_lowers,
            &mut session.independent_nested_capacities.value_exact_lower, 2)
    } else {
        (&mut session.bounds[row as usize].exact_non_variable_uppers,
            &mut session.independent_nested_capacities.value_exact_upper, 3)
    };
    let old_capacity = slot.capacity();
    slot.try_reserve_exact(1).expect("matrix bound reservation");
    session.f5c_matrix_observer.as_mut().unwrap()
        .nested_request(lane_index, old_capacity, slot.capacity());
    session.f5c_matrix_observer.as_mut().unwrap().live_events.as_mut().unwrap()
        .row(false, row as usize, lane_index, slot.len(), slot.capacity());
    InferenceSession::record_bound_capacity_growth(
        &mut session.bound_payload_bytes, accounting, &mut session.execution_counters,
        &mut session.route_journal, row as usize, false, old_capacity, slot.capacity(),
        std::mem::size_of::<ValueEndpointKey>(),
    ).unwrap();
    slot.push(value);
    session.f5c_matrix_observer.as_mut().unwrap().nested_insert(lane_index);
    session.f5c_matrix_observer.as_mut().unwrap().live_events.as_mut().unwrap()
        .row(false, row as usize, lane_index, slot.len(), slot.capacity());
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_seed_value_edge(session: &mut InferenceSession, row: u32, next: u32, lower: bool) {
    let (slot, accounting, lane_index) = if lower {
        (&mut session.bounds[row as usize].direct_lower_rows,
            &mut session.independent_nested_capacities.value_direct_lower, 0)
    } else {
        (&mut session.bounds[row as usize].direct_upper_rows,
            &mut session.independent_nested_capacities.value_direct_upper, 1)
    };
    let old_capacity = slot.capacity();
    slot.try_reserve_exact(1).expect("matrix edge reservation");
    session.f5c_matrix_observer.as_mut().unwrap()
        .nested_request(lane_index, old_capacity, slot.capacity());
    session.f5c_matrix_observer.as_mut().unwrap().live_events.as_mut().unwrap()
        .row(false, row as usize, lane_index, slot.len(), slot.capacity());
    InferenceSession::record_bound_capacity_growth(
        &mut session.bound_payload_bytes, accounting, &mut session.execution_counters,
        &mut session.route_journal, row as usize, false, old_capacity, slot.capacity(),
        std::mem::size_of::<u32>(),
    ).unwrap();
    slot.push(next);
    session.f5c_matrix_observer.as_mut().unwrap().nested_insert(lane_index);
    session.f5c_matrix_observer.as_mut().unwrap().live_events.as_mut().unwrap()
        .row(false, row as usize, lane_index, slot.len(), slot.capacity());
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_graph_session(d: usize, name: &str) -> (InferenceSession, Vec<u32>) {
    let source = matrix_source(F5cMatrixFamily::SharedAcyclic, d);
    let mut session = matrix_session(&source, name);
    assert_eq!(session.batch.definitions.len(), d);
    assert_eq!(session.batch.definition_uses.len(), d);
    assert_eq!(session.batch.scc_components_in_dependency_first_order().count(), 1);
    let mut roots = Vec::with_capacity(d);
    for index in 0..d {
        let root = session.batch.definitions[index].root.clone();
        let position = session.batch.root_component_positions[&root].component;
        let row = session.fresh_value_at_level(1).unwrap();
        session.live_components[position].ordinal = row;
        roots.push(row);
    }
    (session, roots)
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_acyclic(case: F5cMatrixCase) {
    let (d, k) = case.parameters();
    let shared = case.family == F5cMatrixFamily::SharedAcyclic;
    let (mut session, roots) = matrix_graph_session(d, "f5c-resource-matrix-acyclic");
    let cones = if shared { 1 } else { d };
    let mut rows = Vec::with_capacity(k);
    let mut bound_edges = 0usize;
    let terms_before = session.store.terms.capacity_snapshot().1.lengths[3];
    for cone in 0..cones {
        rows.clear();
        for _ in 0..k { rows.push(session.fresh_value_at_level(1).unwrap()); }
        matrix_seed_value_bound(&mut session, rows[k - 1], ValueEndpointKey::IntPositive, true);
        matrix_seed_value_bound(&mut session, rows[k - 1], ValueEndpointKey::IntNegative, false);
        bound_edges += 2;
        for i in 0..k - 1 {
            matrix_seed_value_edge(&mut session, rows[i], rows[i + 1], true);
            matrix_seed_value_edge(&mut session, rows[i], rows[i + 1], false);
            bound_edges += 2;
        }
        let argument = session.live_value_term(Polarity::Negative, rows[0]).unwrap();
        let result = session.live_value_term(Polarity::Positive, rows[0]).unwrap();
        let function = session.positive_function_term(argument,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session.batch.collected_leaf_term(Leaf::EffectBottomPositive), result).unwrap();
        for root in if shared { 0..d } else { cone..cone + 1 } {
            matrix_seed_value_bound(&mut session, roots[root],
                ValueEndpointKey::PositiveFunction(function), true);
            bound_edges += 1;
        }
    }
    assert_eq!(bound_edges, 2 * k * cones + d);
    assert_eq!(roots.len(), d, "constructed root frontier");
    let terms_after = session.store.terms.capacity_snapshot().1.lengths[3];
    assert_eq!(terms_after - terms_before, 3 * cones, "constructed terms");
    session.sample_f4_resources(ResourceBoundary::InitialAdmission).unwrap();
    session.execute_scc_plan().unwrap();
    let states = 2 * k * cones;
    assert_eq!(session.resource_ledger.component_expansion_memo_roots.requested_slots, states);
    assert_eq!(session.execution_counters.generalization_shared_summary_admissions, states);
    assert_eq!(session.execution_counters.generalization_shared_summary_hits,
        if shared { 2 * k * (d - 1) } else { 0 });
    if shared { assert_eq!(session.execution_counters.generalization_uncacheable_states, 0); }
    matrix_finish_and_emit(session, case);
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_guarded_cycle(case: F5cMatrixCase) {
    let (d, k) = case.parameters();
    assert!(d <= k, "each root enters a distinct cycle rotation");
    let (mut session, roots) = matrix_graph_session(d, "f5c-resource-matrix-cycle");
    let mut cycle = Vec::with_capacity(k);
    for _ in 0..k { cycle.push(session.fresh_value_at_level(1).unwrap()); }
    let terms_before = session.store.terms.capacity_snapshot().1.lengths[3];
    for index in 0..k {
        let next = cycle[(index + 1) % k];
        let negative = session.live_value_term(Polarity::Negative, next).unwrap();
        let positive = session.live_value_term(Polarity::Positive, next).unwrap();
        let lower = session.positive_function_term(negative,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session.batch.collected_leaf_term(Leaf::EffectBottomPositive), positive).unwrap();
        let upper = session.negative_function_term(positive,
            session.batch.collected_leaf_term(Leaf::EffectBottomPositive),
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative), negative).unwrap();
        matrix_seed_value_bound(&mut session, cycle[index],
            ValueEndpointKey::PositiveFunction(lower), true);
        matrix_seed_value_bound(&mut session, cycle[index],
            ValueEndpointKey::NegativeFunction(upper), false);
    }
    for (index, root) in roots.iter().copied().enumerate() {
        let rotation = cycle[index];
        matrix_seed_value_bound(&mut session, root, ValueEndpointKey::ValueRow(rotation), true);
        matrix_seed_value_bound(&mut session, root, ValueEndpointKey::ValueRow(rotation), false);
    }
    assert_eq!(cycle.len(), k);
    assert_eq!(roots.len(), d);
    let terms_after = session.store.terms.capacity_snapshot().1.lengths[3];
    assert_eq!(terms_after - terms_before, 4 * k, "constructed cycle terms");
    session.sample_f4_resources(ResourceBoundary::InitialAdmission).unwrap();
    session.execute_scc_plan().unwrap();
    assert_eq!(session.execution_counters.generalization_recursive_binder_writes, d);
    assert_eq!(session.execution_counters.generalization_shared_summary_admissions, 0);
    assert_eq!(session.execution_counters.generalization_uncacheable_states, 2 * d * k);
    matrix_finish_and_emit(session, case);
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_arena_factor(case: F5cMatrixCase) {
    let (m, u) = case.parameters();
    let source = matrix_source(case.family, u);
    let mut session = matrix_session(&source, "f5c-resource-matrix-arena-factor");
    assert_eq!(session.batch.definition_uses.len(), u);
    let before = session.finalization.as_ref().unwrap().f5c_resource_probe().arena[0].requested_slots;
    for _ in 0..m {
        let closed = session.finalization.as_mut().unwrap().finalize_scheme(|finalizer| {
            let value = finalizer.positive_int()?;
            finalizer.set_scheme(0, &[], value)
        }).unwrap();
        let (_, checkpoint) = closed.into_parts();
        assert_eq!(checkpoint.retained_bytes_before(), session.current_closed_retained_bytes);
        session.current_closed_retained_bytes = checkpoint.retained_bytes_after();
    }
    let after = session.finalization.as_ref().unwrap().f5c_resource_probe().arena[0].requested_slots;
    assert_eq!(after - before, m, "unrelated closed positive nodes");
    session.sample_f4_resources(ResourceBoundary::InitialAdmission).unwrap();
    session.execute_scc_plan().unwrap();
    assert_eq!(session.execution_counters.instantiation_node_visits, 5 * u);
    assert_eq!(session.execution_counters.instantiation_fresh_value_variables, u);
    assert_eq!(session.instantiation_scratch.substitution_peak_len, 1,
        "one substitution slot is live at a time");
    let identity = session.schemes[0].as_ref().unwrap();
    let view = session.finalization.as_ref().unwrap().scheme_view(identity).unwrap();
    assert_eq!(view.quantifier_count(), 1, "one substitution slot per use");
    assert!(view.recursive_bounds().is_empty());
    matrix_finish_and_emit(session, case);
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_flat_normalization_draft(k: usize, _ordinal: usize) -> f5c_draft::FlatDraft {
    use f5c_draft::{ChildSpan, FlatDraft, NegativeId, NegativeNode, NodeRef,
        PositiveId, PositiveNode};
    assert!(k >= 2);
    let q = k - 1;
    let mut draft = FlatDraft {
        structural_incidences: 2 * k + 2,
        quantifier_count: q as u32,
        predicate: Some(PositiveId(k as u32)),
        positive_nodes: Vec::with_capacity(k + 1),
        negative_nodes: Vec::with_capacity(k + 1),
        positive_children: Vec::with_capacity(k),
        negative_children: Vec::with_capacity(k),
        recursive_bounds: Vec::new(),
        insertion_order: Vec::with_capacity(2 * (k + 1)),
        owners: None,
    };
    for ordinal in 0..q {
        draft.positive_nodes.push(PositiveNode::Quantified(ordinal as u32));
        draft.insertion_order.push(NodeRef::Positive(PositiveId(ordinal as u32)));
        draft.negative_nodes.push(NegativeNode::Quantified(ordinal as u32));
        draft.insertion_order.push(NodeRef::Negative(NegativeId(ordinal as u32)));
    }
    draft.negative_nodes.push(NegativeNode::Int);
    draft.insertion_order.push(NodeRef::Negative(NegativeId(q as u32)));
    draft.negative_children.extend((0..k).map(|id| NegativeId(id as u32)));
    draft.negative_nodes.push(NegativeNode::Intersection(ChildSpan { start: 0, len: k as u32 }));
    draft.insertion_order.push(NodeRef::Negative(NegativeId(k as u32)));
    draft.positive_nodes.push(PositiveNode::Function {
        argument: NegativeId(k as u32), result: PositiveId(0),
    });
    draft.insertion_order.push(NodeRef::Positive(PositiveId(q as u32)));
    draft.positive_children.extend((0..k).map(|id| PositiveId(id as u32)));
    draft.positive_nodes.push(PositiveNode::Union(ChildSpan { start: 0, len: k as u32 }));
    draft.insertion_order.push(NodeRef::Positive(PositiveId(k as u32)));
    assert_eq!(draft.positive_nodes.len(), k + 1);
    assert_eq!(draft.negative_nodes.len(), k + 1);
    assert_eq!(draft.insertion_order.len(), 2 * (k + 1));
    draft
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_stable_merge_sort<T: Copy>(
    values: &mut [T], scratch: &mut [T], compare: &mut impl FnMut(T, T) -> std::cmp::Ordering,
) {
    if values.len() < 2 { return; }
    let middle = values.len() / 2;
    let (left, right) = values.split_at_mut(middle);
    let (left_scratch, right_scratch) = scratch.split_at_mut(middle);
    matrix_stable_merge_sort(left, left_scratch, compare);
    matrix_stable_merge_sort(right, right_scratch, compare);
    let (left, right) = values.split_at(middle);
    let (mut l, mut r, mut out) = (0, 0, 0);
    while l < left.len() && r < right.len() {
        if compare(left[l], right[r]) != std::cmp::Ordering::Greater {
            scratch[out] = left[l]; l += 1;
        } else {
            scratch[out] = right[r]; r += 1;
        }
        out += 1;
    }
    while l < left.len() { scratch[out] = left[l]; l += 1; out += 1; }
    while r < right.len() { scratch[out] = right[r]; r += 1; out += 1; }
    values.copy_from_slice(&scratch[..values.len()]);
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_normalization_oracle(k: usize) -> (usize, usize) {
    use std::cmp::Ordering;
    let mut child_calls = 0usize;
    let mut word_calls = 0usize;
    // All four integer descriptor-height groups in radix order. Each rank
    // group is passed through the same stable mergesort and adjacent compare
    // schedule, including the singleton composite groups.
    let mut height_zero = Vec::with_capacity(2 * k - 1);
    height_zero.extend((0..k - 1).map(|ordinal| vec![2u32, ordinal as u32]));
    height_zero.push(vec![8]);
    height_zero.extend((0..k - 1).map(|ordinal| vec![9u32, ordinal as u32]));
    let mut intersection = Vec::with_capacity(2 * k + 2);
    intersection.extend([11, k as u32]);
    intersection.extend((k - 1..2 * k - 1).flat_map(|rank| [0, rank as u32]));
    let function = vec![5, 1, 0, 0, 0];
    let mut union = Vec::with_capacity(2 * k + 2);
    union.extend([4, k as u32]);
    union.extend((0..k - 1).flat_map(|rank| [0, rank as u32]));
    union.extend([2, 0]);
    for descriptors in [height_zero, vec![intersection], vec![function], vec![union]] {
        let mut order = (0..descriptors.len()).collect::<Vec<_>>();
        let mut scratch = order.clone();
        let mut compare_descriptor = |left: usize, right: usize| {
            for (l, r) in descriptors[left].iter().zip(&descriptors[right]) {
                word_calls += 1;
                match l.cmp(r) {
                    Ordering::Equal => {}
                    result => return result,
                }
            }
            descriptors[left].len().cmp(&descriptors[right].len())
        };
        matrix_stable_merge_sort(&mut order, &mut scratch, &mut compare_descriptor);
        for pair in order.windows(2) { compare_descriptor(pair[0], pair[1]); }
    }
    for mut children in [
        (0..k).map(|rank| (0u32, (k - 1 + rank) as u32)).collect::<Vec<_>>(),
        (0..k - 1).map(|rank| (0u32, rank as u32))
            .chain(std::iter::once((2u32, 0))).collect::<Vec<_>>(),
    ] {
        let mut scratch = children.clone();
        let mut compare_child = |left: (u32, u32), right: (u32, u32)| {
            child_calls += 1;
            word_calls += 1;
            match left.0.cmp(&right.0) {
                Ordering::Equal => { word_calls += 1; left.1.cmp(&right.1) }
                order => order,
            }
        };
        matrix_stable_merge_sort(&mut children, &mut scratch, &mut compare_child);
        for pair in children.windows(2) { compare_child(pair[0], pair[1]); }
    }
    (child_calls, word_calls)
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_normalization(case: F5cMatrixCase) {
    let (d, k) = case.parameters();
    assert_eq!(d % 2, 0, "paired positive and negative composites");
    let source = matrix_source(F5cMatrixFamily::IndependentIdentities, d / 2);
    let mut session = matrix_session(&source, "f5c-resource-matrix-normalization");
    assert_eq!(session.batch.definitions.len(), d / 2);
    assert_eq!(session.batch.counters.emitted_facts, 5 * (d / 2));
    assert_eq!(session.store.facts().len(), 5 * (d / 2));
    let witness = matrix_flat_normalization_draft(k, 0);
    assert_eq!(witness.positive_children.len(), k);
    assert_eq!(witness.negative_children.len(), k);
    assert_eq!(witness.positive_nodes.len() + witness.negative_nodes.len(), 2 * (k + 1));
    let (child_per_draft, word_per_draft) = matrix_normalization_oracle(k);
    session.f5c_matrix_normalization = Some((k, matrix_flat_normalization_draft));
    session.execute_scc_plan().unwrap();
    assert_eq!(session.execution_counters.generalization_quantifier_writes,
        d / 2 * (k - 1));
    assert_eq!(session.execution_counters.generalization_recursive_binder_writes, 0);
    assert_eq!(session.execution_counters.closed_normalized_key_writes, d * (k + 1));
    assert_eq!(session.execution_counters.closed_normalization_child_comparisons,
        d / 2 * child_per_draft);
    assert_eq!(session.execution_counters.closed_normalization_word_comparisons,
        d / 2 * word_per_draft);
    assert_eq!(session.execution_counters.closed_normalization_hash_probes, 0);
    assert_eq!(session.execution_counters.closed_normalization_hash_admissions, 0);
    assert_eq!(session.execution_counters.closed_normalization_hash_duplicates, 0);
    matrix_finish_and_emit(session, case);
}

#[cfg(feature = "f5c_resource_probe")]
fn matrix_run(case: F5cMatrixCase) {
    match case.family {
        F5cMatrixFamily::IndependentIdentities => matrix_identity(case),
        F5cMatrixFamily::IdentityAliases => matrix_aliases(case),
        F5cMatrixFamily::SharedAcyclic | F5cMatrixFamily::IndependentAcyclic => {
            matrix_acyclic(case)
        }
        F5cMatrixFamily::GuardedCycle => matrix_guarded_cycle(case),
        F5cMatrixFamily::Normalization => matrix_normalization(case),
        F5cMatrixFamily::ArenaFactor => matrix_arena_factor(case),
    }
}

#[cfg(feature = "f5c_resource_probe")]
#[test]
#[ignore = "approved F5c resource matrix preflight"]
fn f5c_resource_matrix_preflight() {
    for family in F5cMatrixFamily::ALL {
        let dimension = match family {
            F5cMatrixFamily::IndependentIdentities => 'D',
            F5cMatrixFamily::IdentityAliases => 'U',
            F5cMatrixFamily::ArenaFactor => 'M',
            _ => 'D',
        };
        let companion = match family {
            F5cMatrixFamily::IndependentIdentities | F5cMatrixFamily::IdentityAliases => None,
            _ => Some(32),
        };
        matrix_run(F5cMatrixCase { family, dimension, size: 32, companion, emit: false });
    }
    eprintln!("F5C_RESOURCE_MATRIX_PREFLIGHT\tfamilies=7\tdimension=32");
}

#[cfg(feature = "f5c_resource_probe")]
#[test]
#[ignore = "isolated F5c guarded cycle D=32 K=32 preflight"]
fn f5c_guarded_cycle_32_32_preflight() {
    matrix_run(F5cMatrixCase {
        family: F5cMatrixFamily::GuardedCycle,
        dimension: 'D',
        size: 32,
        companion: Some(32),
        emit: false,
    });
}

#[cfg(feature = "f5c_resource_probe")]
#[test]
#[ignore = "approved F5c resource matrix case"]
fn f5c_resource_matrix_case() {
    matrix_run(F5cMatrixCase::from_env());
}

#[cfg(feature = "f5c_resource_probe")]
#[test]
#[ignore = "isolated F5c guarded cycle D=32 K=4000 diagnostic"]
fn f5c_guarded_cycle_32_4000_diagnostic() {
    matrix_guarded_cycle(F5cMatrixCase {
        family: F5cMatrixFamily::GuardedCycle,
        dimension: 'D',
        size: 32,
        companion: Some(4000),
        emit: true,
    });
}
