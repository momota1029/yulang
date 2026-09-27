use super::*;

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
    let member_count = batch.counters.scc_maximum_component_size;
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
            assert_eq!(
                session.execution_counters,
                capture
                    .transactional_counter_baseline
                    .as_ref()
                    .unwrap()
                    .clone()
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
            "F5C_CANDIDATE_SUMMARY\tcase={name}\tsource_bytes={}\tdefinitions={member_count}\tinternal_references={member_count}\tmembers={member_count}\tpaired_parity_capacity_bytes={paired_parity_bytes}\ttest_capture_inline_bytes={}\tcapture_record_capacity_bytes={}\tboundary_order_capacity_bytes={}\tboundary_samples_capacity_bytes={}\tnormalizer_physical_samples_capacity_bytes={}\tmember_output_length_samples_capacity_bytes={}",
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
) -> CandidateProbeResult {
    let capture = flat.then(|| {
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
        let mut maximum_function_depth = 0;
        let mut normalized_unions = 0;
        while let Some((id, function_depth)) = pending.pop() {
            match view.positive_value(id).unwrap() {
                yu_types::PositiveValueView::Function { result, .. } => {
                    maximum_function_depth = maximum_function_depth.max(function_depth + 1);
                    pending.push((result, function_depth + 1));
                }
                yu_types::PositiveValueView::Union(children) => {
                    normalized_unions += 1;
                    let mut unique = std::collections::HashSet::new();
                    assert!(
                        children.iter().all(|child| unique.insert(*child)),
                        "normalized union retains duplicate child IDs"
                    );
                    if width > 1 {
                        assert_eq!(
                            children.len(),
                            2,
                            "width endpoint collapses to one representative beside Int"
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
        if width > 1 {
            assert_eq!(
                normalized_unions, 1,
                "seeded width must retain one normalized Union"
            );
        }
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
        let boxed =
            candidate_seeded_run(&format!("seeded_depth_{depth}_boxed"), depth, 1, false, 0);
        let flat = candidate_seeded_run(
            &format!("seeded_depth_{depth}_flat"),
            depth,
            1,
            true,
            boxed.retained_bytes(),
        );
        boxed.assert_parity(&flat);
    }
    for width in [8usize, 32, 64] {
        let boxed =
            candidate_seeded_run(&format!("seeded_width_{width}_boxed"), 1, width, false, 0);
        let flat = candidate_seeded_run(
            &format!("seeded_width_{width}_flat"),
            1,
            width,
            true,
            boxed.retained_bytes(),
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
