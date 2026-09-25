use super::*;

fn positive_function(argument: F5cNegative, result: F5cPositive) -> F5cPositive {
    F5cPositive::Function {
        argument: Box::new(argument),
        argument_effect: F5cNegativeEffect::Empty,
        result_effect: F5cPositiveEffect::Bottom,
        result: Box::new(result),
    }
}

fn report_normalization(
    case: &str,
    drafts: &mut [GeneralizationDraft],
) -> f5c_normalization::NormalizationStats {
    let stats =
        f5c_normalization::normalize_component(drafts).expect("measurement fixture normalizes");
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
                value = *result;
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
                pending.extend(children);
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
    for depth in [64usize, 256, 1024, 4096] {
        let mut value = F5cPositive::Int;
        for _ in 0..depth {
            value = positive_function(F5cNegative::Top, value);
        }
        let mut drafts = [draft(value, 0)];
        report_normalization(&format!("function_chain_depth_{depth}"), &mut drafts);
        let value = std::mem::replace(&mut drafts[0].predicate, F5cPositive::Bottom);
        assert_eq!(drain_positive_function_chain(value), depth);
    }

    for width in [16usize, 64, 256, 1024] {
        let members = (0..width)
            .map(|ordinal| F5cPositive::Quantified(ordinal as u32))
            .collect();
        let mut drafts = [draft(F5cPositive::Union(members), width)];
        report_normalization(&format!("unique_union_width_{width}"), &mut drafts);
        let F5cPositive::Union(members) =
            std::mem::replace(&mut drafts[0].predicate, F5cPositive::Bottom)
        else {
            panic!("wide normalized result remains a Union");
        };
        assert_eq!(members.len(), width);
    }

    for width in [16usize, 64, 256, 1024] {
        let members = (0..width)
            .map(|_| positive_function(F5cNegative::Top, F5cPositive::Int))
            .collect();
        let mut drafts = [draft(F5cPositive::Union(members), 0)];
        let stats = report_normalization(&format!("duplicate_union_width_{width}"), &mut drafts);
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
        report_normalization(&format!("independent_roots_{root_count}"), &mut drafts);
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
        let expanded = memo.positive_value(root).unwrap();
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
            value = positive_function(F5cNegative::Top, value);
        }
        let mut memo = F5cComponentExpansionMemo::default();
        let empty = HashSet::new();
        let output =
            crate::f5c_replay::replay_positive(&mut memo, &value, &empty, &empty, &empty).unwrap();
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
