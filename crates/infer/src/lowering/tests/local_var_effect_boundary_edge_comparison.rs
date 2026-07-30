//! LVB callback construction comparison at the second application boundary.
//!
//! `ConstraintMachine` does not expose a full constraint-record iterator. The harness therefore
//! snapshots the second application's three fresh slots, recovers the structural endpoints from
//! their bounds, and queries each expected canonical edge with `debug_constraint_record_id`.
//! This keeps the comparison structural without adding production-only introspection.

use super::*;

use crate::constraints::explain::{ExplanationBudget, ExplanationEdgeKind};
use crate::constraints::{
    ConstraintWeights, OriginId, RowDerivationRule, StructuralDerivationRule, TypeLevel,
};
use crate::instantiate::instantiate_scheme;

#[derive(Debug)]
struct SecondApplicationEdges {
    callback_to_expected: bool,
    callback_fun_to_expected: bool,
    callback_effect_to_expected: bool,
    family_row_to_expected: bool,
    helper_effect_to_call: bool,
    call_to_result: bool,
    result_has_family_lower: bool,
    callback_level: TypeLevel,
    body_effect_level: TypeLevel,
    callback_birth_level: TypeLevel,
    body_effect_birth_level: TypeLevel,
}

/// Slots that survive from second-application construction until the analysis queue is quiescent.
#[derive(Debug, Clone, Copy)]
struct DeferredSecondApplicationSnapshot {
    helper_ref_value: TypeVar,
    init_value: TypeVar,
    callback_expr: ExprId,
    callback_value: TypeVar,
    callback_fun: PosId,
    callback_body_effect: TypeVar,
    result_effect: TypeVar,
    call_effect: TypeVar,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DefinitionRegistration {
    queue_index: usize,
    root: TypeVar,
}

#[derive(Debug, Clone, Copy)]
struct HandBuiltNestedDefinition {
    def: DefId,
    root: TypeVar,
    boundary: DeferredSecondApplicationSnapshot,
    nested_call: Option<DeferredNestedApplicationSnapshot>,
    queued_registration: Option<DefinitionRegistration>,
}

#[derive(Debug, Clone, Copy)]
struct DeferredNestedApplicationSnapshot {
    target_ref_value: TypeVar,
    callee_ref_value: TypeVar,
    argument_value: TypeVar,
    argument_effect: TypeVar,
    result_value: TypeVar,
    result_effect: TypeVar,
    call_effect: TypeVar,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NestedApplicationEdges {
    callee_ref_to_application: bool,
    resolved_fun_to_application: bool,
    argument_effect_to_call: bool,
    inner_return_effect_to_call: bool,
    call_to_result: bool,
    result_to_callback_body: bool,
    result_is_callback_body: bool,
    callback_body_reaches_result: bool,
    argument_effect_has_outer_family_lower: bool,
    argument_outer_family_row_count: usize,
    argument_outer_family_source_count: usize,
    argument_effect_has_inner_return_family_lower: bool,
    nested_result_has_outer_family_lower: bool,
    callback_body_has_outer_family_lower: bool,
    outer_result_has_outer_family_lower: bool,
    callee_ref_birth_level: TypeLevel,
    argument_effect_birth_level: TypeLevel,
    result_effect_birth_level: TypeLevel,
    call_effect_birth_level: TypeLevel,
    instantiated_argument_birth_level: TypeLevel,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EffectSlotTrace {
    var: TypeVar,
    level: TypeLevel,
    birth_level: TypeLevel,
    has_family_lower: bool,
    has_bottom_lower: bool,
    has_closed_empty_upper: bool,
    lower_nodes: Vec<String>,
    upper_nodes: Vec<String>,
    upper_var_closure: Vec<String>,
}

#[derive(Debug, Clone)]
struct MultiStatementBoundaryTrace {
    statement_effects: Vec<EffectSlotTrace>,
    tail_effect: EffectSlotTrace,
    aggregate_effect: EffectSlotTrace,
    callback_ret_eff: TypeVar,
    callback_evaluation_effect: EffectSlotTrace,
    first_application_effect: EffectSlotTrace,
    second_application_effect: EffectSlotTrace,
}

#[derive(Debug, Clone)]
struct V5NestedBoundaryTrace {
    instantiated_inner_return_effect: EffectSlotTrace,
    actual_callback_body_effect: EffectSlotTrace,
    inner_return_family_lower_path: Vec<String>,
    callback_body_to_residual_rules: Vec<StructuralDerivationRule>,
    callback_body_to_residual_row_rules: Vec<RowDerivationRule>,
    argument_effect: EffectSlotTrace,
    call_effect: EffectSlotTrace,
    result_effect: EffectSlotTrace,
    outer_aggregate_effect: EffectSlotTrace,
    outer_callback_ret_eff: TypeVar,
    outer_second_application_effect: EffectSlotTrace,
    argument_effect_to_call: bool,
    inner_return_effect_to_call: bool,
    call_to_result: bool,
    result_to_outer_aggregate: bool,
}

#[derive(Debug, Clone, Copy)]
struct MultiStatementBoundarySnapshot {
    definition: HandBuiltNestedDefinition,
    statement_effects: [TypeVar; 2],
    tail_effect: TypeVar,
    aggregate_effect: TypeVar,
    callback_evaluation_effect: TypeVar,
    first_application_effect: TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SemanticEffectSlotTrace {
    level: TypeLevel,
    birth_level: TypeLevel,
    has_family_lower: bool,
    has_bottom_lower: bool,
    has_closed_empty_upper: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SemanticMultiStatementBoundaryTrace {
    statement_effects: Vec<SemanticEffectSlotTrace>,
    tail_effect: SemanticEffectSlotTrace,
    aggregate_effect: SemanticEffectSlotTrace,
    callback_ret_eff_is_aggregate: bool,
    callback_evaluation_effect: SemanticEffectSlotTrace,
    first_application_effect: SemanticEffectSlotTrace,
    second_application_effect: SemanticEffectSlotTrace,
}

#[test]
fn parsed_and_hand_built_callbacks_register_the_same_second_application_edges() {
    let parsed = second_application_edges(CallbackConstruction::Parsed);
    let hand_built = second_application_edges(CallbackConstruction::HandBuilt);

    assert!(
        parsed.callback_to_expected
            && parsed.callback_fun_to_expected
            && parsed.callback_effect_to_expected
            && parsed.family_row_to_expected
            && parsed.helper_effect_to_call
            && parsed.call_to_result,
        "parsed callback must exercise the complete second-application decomposition: {parsed:#?}"
    );
    assert!(
        hand_built.callback_to_expected
            && hand_built.callback_fun_to_expected
            && hand_built.callback_effect_to_expected
            && hand_built.family_row_to_expected
            && hand_built.helper_effect_to_call
            && hand_built.call_to_result,
        "hand-built callback must exercise the complete second-application decomposition: \
         {hand_built:#?}"
    );
    assert_eq!(
        parsed.result_has_family_lower, hand_built.result_has_family_lower,
        "the two constructions must agree on pre-compact family reachability"
    );
    assert!(
        !parsed.result_has_family_lower,
        "the isolated LVB-A4 shape must discharge the local family in both constructions"
    );
    assert_eq!(parsed.callback_level, hand_built.callback_level);
    assert_eq!(parsed.body_effect_level, hand_built.body_effect_level);
    assert_eq!(parsed.callback_birth_level, hand_built.callback_birth_level);
    assert_eq!(
        parsed.body_effect_birth_level,
        hand_built.body_effect_birth_level
    );
    assert_eq!(
        parsed.callback_level,
        TypeLevel::root(),
        "both callback values are wrapped after leaving the lambda body level"
    );
    assert_eq!(
        parsed.body_effect_level,
        TypeLevel::root(),
        "application constraints extrude both callback body effects to the enclosing level"
    );
    assert_eq!(
        parsed.body_effect_birth_level,
        TypeLevel::root().child(),
        "both callback body effects are born in the child level used by normal lambda lowering"
    );
}

#[test]
fn parsed_and_hand_built_callbacks_keep_the_same_edges_after_deferred_resolution() {
    let (output, parsed, hand_built) = deferred_resolution_fixture();
    assert!(
        !output.session.has_pending_work(),
        "the comparison must inspect a quiescent post-UseResolved constraint graph"
    );

    let parsed = post_resolution_edges(&output, parsed);
    let hand_built = post_resolution_edges(&output, hand_built);

    assert_eq!(
        parsed, hand_built,
        "the post-resolution canonical edge snapshots must agree"
    );
    assert!(
        !parsed.result_has_family_lower,
        "both full-pipeline witnesses must discharge the handled local family"
    );
    assert!(
        parsed.callback_to_expected
            && parsed.callback_fun_to_expected
            && parsed.callback_effect_to_expected
            && parsed.family_row_to_expected
            && parsed.helper_effect_to_call
            && parsed.call_to_result,
        "all six canonical post-resolution edges must remain inspectable: {parsed:#?}"
    );
}

#[test]
fn nested_hand_built_outer_retains_family_despite_matching_edges_and_ordered_generalization() {
    let (mut output, parsed_inner, parsed_outer, hand_inner, hand_outer, _, _, _, _) =
        nested_deferred_resolution_fixture();
    assert!(
        !output.session.has_pending_work(),
        "the nested comparison must inspect a quiescent post-UseResolved constraint graph"
    );

    let parsed_inner_edges = post_resolution_edges(&output, parsed_inner.boundary);
    let parsed_outer_edges = post_resolution_edges(&output, parsed_outer.boundary);
    let hand_inner_edges = post_resolution_edges(&output, hand_inner.boundary);
    let hand_outer_edges = post_resolution_edges(&output, hand_outer.boundary);
    assert_eq!(parsed_inner_edges, hand_inner_edges);
    for (label, edges) in [
        ("parsed inner", parsed_inner_edges),
        ("parsed outer", parsed_outer_edges),
        ("hand-built inner", hand_inner_edges),
        ("hand-built outer", hand_outer_edges),
    ] {
        assert!(
            edges.callback_to_expected
                && edges.callback_fun_to_expected
                && edges.callback_effect_to_expected
                && edges.family_row_to_expected
                && edges.helper_effect_to_call
                && edges.call_to_result,
            "{label} must retain all six canonical post-resolution edges: {edges:#?}"
        );
    }
    assert!(!parsed_outer_edges.result_has_family_lower);
    assert!(hand_outer_edges.result_has_family_lower);

    let parsed_nested_edges = nested_application_edges(&output, parsed_outer);
    let hand_nested_edges = nested_application_edges(&output, hand_outer);
    for (label, edges) in [
        ("parsed nested call", parsed_nested_edges),
        ("hand-built nested call", hand_nested_edges),
    ] {
        assert!(
            edges.callee_ref_to_application
                && edges.resolved_fun_to_application
                && edges.argument_effect_to_call
                && edges.inner_return_effect_to_call
                && edges.call_to_result,
            "{label} must retain the nested application's complete effect wiring: {edges:#?}"
        );
        assert!(
            edges.argument_effect_has_outer_family_lower
                && edges.nested_result_has_outer_family_lower
                && edges.callback_body_has_outer_family_lower,
            "{label} must transport the outer family through argument, call result, and callback \
             body: {edges:#?}"
        );
        assert_eq!(
            edges.instantiated_argument_birth_level,
            TypeLevel::secondary(),
            "{label} must instantiate the already-generalized inner scheme at the ordinary \
             deferred-use level"
        );
    }
    assert_eq!(parsed_nested_edges.argument_outer_family_row_count, 1);
    assert_eq!(hand_nested_edges.argument_outer_family_row_count, 1);
    assert!(
        hand_nested_edges.argument_outer_family_source_count
            > parsed_nested_edges.argument_outer_family_source_count,
        "the hand-built nested argument is the whole prior callback body, so more outer-family \
         source slots feed its one concrete row: parsed={parsed_nested_edges:#?}, \
         hand-built={hand_nested_edges:#?}"
    );
    assert!(
        !parsed_nested_edges.argument_effect_has_inner_return_family_lower,
        "the parsed call argument is only its final r.get() computation"
    );
    assert!(
        hand_nested_edges.argument_effect_has_inner_return_family_lower,
        "the hand-built call argument is the whole prior body, including its observe effect"
    );
    assert!(
        parsed_nested_edges.result_to_callback_body && !parsed_nested_edges.result_is_callback_body,
        "parsed block lowering must connect the nested result into a distinct aggregate body \
         effect: {parsed_nested_edges:#?}"
    );
    assert!(
        !hand_nested_edges.result_to_callback_body && hand_nested_edges.result_is_callback_body,
        "the hand-built wrapper uses the nested result effect itself as the callback body effect: \
         {hand_nested_edges:#?}"
    );
    assert!(
        parsed_nested_edges.callback_body_reaches_result
            && hand_nested_edges.callback_body_reaches_result
    );
    assert!(!parsed_nested_edges.outer_result_has_outer_family_lower);
    assert!(hand_nested_edges.outer_result_has_outer_family_lower);
    for edges in [parsed_nested_edges, hand_nested_edges] {
        assert_eq!(
            edges.callee_ref_birth_level,
            edges.argument_effect_birth_level
        );
        assert_eq!(
            edges.callee_ref_birth_level,
            edges.result_effect_birth_level
        );
        assert_eq!(edges.callee_ref_birth_level, edges.call_effect_birth_level);
    }
    assert_eq!(
        parsed_nested_edges.callee_ref_birth_level,
        hand_nested_edges.callee_ref_birth_level.child(),
        "normal parsed nesting puts the inner call one lexical level deeper than the current \
         hand-built wrapper"
    );

    let parsed_inner_family = resolved_snapshot_family_path(&output, parsed_inner.boundary);
    let parsed_outer_family = resolved_snapshot_family_path(&output, parsed_outer.boundary);
    let hand_inner_family = resolved_snapshot_family_path(&output, hand_inner.boundary);
    let hand_outer_family = resolved_snapshot_family_path(&output, hand_outer.boundary);
    assert_ne!(parsed_inner_family, parsed_outer_family);
    assert_ne!(hand_inner_family, hand_outer_family);

    let events = output.session.take_scc_events();
    assert!(
        parsed_inner.def.0 < parsed_outer.def.0,
        "module-map source registration must assign the inner definition before the outer"
    );
    assert_hand_registration_root(hand_inner);
    assert_hand_registration_root(hand_outer);
    assert!(
        hand_inner
            .queued_registration
            .expect("hand inner registration")
            .queue_index
            < hand_outer
                .queued_registration
                .expect("hand outer registration")
                .queue_index,
        "the hand-built inner RegisterDef must be enqueued before the outer RegisterDef"
    );
    for pair in [(parsed_inner, parsed_outer), (hand_inner, hand_outer)] {
        assert_inner_generalized_before_outer_use(events.as_slice(), pair.0, pair.1);
    }

    for definition in [parsed_inner, parsed_outer, hand_inner, hand_outer] {
        assert!(
            output
                .session
                .generalized_scheme_record(definition.def)
                .is_some(),
            "{:?} must have a finalized generalized-scheme record",
            definition.def
        );
        assert!(
            def_scheme(&output, definition.def)
                .stack_quantifiers
                .is_empty(),
            "{:?} must not retain a raw subtraction owner",
            definition.def
        );
    }
    let parsed_outer_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, parsed_outer.def),
    );
    for family in [&parsed_inner_family, &parsed_outer_family] {
        let family = family.join("::");
        assert!(
            !parsed_outer_scheme.contains(&family),
            "the parsed outer control must discharge {family}: {parsed_outer_scheme}"
        );
    }

    let hand_inner_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, hand_inner.def),
    );
    let parsed_inner_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, parsed_inner.def),
    );
    assert_eq!(
        parsed_inner_scheme, hand_inner_scheme,
        "the nested targets themselves must finalize to the same generalized scheme"
    );
    let hand_inner_family_name = hand_inner_family.join("::");
    assert!(
        !hand_inner_scheme.contains(&hand_inner_family_name),
        "the single hand-built inner boundary must discharge {hand_inner_family_name}: \
         {hand_inner_scheme}"
    );

    let hand_outer_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, hand_outer.def),
    );
    assert!(
        !hand_outer_scheme.contains(&hand_inner_family_name),
        "the already-generalized inner family must not leak into the hand-built outer scheme: \
         {hand_outer_scheme}"
    );
    let hand_outer_family_name = hand_outer_family.join("::");
    assert!(
        hand_outer_scheme.contains(&hand_outer_family_name),
        "the nested hand-built gap must retain the outer family {hand_outer_family_name}: \
         {hand_outer_scheme}"
    );
}

#[test]
fn v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization() {
    let (mut output, _, _, _, _, parsed_inner, parsed_outer, hand_inner, hand_outer) =
        nested_deferred_resolution_fixture();
    assert!(
        !output.session.has_pending_work(),
        "the v5 nested comparison must inspect a quiescent post-UseResolved graph"
    );

    let parsed_inner_family = resolved_snapshot_family_path(&output, parsed_inner.boundary);
    let parsed_outer_family = resolved_snapshot_family_path(&output, parsed_outer.boundary);
    let hand_inner_family = resolved_snapshot_family_path(&output, hand_inner.boundary);
    let hand_outer_family = resolved_snapshot_family_path(&output, hand_outer.boundary);
    assert_ne!(parsed_inner_family, parsed_outer_family);
    assert_ne!(hand_inner_family, hand_outer_family);

    let parsed_inner_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, parsed_inner.def),
    );
    let hand_inner_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, hand_inner.def),
    );
    let parsed_outer_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, parsed_outer.def),
    );
    let hand_outer_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, hand_outer.def),
    );
    eprintln!("v5 parsed inner finalized scheme: {parsed_inner_scheme}");
    eprintln!("v5 hand-built inner finalized scheme: {hand_inner_scheme}");
    eprintln!("v5 parsed outer finalized scheme: {parsed_outer_scheme}");
    eprintln!("v5 hand-built outer finalized scheme: {hand_outer_scheme}");

    let parsed_nested =
        v5_nested_boundary_trace(&output, parsed_outer, parsed_inner_family.as_slice());
    let hand_nested = v5_nested_boundary_trace(&output, hand_outer, hand_inner_family.as_slice());
    eprintln!("v5 parsed nested trace: {parsed_nested:#?}");
    eprintln!("v5 hand-built nested trace: {hand_nested:#?}");
    for (label, trace) in [("parsed", &parsed_nested), ("hand-built", &hand_nested)] {
        assert!(
            trace.argument_effect_to_call
                && trace.inner_return_effect_to_call
                && trace.call_to_result
                && trace.result_to_outer_aggregate,
            "{label} nested call must retain the complete call-to-aggregate wiring: {trace:#?}"
        );
        assert_eq!(
            trace.outer_callback_ret_eff, trace.outer_aggregate_effect.var,
            "{label} outer callback Fun.ret_eff must be the block aggregate"
        );
    }

    let hand_inner_family_name = hand_inner_family.join("::");
    let hand_outer_family_name = hand_outer_family.join("::");
    let parsed_inner_family_name = parsed_inner_family.join("::");
    let parsed_outer_family_name = parsed_outer_family.join("::");
    let normalized_parsed_inner =
        parsed_inner_scheme.replace(&parsed_inner_family_name, "<inner-family>");
    let normalized_hand_inner = hand_inner_scheme
        .replace(&format!("\"{hand_inner_family_name}\""), "<inner-family>")
        .replace(&hand_inner_family_name, "<inner-family>");
    assert_eq!(
        normalized_parsed_inner, normalized_hand_inner,
        "the v5 hand-built inner must finalize to the parsed LVB-A3 target structure"
    );
    assert!(
        def_scheme(&output, hand_inner.def)
            .stack_quantifiers
            .is_empty(),
        "the v5 inner target must not retain a raw subtraction owner: {hand_inner_scheme}"
    );
    assert!(
        !hand_outer_scheme.contains(&hand_outer_family_name),
        "the v5 outer boundary must discharge its own family: {hand_outer_scheme}"
    );
    assert!(
        !parsed_outer_scheme.contains(&parsed_inner_family_name)
            && !parsed_outer_scheme.contains(&parsed_outer_family_name),
        "the parsed nested control must isolate both local families: {parsed_outer_scheme}"
    );
    assert!(
        !hand_outer_scheme.contains(&hand_inner_family_name),
        "the v5 nested witness must exclude the inner family from the outer finalized scheme: \
         {hand_outer_scheme}"
    );
    assert!(
        parsed_nested.actual_callback_body_effect.has_family_lower
            && hand_nested.actual_callback_body_effect.has_family_lower,
        "both callbacks genuinely use the inner ref family"
    );
    assert!(
        !parsed_nested.argument_effect.has_family_lower
            && !hand_nested.argument_effect.has_family_lower,
        "callback value evaluation stays exact-pure; the leak is not argument evaluation"
    );
    assert!(
        !parsed_nested
            .instantiated_inner_return_effect
            .has_family_lower
            && !parsed_nested.call_effect.has_family_lower
            && !parsed_nested.result_effect.has_family_lower
            && !parsed_nested.outer_aggregate_effect.has_family_lower
            && !parsed_nested
                .outer_second_application_effect
                .has_family_lower,
        "the parsed control must keep the inner family out of every result-side effect slot: \
         {parsed_nested:#?}"
    );
    assert!(
        hand_nested
            .instantiated_inner_return_effect
            .has_family_lower
            && hand_nested.call_effect.has_family_lower
            && hand_nested.result_effect.has_family_lower
            && hand_nested.outer_aggregate_effect.has_family_lower
            && hand_nested.outer_second_application_effect.has_family_lower,
        "the first hand-built result-side contamination must propagate through outer finalize: \
         {hand_nested:#?}"
    );
    assert!(
        !hand_nested.inner_return_family_lower_path.is_empty()
            && parsed_nested.inner_return_family_lower_path.is_empty(),
        "only the hand-built instantiated residual may have a concrete inner-family lower path"
    );
    assert!(
        !hand_nested.callback_body_to_residual_rules.is_empty()
            && parsed_nested.callback_body_to_residual_rules.is_empty(),
        "only the hand-built callback body may connect directly to the instantiated residual"
    );
    assert!(
        hand_nested
            .callback_body_to_residual_rules
            .contains(&StructuralDerivationRule::FunctionReturnEffect),
        "the direct residual connection must be derived by function return-effect decomposition"
    );
    assert!(
        hand_nested
            .callback_body_to_residual_row_rules
            .contains(&RowDerivationRule::UnweightedReduction),
        "the concrete family must enter the residual when the expected handled row is reduced \
         against callback-body lowers that already exist"
    );

    let events = output.session.take_scc_events();
    assert_inner_generalized_before_outer_use(events.as_slice(), parsed_inner, parsed_outer);
    assert_inner_generalized_before_outer_use(events.as_slice(), hand_inner, hand_outer);
}

#[test]
fn single_multi_statement_boundary_traces_block_aggregate_through_finalization() {
    let (
        mut output,
        parsed,
        hand_built,
        level_aligned,
        deferred_reference,
        pre_parsed,
        pre_hand_built,
        pre_level_aligned,
        pre_deferred_reference,
        helper,
    ) = multi_statement_single_boundary_fixture();
    assert!(
        !output.session.has_pending_work(),
        "the comparison must inspect a quiescent post-UseResolved constraint graph"
    );

    let family_path = resolved_snapshot_family_path(&output, parsed.definition.boundary);
    let post_parsed = multi_statement_boundary_trace(&output.session, parsed, &family_path);
    let post_hand_built = multi_statement_boundary_trace(&output.session, hand_built, &family_path);
    let post_level_aligned =
        multi_statement_boundary_trace(&output.session, level_aligned, &family_path);
    let post_deferred_reference =
        multi_statement_boundary_trace(&output.session, deferred_reference, &family_path);
    eprintln!("pre-quiescence parsed: {pre_parsed:#?}");
    eprintln!("pre-quiescence hand-built: {pre_hand_built:#?}");
    eprintln!("pre-quiescence level-aligned control: {pre_level_aligned:#?}");
    eprintln!("pre-quiescence deferred-reference control: {pre_deferred_reference:#?}");
    eprintln!("post-quiescence parsed: {post_parsed:#?}");
    eprintln!("post-quiescence hand-built: {post_hand_built:#?}");
    eprintln!("post-quiescence level-aligned control: {post_level_aligned:#?}");
    eprintln!("post-quiescence deferred-reference control: {post_deferred_reference:#?}");
    eprintln!(
        "post aggregate upper closure parsed={:?}",
        post_parsed.aggregate_effect.upper_var_closure
    );
    eprintln!(
        "post aggregate upper closure hand-built={:?}",
        post_hand_built.aggregate_effect.upper_var_closure
    );
    eprintln!(
        "post aggregate upper closure level-aligned={:?}",
        post_level_aligned.aggregate_effect.upper_var_closure
    );
    for (phase, label, trace) in [
        ("pre", "parsed", &pre_parsed),
        ("pre", "hand-built", &pre_hand_built),
        ("pre", "level-aligned", &pre_level_aligned),
        ("pre", "deferred-reference", &pre_deferred_reference),
        ("post", "parsed", &post_parsed),
        ("post", "hand-built", &post_hand_built),
        ("post", "level-aligned", &post_level_aligned),
        ("post", "deferred-reference", &post_deferred_reference),
    ] {
        let slots = |effects: &[EffectSlotTrace]| {
            effects
                .iter()
                .map(|effect| {
                    (
                        effect.var,
                        effect.birth_level,
                        effect.level,
                        effect.has_family_lower,
                    )
                })
                .collect::<Vec<_>>()
        };
        eprintln!(
            "{phase} compact {label}: statements={:?}, tail={:?}, aggregate={:?}, \
             callback_ret={:?}, callback_eval={:?}, first_app={:?}, second_app={:?}",
            slots(trace.statement_effects.as_slice()),
            slots(std::slice::from_ref(&trace.tail_effect))[0],
            slots(std::slice::from_ref(&trace.aggregate_effect))[0],
            trace.callback_ret_eff,
            slots(std::slice::from_ref(&trace.callback_evaluation_effect))[0],
            slots(std::slice::from_ref(&trace.first_application_effect))[0],
            slots(std::slice::from_ref(&trace.second_application_effect))[0],
        );
    }

    for (label, snapshot, trace) in [
        ("parsed", parsed, &post_parsed),
        ("hand-built", hand_built, &post_hand_built),
        (
            "level-aligned hand-built control",
            level_aligned,
            &post_level_aligned,
        ),
        (
            "deferred-reference hand-built control",
            deferred_reference,
            &post_deferred_reference,
        ),
    ] {
        assert_eq!(
            snapshot.aggregate_effect, snapshot.definition.boundary.callback_body_effect,
            "{label} callback Fun.ret_eff must retain the real block-aggregate slot"
        );
        assert_eq!(
            trace.callback_ret_eff, trace.aggregate_effect.var,
            "{label} callback Fun.ret_eff must be the aggregate itself"
        );
        assert!(
            trace
                .statement_effects
                .iter()
                .all(|effect| effect.has_family_lower),
            "{label} statement effects must each receive the handled family after deferred \
             operation resolution: {trace:#?}"
        );
        assert!(
            trace.aggregate_effect.has_family_lower,
            "{label} block aggregate must receive its statements' handled family: {trace:#?}"
        );
        assert!(
            snapshot
                .statement_effects
                .into_iter()
                .chain([snapshot.tail_effect])
                .all(|effect| {
                    var_reaches_var(
                        output.session.infer.constraints(),
                        snapshot.aggregate_effect,
                        effect,
                    )
                }),
            "{label} block aggregate must remain downstream of every individual computation"
        );
        assert!(
            trace.callback_evaluation_effect.has_closed_empty_upper
                && !trace.callback_evaluation_effect.has_family_lower,
            "{label} callback value evaluation must retain the exact-pure closed-empty upper and \
             no non-pure family lower: {trace:#?}"
        );
    }

    assert_ne!(
        semantic_multi_statement_trace(&pre_parsed),
        semantic_multi_statement_trace(&pre_hand_built),
        "the construction-time trace must expose the hand-built lifecycle divergence"
    );
    assert_ne!(
        semantic_multi_statement_trace(&post_parsed),
        semantic_multi_statement_trace(&post_hand_built),
        "the post-resolution trace must retain the construction-level lifecycle divergence"
    );
    assert!(
        pre_parsed
            .statement_effects
            .iter()
            .all(|effect| !effect.has_family_lower)
            && pre_hand_built
                .statement_effects
                .iter()
                .all(|effect| !effect.has_family_lower),
        "both controls must defer source-level operation resolution"
    );
    for (parsed_effect, hand_effect) in post_parsed
        .statement_effects
        .iter()
        .chain([&post_parsed.tail_effect, &post_parsed.aggregate_effect])
        .zip(post_hand_built.statement_effects.iter().chain([
            &post_hand_built.tail_effect,
            &post_hand_built.aggregate_effect,
        ]))
    {
        assert_eq!(
            parsed_effect.birth_level,
            hand_effect.birth_level.child(),
            "the first stable divergence is already present in each statement and block aggregate"
        );
        assert_eq!(
            parsed_effect.level,
            hand_effect.level.child(),
            "the hand-built callback body remains one TypeLevel shallower"
        );
    }
    assert!(
        !post_parsed.first_application_effect.has_family_lower
            && !post_hand_built.first_application_effect.has_family_lower,
        "point (e) must remain family-free in both constructions"
    );
    assert!(
        !post_parsed.second_application_effect.has_family_lower
            && !post_hand_built.second_application_effect.has_family_lower,
        "incremental unweighted row reduction must close the former point (f) divergence"
    );
    assert_eq!(
        post_parsed.aggregate_effect.birth_level,
        post_level_aligned.aggregate_effect.birth_level
    );
    assert_eq!(
        post_parsed.aggregate_effect.level, post_level_aligned.aggregate_effect.level,
        "incremental row reduction must leave the level-aligned aggregate at the parsed level"
    );
    assert!(
        !post_level_aligned
            .second_application_effect
            .has_family_lower,
        "the level-aligned control must also discharge after incremental row reduction"
    );
    assert!(
        post_parsed
            .aggregate_effect
            .upper_nodes
            .iter()
            .any(|upper| upper.starts_with("Row("))
            && post_hand_built
                .aggregate_effect
                .upper_nodes
                .iter()
                .any(|upper| upper.starts_with("Row("))
            && post_level_aligned
                .aggregate_effect
                .upper_nodes
                .iter()
                .any(|upper| upper.starts_with("Row(")),
        "all three main cases must receive the helper's concrete expected callback row"
    );
    assert_eq!(
        post_parsed.aggregate_effect.birth_level,
        post_deferred_reference.aggregate_effect.birth_level
    );
    assert_eq!(
        post_parsed.aggregate_effect.level,
        post_deferred_reference.aggregate_effect.level
    );
    assert!(
        !post_deferred_reference
            .second_application_effect
            .has_family_lower,
        "deferring the local-reference structure until helper resolution must restore discharge"
    );

    let parsed_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, parsed.definition.def),
    );
    let hand_built_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, hand_built.definition.def),
    );
    let level_aligned_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, level_aligned.definition.def),
    );
    let deferred_reference_scheme = poly::dump::format_scheme(
        &output.session.poly.typ,
        def_scheme(&output, deferred_reference.definition.def),
    );
    let helper_scheme =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, helper));
    eprintln!("helper scheme: {helper_scheme}");
    eprintln!("parsed finalized scheme: {parsed_scheme}");
    eprintln!("hand-built finalized scheme: {hand_built_scheme}");
    eprintln!("level-aligned finalized scheme: {level_aligned_scheme}");
    eprintln!("deferred-reference finalized scheme: {deferred_reference_scheme}");
    assert!(
        def_scheme(&output, helper).stack_quantifiers.is_empty(),
        "the helper producer must not retain a raw subtraction owner: {helper_scheme}"
    );
    let family_name = family_path.join("::");
    assert!(
        !parsed_scheme.contains(&family_name),
        "the parsed multi-statement control must discharge {family_name}: {parsed_scheme}"
    );
    assert!(
        !hand_built_scheme.contains(&family_name),
        "incremental row reduction must discharge {family_name} from the hand-built boundary: \
         {hand_built_scheme}"
    );
    assert_eq!(
        parsed_scheme, hand_built_scheme,
        "the repaired hand-built boundary must finalize to the parsed scheme"
    );
    assert_eq!(
        hand_built_scheme, level_aligned_scheme,
        "the birth-level-aligned control must converge independently of raw birth depth"
    );
    assert_eq!(
        parsed_scheme, deferred_reference_scheme,
        "with identical hand-built wrapping and levels, only deferring the reference structure \
         restores the parsed finalized scheme"
    );

    // Preserve and inspect SCC ordering only after all finalized-scheme observations are complete.
    let events = output.session.take_scc_events();
    let event_positions = |snapshot: MultiStatementBoundarySnapshot| {
        let instantiate = events
            .iter()
            .position(|event| {
                matches!(
                    event,
                    SccEvent::InstantiateUse {
                        parent,
                        target,
                        use_value,
                    } if *parent == snapshot.definition.def
                        && *target == helper
                        && *use_value == snapshot.definition.boundary.helper_ref_value
                )
            })
            .expect("the helper ref must instantiate through deferred UseResolved");
        let quantify = events
            .iter()
            .position(|event| {
                matches!(
                    event,
                    SccEvent::QuantifyComponent { component, roots }
                        if component == &vec![snapshot.definition.def]
                            && roots == &vec![snapshot.definition.root]
                )
            })
            .expect("the enclosing definition must be quantified");
        (instantiate, quantify)
    };
    let parsed_events = event_positions(parsed);
    let hand_built_events = event_positions(hand_built);
    let level_aligned_events = event_positions(level_aligned);
    let deferred_reference_events = event_positions(deferred_reference);
    eprintln!(
        "helper InstantiateUse/parent QuantifyComponent positions: parsed={parsed_events:?}, \
         hand-built={hand_built_events:?}, level-aligned={level_aligned_events:?}, \
         deferred-reference={deferred_reference_events:?}"
    );
    assert!(
        parsed_events.0 < parsed_events.1,
        "parsed lowering must instantiate the helper before finalizing its parent"
    );
    assert!(
        hand_built_events.0 < hand_built_events.1
            && level_aligned_events.0 < level_aligned_events.1
            && deferred_reference_events.0 < deferred_reference_events.1,
        "SCC ordering must be identical: every helper use instantiates before parent quantification"
    );
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PostResolutionEdges {
    callback_to_expected: bool,
    callback_fun_to_expected: bool,
    callback_effect_to_expected: bool,
    family_row_to_expected: bool,
    helper_effect_to_call: bool,
    call_to_result: bool,
    result_has_family_lower: bool,
}

#[derive(Clone, Copy)]
enum CallbackConstruction {
    Parsed,
    HandBuilt,
}

fn second_application_edges(construction: CallbackConstruction) -> SecondApplicationEdges {
    let (mut output, helper, owner, site) = boundary_fixture();
    let helper_scheme = def_scheme(&output, helper).clone();
    let helper_predicate = instantiate_scheme(
        &output.session.poly.typ,
        &mut output.session.infer,
        TypeLevel::root(),
        &helper_scheme,
    );
    let family_path = instantiated_helper_family_path(
        output.session.infer.constraints().types(),
        helper_predicate,
    );
    let module = output.modules.root_id();

    let mut lowerer = ExprLowerer::new(&mut output.session, &output.modules, module, site, owner);
    let helper_value = lowerer.fresh_type_var();
    let helper_effect = lowerer.fresh_exact_pure_effect();
    lowerer.subtype_pos_to_var(helper_predicate, helper_value);
    let helper_expr = lowerer.session.poly.add_expr(Expr::Lit(Lit::Unit));
    let helper = Computation::value(helper_expr, helper_value, helper_effect);
    let init = lowerer.unit_expr();
    let helper_with_init = lowerer.make_internal_app(helper, init);

    let (callback, callback_fun, body_effect, family_row) = match construction {
        CallbackConstruction::Parsed => parsed_callback(&mut lowerer, &family_path, init.value),
        CallbackConstruction::HandBuilt => {
            hand_built_callback(&mut lowerer, &family_path, init.value)
        }
    };
    let callback_level = lowerer.session.infer.constraints().level_of(callback.value);
    let body_effect_level = lowerer.session.infer.constraints().level_of(body_effect);
    let callback_birth_level = lowerer
        .session
        .infer
        .constraints()
        .birth_level_of(callback.value);
    let body_effect_birth_level = lowerer
        .session
        .infer
        .constraints()
        .birth_level_of(body_effect);

    let expected_callback = lowerer
        .session
        .infer
        .constraints()
        .bounds()
        .of(helper_with_init.value)
        .and_then(|bounds| {
            bounds.lowers().iter().find_map(|bound| {
                match lowerer.session.infer.constraints().types().pos(bound.pos) {
                    Pos::Fun { arg, .. } => Some(*arg),
                    _ => None,
                }
            })
        })
        .expect("the first application must expose the helper's callback argument");
    let (expected_callback_effect, helper_result_effect) = match lowerer
        .session
        .infer
        .constraints()
        .types()
        .neg(expected_callback)
    {
        Neg::Fun { ret_eff, .. } => {
            let helper_result_effect = lowerer
                .session
                .infer
                .constraints()
                .bounds()
                .of(helper_with_init.value)
                .and_then(|bounds| {
                    bounds.lowers().iter().find_map(|bound| {
                        match lowerer.session.infer.constraints().types().pos(bound.pos) {
                            Pos::Fun { ret_eff, .. } => Some(*ret_eff),
                            _ => None,
                        }
                    })
                })
                .expect("helper result effect");
            (*ret_eff, helper_result_effect)
        }
        other => panic!("helper callback must be a function, got {other:?}"),
    };

    let next = lowerer.session.infer.constraints().next_type_var();
    let result = lowerer.make_internal_app(helper_with_init, callback);
    // `make_app_with_origins` allocates result value, result effect, and call effect in this order.
    // Capturing `next_type_var` is the existing test-only seam for isolating d2 without changing
    // production application lowering.
    let call_effect = TypeVar(next + 2);
    assert_eq!(result.value, TypeVar(next));
    assert_eq!(result.effect, TypeVar(next + 1));

    let types = lowerer.session.infer.constraints().types();
    let callback_var = types
        .pos_nodes()
        .iter()
        .position(|node| matches!(node, Pos::Var(var) if *var == callback.value))
        .map(|index| PosId(index as u32))
        .expect("callback value use");
    let callback_effect = match types.pos(callback_fun) {
        Pos::Fun { ret_eff, .. } => *ret_eff,
        _ => unreachable!(),
    };
    let call_effect_upper = types
        .neg_nodes()
        .iter()
        .position(|node| matches!(node, Neg::Var(var) if *var == call_effect))
        .map(|index| NegId(index as u32))
        .expect("call-effect upper");
    let result_effect_upper = types
        .neg_nodes()
        .iter()
        .position(|node| matches!(node, Neg::Var(var) if *var == result.effect))
        .map(|index| NegId(index as u32))
        .expect("result-effect upper");
    let call_effect_lower = types
        .pos_nodes()
        .iter()
        .position(|node| matches!(node, Pos::Var(var) if *var == call_effect))
        .map(|index| PosId(index as u32))
        .expect("call-effect lower");

    let machine = lowerer.session.infer.constraints();
    let has_edge = |lower, upper| {
        machine
            .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .is_some()
    };
    SecondApplicationEdges {
        callback_to_expected: has_edge(callback_var, expected_callback),
        callback_fun_to_expected: has_edge(callback_fun, expected_callback),
        callback_effect_to_expected: has_edge(callback_effect, expected_callback_effect),
        family_row_to_expected: has_edge(family_row, expected_callback_effect),
        helper_effect_to_call: has_edge(helper_result_effect, call_effect_upper),
        call_to_result: has_edge(call_effect_lower, result_effect_upper),
        result_has_family_lower: var_reaches_family(machine, result.effect, &family_path),
        callback_level,
        body_effect_level,
        callback_birth_level,
        body_effect_birth_level,
    }
}

fn parsed_callback(
    lowerer: &mut ExprLowerer<'_>,
    family_path: &[String],
    payload: TypeVar,
) -> (Computation, PosId, TypeVar, PosId) {
    // The application body supplies a non-pure body effect slot through the ordinary lambda path.
    // The explicit family lower models the local-ref operation while keeping this edge-focused
    // witness independent of selection analysis.
    let root = parse("my callback = \\r -> (\\_ -> ()) r\n");
    let callback = lowerer
        .lower_expr(&binding_expr(&root, "callback"))
        .expect("parsed callback lowering");
    let callback_fun = function_lower_bound(lowerer, callback.value);
    let body_effect = match lowerer
        .session
        .infer
        .constraints()
        .types()
        .pos(callback_fun)
    {
        Pos::Fun { ret_eff, .. } => match lowerer.session.infer.constraints().types().pos(*ret_eff)
        {
            Pos::Var(effect) => *effect,
            other => panic!("parsed callback body effect must be a variable, got {other:?}"),
        },
        _ => unreachable!(),
    };
    let family_row = add_family_effect(lowerer, body_effect, family_path, payload);
    (callback, callback_fun, body_effect, family_row)
}

fn hand_built_callback(
    lowerer: &mut ExprLowerer<'_>,
    family_path: &[String],
    payload: TypeVar,
) -> (Computation, PosId, TypeVar, PosId) {
    // Mirror `lower_lambda_params`: parameter outside, body slots inside a child level, then a
    // pure Fun value wrapper after restoring the enclosing level.
    let param = lowerer.fresh_type_var();
    let previous_level = lowerer.session.infer.enter_child_level();
    let body_value = lowerer.fresh_type_var();
    lowerer.constrain_exact_primitive(body_value, "unit");
    let body_effect = lowerer.fresh_type_var();
    let family_row = add_family_effect(lowerer, body_effect, family_path, payload);
    lowerer.session.infer.restore_level(previous_level);

    let param_def = lowerer.session.poly.defs.fresh();
    lowerer.session.poly.defs.set(param_def, Def::Arg);
    let pat = lowerer.session.poly.add_pat(Pat::Var(param_def));
    let body_expr = lowerer.session.poly.add_expr(Expr::Lit(Lit::Unit));
    let value = lowerer.fresh_type_var();
    let effect = lowerer.fresh_exact_pure_effect();
    let arg = lowerer.alloc_neg(Neg::Var(param));
    let arg_eff = lowerer.never_neg();
    let ret_eff = lowerer.alloc_pos(Pos::Var(body_effect));
    let ret = lowerer.alloc_pos(Pos::Var(body_value));
    lowerer.constrain_lower(
        value,
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        },
    );
    let callback_fun = function_lower_bound(lowerer, value);
    let expr = lowerer.session.poly.add_expr(Expr::Lambda(pat, body_expr));
    (
        Computation::value(expr, value, effect),
        callback_fun,
        body_effect,
        family_row,
    )
}

fn add_family_effect(
    lowerer: &mut ExprLowerer<'_>,
    effect: TypeVar,
    family_path: &[String],
    payload: TypeVar,
) -> PosId {
    let payload_lower = lowerer.alloc_pos(Pos::Var(payload));
    let payload_upper = lowerer.alloc_neg(Neg::Var(payload));
    let payload = lowerer
        .session
        .infer
        .alloc_neu(Neu::Bounds(payload_lower, payload_upper));
    let family = lowerer.alloc_pos(Pos::Con(family_path.to_vec(), vec![payload]));
    let row = lowerer.alloc_pos(Pos::Row(vec![family]));
    let upper = lowerer.alloc_neg(Neg::Var(effect));
    lowerer
        .session
        .infer
        .subtype(row, upper, OriginId::unknown_internal());
    row
}

fn function_lower_bound(lowerer: &ExprLowerer<'_>, value: TypeVar) -> PosId {
    lowerer
        .session
        .infer
        .constraints()
        .bounds()
        .of(value)
        .and_then(|bounds| {
            bounds.lowers().iter().find_map(|bound| {
                matches!(
                    lowerer.session.infer.constraints().types().pos(bound.pos),
                    Pos::Fun { .. }
                )
                .then_some(bound.pos)
            })
        })
        .expect("function lower bound")
}

fn var_reaches_family(
    machine: &crate::constraints::ConstraintMachine,
    root: TypeVar,
    family_path: &[String],
) -> bool {
    let mut pending = vec![root];
    let mut visited = rustc_hash::FxHashSet::default();
    while let Some(var) = pending.pop() {
        if !visited.insert(var) {
            continue;
        }
        let Some(bounds) = machine.bounds().of(var) else {
            continue;
        };
        for lower in bounds.lowers() {
            match machine.types().pos(lower.pos) {
                Pos::Con(path, _) if path == family_path => return true,
                Pos::Row(items)
                    if items.iter().any(|item| {
                        matches!(machine.types().pos(*item), Pos::Con(path, _) if path == family_path)
                    }) =>
                {
                    return true;
                }
                Pos::Var(next) => pending.push(*next),
                _ => {}
            }
        }
    }
    false
}

fn family_lower_path(
    machine: &crate::constraints::ConstraintMachine,
    root: TypeVar,
    family_path: &[String],
) -> Vec<String> {
    let mut pending = std::collections::VecDeque::from([(root, Vec::new())]);
    let mut visited = rustc_hash::FxHashSet::default();
    while let Some((var, path)) = pending.pop_front() {
        if !visited.insert(var) {
            continue;
        }
        let Some(bounds) = machine.bounds().of(var) else {
            continue;
        };
        for lower in bounds.lowers() {
            let node = machine.types().pos(lower.pos);
            let mut next_path = path.clone();
            next_path.push(format!("{var:?} <- {:?} {node:?}", lower.pos));
            match node {
                Pos::Con(found, _) if found == family_path => return next_path,
                Pos::Row(items)
                    if items.iter().any(|item| {
                        matches!(
                            machine.types().pos(*item),
                            Pos::Con(found, _) if found == family_path
                        )
                    }) =>
                {
                    let family_item = items
                        .iter()
                        .find_map(|item| match machine.types().pos(*item) {
                            Pos::Con(found, args) if found == family_path => {
                                Some(format!("{:?} {} {args:?}", item, found.join("::")))
                            }
                            _ => None,
                        })
                        .expect("matching family row item");
                    next_path.push(family_item);
                    return next_path;
                }
                Pos::Var(next) => pending.push_back((*next, next_path)),
                _ => {}
            }
        }
    }
    Vec::new()
}

fn multi_statement_single_boundary_fixture() -> (
    BodyLowering,
    MultiStatementBoundarySnapshot,
    MultiStatementBoundarySnapshot,
    MultiStatementBoundarySnapshot,
    MultiStatementBoundarySnapshot,
    MultiStatementBoundaryTrace,
    MultiStatementBoundaryTrace,
    MultiStatementBoundaryTrace,
    MultiStatementBoundaryTrace,
    DefId,
) {
    let root = parse(multi_statement_single_boundary_fixture_source());
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let std = lower.modules.module_decls(root_module, &Name("std".into()))[0].module;
    let control = lower.modules.module_decls(std, &Name("control".into()))[0].module;
    let var = lower.modules.module_decls(control, &Name("var".into()))[0].module;
    let act = lower.modules.type_decls(var, &Name("single_var".into()))[0].id;
    let family_path = lower
        .modules
        .type_decl_by_id(act)
        .map(|decl| {
            lower
                .modules
                .type_decl_path(&decl)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect::<Vec<_>>()
        })
        .expect("single-boundary act path");
    let companion = lower
        .modules
        .type_companion(act)
        .expect("single-boundary act companion");
    let helper = lower
        .modules
        .value_decls(companion, &Name("with_ref".into()))[0]
        .def;
    let parsed_def = lower
        .modules
        .value_decls(companion, &Name("parsed_enclosing".into()))[0]
        .def;

    let mut lowerer = crate::lowering::body::BodyLowerer::new(lower);
    lowerer.lower_block(&root, root_module);
    let parsed_boundary =
        recover_parsed_second_application_snapshot(&lowerer.session, parsed_def, helper);
    let parsed_calls =
        selection_application_effects(&lowerer.session, parsed_boundary.callback_expr, "get");
    let [parsed_first, parsed_second, parsed_tail] = parsed_calls.as_slice() else {
        panic!(
            "parsed callback must contain exactly three direct get applications: {parsed_calls:?}"
        );
    };
    let parsed = MultiStatementBoundarySnapshot {
        definition: HandBuiltNestedDefinition {
            def: parsed_def,
            root: lowerer
                .typing
                .def(parsed_def)
                .expect("parsed enclosing generalization root"),
            boundary: parsed_boundary,
            nested_call: None,
            queued_registration: None,
        },
        statement_effects: [*parsed_first, *parsed_second],
        tail_effect: *parsed_tail,
        aggregate_effect: parsed_boundary.callback_body_effect,
        callback_evaluation_effect: second_application_argument_effect(
            lowerer.session.infer.constraints(),
            parsed_boundary.helper_ref_value,
        ),
        first_application_effect: first_application_effect(
            lowerer.session.infer.constraints(),
            parsed_boundary.helper_ref_value,
        ),
    };
    let hand_built = lower_hand_built_multi_statement_definition(
        &mut lowerer,
        companion,
        helper,
        family_path.as_slice(),
        false,
        true,
    );
    let level_aligned = lower_hand_built_multi_statement_definition(
        &mut lowerer,
        companion,
        helper,
        family_path.as_slice(),
        true,
        true,
    );
    let deferred_reference = lower_hand_built_multi_statement_definition(
        &mut lowerer,
        companion,
        helper,
        family_path.as_slice(),
        true,
        false,
    );

    let pre_parsed =
        multi_statement_boundary_trace(&lowerer.session, parsed, family_path.as_slice());
    let pre_hand_built =
        multi_statement_boundary_trace(&lowerer.session, hand_built, family_path.as_slice());
    let pre_level_aligned =
        multi_statement_boundary_trace(&lowerer.session, level_aligned, family_path.as_slice());
    let pre_deferred_reference = multi_statement_boundary_trace(
        &lowerer.session,
        deferred_reference,
        family_path.as_slice(),
    );
    lowerer.drain_analysis_with_conformance();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    let output = lowerer.finish();
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    (
        output,
        parsed,
        hand_built,
        level_aligned,
        deferred_reference,
        pre_parsed,
        pre_hand_built,
        pre_level_aligned,
        pre_deferred_reference,
        helper,
    )
}

fn lower_hand_built_multi_statement_definition(
    body_lowerer: &mut crate::lowering::body::BodyLowerer,
    module: ModuleId,
    helper: DefId,
    family_path: &[String],
    align_enclosing_body_level: bool,
    preconstrain_reference: bool,
) -> MultiStatementBoundarySnapshot {
    let def = body_lowerer.session.poly.defs.fresh();
    body_lowerer.session.poly.defs.set(
        def,
        Def::Let {
            vis: Vis::My,
            scheme: None,
            body: None,
            children: Vec::new(),
        },
    );
    let previous_level = body_lowerer.session.infer.enter_child_level();
    let root = body_lowerer.session.infer.fresh_type_var();
    body_lowerer.typing.set_def(def, root);
    let queued_registration = DefinitionRegistration {
        queue_index: body_lowerer.session.work().len(),
        root,
    };
    body_lowerer
        .session
        .enqueue(AnalysisWork::Scc(SccInput::RegisterDef { def, root }));

    let (function, boundary, statement_effects, tail_effect, callback_effect, first_effect) = {
        let mut lowerer = ExprLowerer::new(
            &mut body_lowerer.session,
            &body_lowerer.modules,
            module,
            ModuleOrder::from_index(u32::MAX),
            def,
        );
        let init_value = lowerer.fresh_type_var();
        let enclosing_body_level =
            align_enclosing_body_level.then(|| lowerer.session.infer.enter_child_level());
        let init_expr = lowerer.session.poly.add_expr(Expr::Lit(Lit::Unit));
        let init = Computation::value(init_expr, init_value, lowerer.fresh_exact_pure_effect());
        let helper_ref = lowerer.lower_resolved_value_ref("with_ref".into(), helper);
        let helper_ref_value = helper_ref.value;
        let helper_with_init = lowerer.make_internal_app(helper_ref, init);
        let first_effect = helper_with_init.effect;

        // Reproduce normal lambda staging without asking `lower_lambda` to create an extra
        // witness Fun: bind the parameter outside, lower only the block at a child level, restore
        // the level, then build the production-style pure Fun around the aggregate slots.
        let callback_param = lowerer.fresh_type_var();
        if preconstrain_reference {
            constrain_hand_built_local_reference(
                &mut lowerer,
                callback_param,
                init_value,
                family_path,
            );
        }
        let before_callback_locals = lowerer.locals.len();
        let callback_pat = lowerer.bind_pattern_local(
            Name("r".into()),
            callback_param,
            None,
            LocalCallReturnEffect::Annotated,
        );
        lowerer
            .function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Anonymous));
        let callback_body_level = lowerer.session.infer.enter_child_level();
        let callback_root = parse(concat!(
            "my callback_body =\n",
            "  r.get()\n",
            "  r.get()\n",
            "  r.get()\n",
        ));
        let body = lowerer
            .lower_expr(&binding_expr(&callback_root, "callback_body"))
            .expect("hand-built callback body lowering");
        lowerer.session.infer.restore_level(callback_body_level);
        lowerer
            .function_frames
            .pop()
            .expect("hand-built callback frame must be balanced");
        lowerer.locals.truncate(before_callback_locals);
        let aggregate_effect = body.effect;
        let calls = selection_application_effects(lowerer.session, body.expr, "get");
        let [first_statement_effect, second_statement_effect, tail_effect] = calls.as_slice()
        else {
            panic!("hand-built callback must contain three get selections: {calls:?}");
        };
        let statement_effects = [*first_statement_effect, *second_statement_effect];
        let tail_effect = *tail_effect;
        let callback_value = lowerer.fresh_type_var();
        let callback_effect = lowerer.fresh_exact_pure_effect();
        let arg = lowerer.alloc_neg(Neg::Var(callback_param));
        let arg_eff = lowerer.never_neg();
        let ret_eff = lowerer.alloc_pos(Pos::Var(body.effect));
        let ret = lowerer.alloc_pos(Pos::Var(body.value));
        lowerer.constrain_lower(
            callback_value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        let callback_fun = function_lower_bound(&lowerer, callback_value);
        let callback_expr = lowerer
            .session
            .poly
            .add_expr(Expr::Lambda(callback_pat, body.expr));
        let callback = Computation::value(callback_expr, callback_value, callback_effect);

        let next = lowerer.session.infer.constraints().next_type_var();
        let result = lowerer.make_internal_app(helper_with_init, callback);
        assert_eq!(result.value, TypeVar(next));
        assert_eq!(result.effect, TypeVar(next + 1));
        let boundary = DeferredSecondApplicationSnapshot {
            helper_ref_value,
            init_value,
            callback_expr,
            callback_value,
            callback_fun,
            callback_body_effect: aggregate_effect,
            result_effect: result.effect,
            call_effect: TypeVar(next + 2),
        };

        if let Some(previous_level) = enclosing_body_level {
            lowerer.session.infer.restore_level(previous_level);
        }
        let param_def = lowerer.session.poly.defs.fresh();
        lowerer.session.poly.defs.set(param_def, Def::Arg);
        let pat = lowerer.session.poly.add_pat(Pat::Var(param_def));
        let function_value = lowerer.fresh_type_var();
        let function_effect = lowerer.fresh_exact_pure_effect();
        let arg = lowerer.alloc_neg(Neg::Var(init_value));
        let arg_eff = lowerer.never_neg();
        let ret_eff = lowerer.alloc_pos(Pos::Var(result.effect));
        let ret = lowerer.alloc_pos(Pos::Var(result.value));
        lowerer.constrain_lower(
            function_value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        let expr = lowerer
            .session
            .poly
            .add_expr(Expr::Lambda(pat, result.expr));
        (
            Computation::value(expr, function_value, function_effect),
            boundary,
            statement_effects,
            tail_effect,
            callback_effect,
            first_effect,
        )
    };

    let body_pos = body_lowerer
        .session
        .infer
        .alloc_pos(Pos::Var(function.value));
    let root_neg = body_lowerer.session.infer.alloc_neg(Neg::Var(root));
    body_lowerer
        .session
        .infer
        .subtype(body_pos, root_neg, OriginId::unknown_internal());
    let Some(Def::Let { body, .. }) = body_lowerer.session.poly.defs.get_mut(def) else {
        unreachable!()
    };
    *body = Some(function.expr);
    body_lowerer
        .session
        .record_binding_fetch(def, BindingFetch::from_evaluation(function.evaluation));
    body_lowerer
        .session
        .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
    body_lowerer.session.infer.restore_level(previous_level);

    MultiStatementBoundarySnapshot {
        definition: HandBuiltNestedDefinition {
            def,
            root,
            boundary,
            nested_call: None,
            queued_registration: Some(queued_registration),
        },
        statement_effects,
        tail_effect,
        aggregate_effect: boundary.callback_body_effect,
        callback_evaluation_effect: callback_effect,
        first_application_effect: first_effect,
    }
}

fn constrain_hand_built_local_reference(
    lowerer: &mut ExprLowerer<'_>,
    reference: TypeVar,
    payload: TypeVar,
    family_path: &[String],
) {
    let payload_arg = lowerer.invariant_var_arg(payload);
    let effect = lowerer.fresh_type_var();
    let lower_item = lowerer.alloc_pos(Pos::Con(family_path.to_vec(), vec![payload_arg]));
    let lower_row = lowerer.alloc_pos(Pos::Row(vec![lower_item]));
    let effect_upper = lowerer.alloc_neg(Neg::Var(effect));
    lowerer
        .session
        .infer
        .subtype(lower_row, effect_upper, OriginId::internal());
    let upper_item = lowerer.alloc_neg(Neg::Con(family_path.to_vec(), vec![payload_arg]));
    let upper_tail = lowerer.alloc_neg(Neg::Bot);
    let effect_lower = lowerer.alloc_pos(Pos::Var(effect));
    let upper_row = lowerer.alloc_neg(Neg::Row(vec![upper_item], upper_tail));
    lowerer
        .session
        .infer
        .subtype(effect_lower, upper_row, OriginId::internal());

    let effect_arg = lowerer.invariant_var_arg(effect);
    let args = vec![effect_arg, payload_arg];
    let reference_type = crate::std_paths::control_var_ref_type();
    let lower = lowerer.alloc_pos(Pos::Con(reference_type.clone(), args.clone()));
    let reference_upper = lowerer.alloc_neg(Neg::Var(reference));
    lowerer
        .session
        .infer
        .subtype(lower, reference_upper, OriginId::internal());
    let reference_lower = lowerer.alloc_pos(Pos::Var(reference));
    let upper = lowerer.alloc_neg(Neg::Con(reference_type, args));
    lowerer
        .session
        .infer
        .subtype(reference_lower, upper, OriginId::internal());
}

fn multi_statement_boundary_trace(
    session: &AnalysisSession,
    snapshot: MultiStatementBoundarySnapshot,
    family_path: &[String],
) -> MultiStatementBoundaryTrace {
    let machine = session.infer.constraints();
    let callback_ret_eff =
        function_return_effect_var(machine, snapshot.definition.boundary.callback_fun);
    MultiStatementBoundaryTrace {
        statement_effects: snapshot
            .statement_effects
            .into_iter()
            .map(|effect| effect_slot_trace(machine, effect, family_path))
            .collect(),
        tail_effect: effect_slot_trace(machine, snapshot.tail_effect, family_path),
        aggregate_effect: effect_slot_trace(machine, snapshot.aggregate_effect, family_path),
        callback_ret_eff,
        callback_evaluation_effect: effect_slot_trace(
            machine,
            snapshot.callback_evaluation_effect,
            family_path,
        ),
        first_application_effect: effect_slot_trace(
            machine,
            snapshot.first_application_effect,
            family_path,
        ),
        second_application_effect: effect_slot_trace(
            machine,
            snapshot.definition.boundary.result_effect,
            family_path,
        ),
    }
}

fn effect_slot_trace(
    machine: &crate::constraints::ConstraintMachine,
    var: TypeVar,
    family_path: &[String],
) -> EffectSlotTrace {
    let bounds = machine.bounds().of(var);
    let has_bottom_lower = bounds.is_some_and(|bounds| {
        bounds
            .lowers()
            .iter()
            .any(|bound| matches!(machine.types().pos(bound.pos), Pos::Bot))
    });
    let has_closed_empty_upper = bounds.is_some_and(|bounds| {
        bounds.uppers().iter().any(|bound| {
            matches!(
                machine.types().neg(bound.neg),
                Neg::Row(items, tail)
                    if items.is_empty() && matches!(machine.types().neg(*tail), Neg::Top)
            )
        })
    });
    let lower_nodes = bounds
        .map(|bounds| {
            bounds
                .lowers()
                .iter()
                .map(|bound| format!("{:?}", machine.types().pos(bound.pos)))
                .collect()
        })
        .unwrap_or_default();
    let upper_nodes = bounds
        .map(|bounds| {
            bounds
                .uppers()
                .iter()
                .map(|bound| format!("{:?}", machine.types().neg(bound.neg)))
                .collect()
        })
        .unwrap_or_default();
    let mut upper_var_closure = Vec::new();
    let mut pending = vec![var];
    let mut visited = rustc_hash::FxHashSet::default();
    while let Some(current) = pending.pop() {
        if !visited.insert(current) {
            continue;
        }
        let Some(current_bounds) = machine.bounds().of(current) else {
            upper_var_closure.push(format!(
                "{current:?}@{:?}/{:?} -> <no bounds>",
                machine.birth_level_of(current),
                machine.level_of(current),
            ));
            continue;
        };
        for upper in current_bounds.uppers() {
            let node = machine.types().neg(upper.neg);
            upper_var_closure.push(format!(
                "{current:?}@{:?}/{:?} -> {node:?}",
                machine.birth_level_of(current),
                machine.level_of(current),
            ));
            if let Neg::Var(next) = node {
                pending.push(*next);
            }
        }
    }
    EffectSlotTrace {
        var,
        level: machine.level_of(var),
        birth_level: machine.birth_level_of(var),
        has_family_lower: var_reaches_family(machine, var, family_path),
        has_bottom_lower,
        has_closed_empty_upper,
        lower_nodes,
        upper_nodes,
        upper_var_closure,
    }
}

fn semantic_multi_statement_trace(
    trace: &MultiStatementBoundaryTrace,
) -> SemanticMultiStatementBoundaryTrace {
    let semantic_effect = |effect: &EffectSlotTrace| SemanticEffectSlotTrace {
        level: effect.level,
        birth_level: effect.birth_level,
        has_family_lower: effect.has_family_lower,
        has_bottom_lower: effect.has_bottom_lower,
        has_closed_empty_upper: effect.has_closed_empty_upper,
    };
    SemanticMultiStatementBoundaryTrace {
        statement_effects: trace
            .statement_effects
            .iter()
            .map(semantic_effect)
            .collect(),
        tail_effect: semantic_effect(&trace.tail_effect),
        aggregate_effect: semantic_effect(&trace.aggregate_effect),
        callback_ret_eff_is_aggregate: trace.callback_ret_eff == trace.aggregate_effect.var,
        callback_evaluation_effect: semantic_effect(&trace.callback_evaluation_effect),
        first_application_effect: semantic_effect(&trace.first_application_effect),
        second_application_effect: semantic_effect(&trace.second_application_effect),
    }
}

fn first_application_effect(
    machine: &crate::constraints::ConstraintMachine,
    helper_ref_value: TypeVar,
) -> TypeVar {
    let first_upper = function_upper_bound(machine, helper_ref_value);
    let Neg::Fun { ret, .. } = machine.types().neg(first_upper) else {
        unreachable!()
    };
    let Neg::Var(result) = machine.types().neg(*ret) else {
        panic!("first application result must use its fresh value slot");
    };
    TypeVar(result.0 + 1)
}

fn second_application_argument_effect(
    machine: &crate::constraints::ConstraintMachine,
    helper_ref_value: TypeVar,
) -> TypeVar {
    let first_upper = function_upper_bound(machine, helper_ref_value);
    let Neg::Fun { ret, .. } = machine.types().neg(first_upper) else {
        unreachable!()
    };
    let Neg::Var(helper_with_init) = machine.types().neg(*ret) else {
        panic!("first application result must use its fresh value slot");
    };
    let second_upper = function_upper_bound(machine, *helper_with_init);
    let Neg::Fun { arg_eff, .. } = machine.types().neg(second_upper) else {
        unreachable!()
    };
    let Pos::Var(callback_effect) = machine.types().pos(*arg_eff) else {
        panic!("second application argument effect must preserve the callback evaluation slot");
    };
    *callback_effect
}

fn selection_application_effects(
    session: &AnalysisSession,
    expr: ExprId,
    selection_name: &str,
) -> Vec<TypeVar> {
    fn collect(
        session: &AnalysisSession,
        expr: ExprId,
        selection_name: &str,
        effects: &mut Vec<TypeVar>,
    ) {
        match session.poly.expr(expr) {
            Expr::App(callee, arg) => {
                if let Expr::Select(_, select) = session.poly.expr(*callee)
                    && session.poly.select(*select).name == selection_name
                {
                    let selected_value = session
                        .selections
                        .get(*select)
                        .map(|use_site| use_site.selected_value)
                        .or_else(|| {
                            session
                                .selections
                                .resolved(*select)
                                .map(|use_site| use_site.selected_value)
                        })
                        .expect("selection application selected-value slot");
                    let upper = function_upper_bound(session.infer.constraints(), selected_value);
                    let Neg::Fun { ret, .. } = session.infer.constraints().types().neg(upper)
                    else {
                        unreachable!()
                    };
                    let Neg::Var(result) = session.infer.constraints().types().neg(*ret) else {
                        panic!("selection application result must use a fresh value slot");
                    };
                    effects.push(TypeVar(result.0 + 1));
                }
                collect(session, *callee, selection_name, effects);
                collect(session, *arg, selection_name, effects);
            }
            Expr::RefSet(reference, value) => {
                collect(session, *reference, selection_name, effects);
                collect(session, *value, selection_name, effects);
            }
            Expr::Lambda(_, body) | Expr::Select(body, _) => {
                collect(session, *body, selection_name, effects);
            }
            Expr::Tuple(items) | Expr::PolyVariant(_, items) => {
                for item in items {
                    collect(session, *item, selection_name, effects);
                }
            }
            Expr::Record { fields, spread } => {
                for (_, value) in fields {
                    collect(session, *value, selection_name, effects);
                }
                match spread {
                    RecordSpread::None => {}
                    RecordSpread::Tail(value) | RecordSpread::Head(value) => {
                        collect(session, *value, selection_name, effects);
                    }
                }
            }
            Expr::Case(scrutinee, arms) => {
                collect(session, *scrutinee, selection_name, effects);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        collect(session, guard, selection_name, effects);
                    }
                    collect(session, arm.body, selection_name, effects);
                }
            }
            Expr::Catch(scrutinee, arms) => {
                collect(session, *scrutinee, selection_name, effects);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        collect(session, guard, selection_name, effects);
                    }
                    collect(session, arm.body, selection_name, effects);
                }
            }
            Expr::Block(statements, tail) => {
                for statement in statements {
                    match statement {
                        Stmt::Let(_, _, expr) | Stmt::Expr(expr) => {
                            collect(session, *expr, selection_name, effects);
                        }
                        Stmt::Module(_, statements) => {
                            for statement in statements {
                                if let Stmt::Let(_, _, expr) | Stmt::Expr(expr) = statement {
                                    collect(session, *expr, selection_name, effects);
                                }
                            }
                        }
                    }
                }
                if let Some(tail) = tail {
                    collect(session, *tail, selection_name, effects);
                }
            }
            Expr::Lit(_) | Expr::PrimitiveOp(_) | Expr::Var(_) => {}
        }
    }

    let mut effects = Vec::new();
    collect(session, expr, selection_name, &mut effects);
    effects
}

fn nested_deferred_resolution_fixture() -> (
    BodyLowering,
    HandBuiltNestedDefinition,
    HandBuiltNestedDefinition,
    HandBuiltNestedDefinition,
    HandBuiltNestedDefinition,
    HandBuiltNestedDefinition,
    HandBuiltNestedDefinition,
    HandBuiltNestedDefinition,
    HandBuiltNestedDefinition,
) {
    let root = parse(nested_deferred_resolution_fixture_source());
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let std = lower.modules.module_decls(root_module, &Name("std".into()))[0].module;
    let control = lower.modules.module_decls(std, &Name("control".into()))[0].module;
    let var = lower.modules.module_decls(control, &Name("var".into()))[0].module;
    let parsed_inner_act = lower.modules.type_decls(var, &Name("inner_var".into()))[0].id;
    let parsed_outer_act = lower.modules.type_decls(var, &Name("outer_var".into()))[0].id;
    let parsed_inner_companion = lower
        .modules
        .type_companion(parsed_inner_act)
        .expect("parsed inner companion");
    let parsed_outer_companion = lower
        .modules
        .type_companion(parsed_outer_act)
        .expect("parsed outer companion");
    let parsed_inner_helper = lower
        .modules
        .value_decls(parsed_inner_companion, &Name("with_ref".into()))[0]
        .def;
    let parsed_outer_helper = lower
        .modules
        .value_decls(parsed_outer_companion, &Name("with_ref".into()))[0]
        .def;
    let parsed_inner_def = lower
        .modules
        .value_decls(parsed_inner_companion, &Name("enclosing".into()))[0]
        .def;
    let parsed_outer_def = lower
        .modules
        .value_decls(parsed_outer_companion, &Name("enclosing".into()))[0]
        .def;
    let parsed_higher_inner_def = lower
        .modules
        .value_decls(parsed_inner_companion, &Name("higher_inner".into()))[0]
        .def;
    let parsed_higher_outer_def = lower
        .modules
        .value_decls(parsed_outer_companion, &Name("higher_outer".into()))[0]
        .def;

    let (inner_trigger, _) =
        binding_def_and_order(&lower.modules, root_module, "text_with_mock_trigger");
    let (outer_trigger, _) = binding_def_and_order(&lower.modules, root_module, "run_trigger");
    let inner_local_act = lower.modules.synthetic_var_act_uses(inner_trigger)[0].clone();
    let outer_local_act = lower.modules.synthetic_var_act_uses(outer_trigger)[0].clone();
    let inner_local_companion = lower
        .modules
        .type_companion(inner_local_act.act)
        .expect("inner synthetic local-var companion");
    let outer_local_companion = lower
        .modules
        .type_companion(outer_local_act.act)
        .expect("outer synthetic local-var companion");
    let hand_inner_helper = lower
        .modules
        .value_decls(inner_local_companion, &Name("with_ref".into()))[0]
        .def;
    let hand_outer_helper = lower
        .modules
        .value_decls(outer_local_companion, &Name("with_ref".into()))[0]
        .def;
    assert_ne!(
        inner_local_act.act, outer_local_act.act,
        "the hand-built nested pair must resolve each helper in its own synthetic act copy"
    );
    let hand_inner_family_path = lower
        .modules
        .type_decl_by_id(inner_local_act.act)
        .map(|decl| {
            lower
                .modules
                .type_decl_path(&decl)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect::<Vec<_>>()
        })
        .expect("hand-built inner family path");

    let mut lowerer = crate::lowering::body::BodyLowerer::new(lower);
    lowerer.lower_block(&root, root_module);
    lowerer.lower_synthetic_act_copy_bodies_for_test();

    let parsed_inner = HandBuiltNestedDefinition {
        def: parsed_inner_def,
        root: lowerer
            .typing
            .def(parsed_inner_def)
            .expect("parsed inner generalization root"),
        boundary: recover_parsed_second_application_snapshot(
            &lowerer.session,
            parsed_inner_def,
            parsed_inner_helper,
        ),
        nested_call: None,
        queued_registration: None,
    };
    let parsed_outer_boundary = recover_parsed_second_application_snapshot(
        &lowerer.session,
        parsed_outer_def,
        parsed_outer_helper,
    );
    let parsed_outer = HandBuiltNestedDefinition {
        def: parsed_outer_def,
        root: lowerer
            .typing
            .def(parsed_outer_def)
            .expect("parsed outer generalization root"),
        boundary: parsed_outer_boundary,
        nested_call: Some(recover_nested_application_snapshot(
            &lowerer.session,
            parsed_outer_boundary.callback_expr,
            parsed_inner_def,
        )),
        queued_registration: None,
    };
    let parsed_higher_inner = HandBuiltNestedDefinition {
        def: parsed_higher_inner_def,
        root: lowerer
            .typing
            .def(parsed_higher_inner_def)
            .expect("parsed higher-order inner generalization root"),
        boundary: recover_parsed_second_application_snapshot(
            &lowerer.session,
            parsed_higher_inner_def,
            parsed_inner_helper,
        ),
        nested_call: None,
        queued_registration: None,
    };
    let parsed_higher_outer_boundary = recover_parsed_second_application_snapshot(
        &lowerer.session,
        parsed_higher_outer_def,
        parsed_outer_helper,
    );
    let parsed_higher_outer = HandBuiltNestedDefinition {
        def: parsed_higher_outer_def,
        root: lowerer
            .typing
            .def(parsed_higher_outer_def)
            .expect("parsed higher-order outer generalization root"),
        boundary: parsed_higher_outer_boundary,
        nested_call: Some(recover_second_stage_nested_application_snapshot(
            &lowerer.session,
            parsed_higher_outer_boundary.callback_expr,
            parsed_higher_inner_def,
        )),
        queued_registration: None,
    };

    let hand_inner = lower_hand_built_nested_function(
        &mut lowerer,
        inner_local_companion,
        hand_inner_helper,
        None,
        concat!(
            "my callback = \\r ->\n",
            "  my before = r.get()\n",
            "  r.update (\\_ -> before)\n",
            "  std::control::var::observe::mark:r.get()\n",
        ),
    );
    let hand_outer = lower_hand_built_nested_function(
        &mut lowerer,
        outer_local_companion,
        hand_outer_helper,
        Some(hand_inner.def),
        concat!(
            "my callback = \\r ->\n",
            "  my before = r.get()\n",
            "  r.update (\\_ -> before)\n",
            "  std::control::var::observe::mark:r.get()\n",
        ),
    );
    let v5_inner = lower_v5_corrected_nested_function(
        &mut lowerer,
        inner_local_companion,
        hand_inner_helper,
        None,
        None,
    );
    let v5_outer = lower_v5_corrected_nested_function(
        &mut lowerer,
        outer_local_companion,
        hand_outer_helper,
        Some(v5_inner.def),
        Some(hand_inner_family_path.as_slice()),
    );

    lowerer.drain_analysis_with_conformance();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    let output = lowerer.finish();
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    (
        output,
        parsed_inner,
        parsed_outer,
        hand_inner,
        hand_outer,
        parsed_higher_inner,
        parsed_higher_outer,
        v5_inner,
        v5_outer,
    )
}

fn lower_v5_corrected_nested_function(
    body_lowerer: &mut crate::lowering::body::BodyLowerer,
    module: ModuleId,
    helper: DefId,
    nested_target: Option<DefId>,
    nested_family_path: Option<&[String]>,
) -> HandBuiltNestedDefinition {
    let def = body_lowerer.session.poly.defs.fresh();
    body_lowerer.session.poly.defs.set(
        def,
        Def::Let {
            vis: Vis::My,
            scheme: None,
            body: None,
            children: Vec::new(),
        },
    );
    let previous_level = body_lowerer.session.infer.enter_child_level();
    let root = body_lowerer.session.infer.fresh_type_var();
    body_lowerer.typing.set_def(def, root);
    let queued_registration = DefinitionRegistration {
        queue_index: body_lowerer.session.work().len(),
        root,
    };
    body_lowerer
        .session
        .enqueue(AnalysisWork::Scc(SccInput::RegisterDef { def, root }));

    let (function, boundary, nested_call) = {
        let mut lowerer = ExprLowerer::new(
            &mut body_lowerer.session,
            &body_lowerer.modules,
            module,
            ModuleOrder::from_index(u32::MAX),
            def,
        );
        let init_value = lowerer.fresh_type_var();
        let enclosing_body_level = lowerer.session.infer.enter_child_level();
        let before_function_locals = lowerer.locals.len();
        let higher_order_param = nested_target.is_none().then(|| {
            let value = lowerer.fresh_type_var();
            let pat = lowerer.bind_pattern_local(
                Name("f".into()),
                value,
                None,
                LocalCallReturnEffect::Annotated,
            );
            let body_level = lowerer.session.infer.enter_child_level();
            (value, pat, body_level)
        });
        let init_expr = lowerer.session.poly.add_expr(Expr::Lit(Lit::Unit));
        let init = Computation::value(init_expr, init_value, lowerer.fresh_exact_pure_effect());
        let helper_ref = lowerer.lower_resolved_value_ref("with_ref".into(), helper);
        let helper_ref_value = helper_ref.value;
        let helper_with_init = lowerer.make_internal_app(helper_ref, init);

        // v5 prepare: bind only a fresh placeholder. The helper application below is the first
        // connection from this parameter to concrete `ref [F(P)] P`.
        let callback_param = lowerer.fresh_type_var();
        let before_callback_locals = lowerer.locals.len();
        let callback_pat = lowerer.bind_pattern_local(
            Name("r".into()),
            callback_param,
            None,
            LocalCallReturnEffect::Annotated,
        );
        lowerer
            .function_frames
            .push(FunctionPredicateFrame::new(LambdaScope::Anonymous));
        let callback_body_level = lowerer.session.infer.enter_child_level();

        let (body, nested_call) = if let Some(nested_target) = nested_target {
            let first_root = parse("my item = r.get()\n");
            let first = lowerer
                .lower_expr(&binding_expr(&first_root, "item"))
                .expect("v5 outer callback leading statement");
            let backing_root = parse("my item = r.get()\n");
            let backing = lowerer
                .lower_expr(&binding_expr(&backing_root, "item"))
                .expect("v5 nested backing argument");
            let nested_ref = lowerer.lower_resolved_value_ref("v5_inner".into(), nested_target);
            let target_ref_value = nested_ref.value;
            let nested_with_backing = lowerer.make_internal_app(nested_ref, backing);
            let nested_callback_param = lowerer.fresh_type_var();
            constrain_hand_built_local_reference(
                &mut lowerer,
                nested_callback_param,
                init_value,
                nested_family_path.expect("nested call must identify the inner family"),
            );
            let before_nested_callback_locals = lowerer.locals.len();
            let nested_callback_pat = lowerer.bind_pattern_local(
                Name("inner_r".into()),
                nested_callback_param,
                None,
                LocalCallReturnEffect::Annotated,
            );
            lowerer
                .function_frames
                .push(FunctionPredicateFrame::new(LambdaScope::Anonymous));
            let nested_callback_level = lowerer.session.infer.enter_child_level();
            let callback_root = parse(concat!(
                "my callback_body =\n",
                "  my before = inner_r.get()\n",
                "  inner_r.update (\\_ -> before)\n",
                "  std::control::var::observe::mark:inner_r.get()\n",
            ));
            let nested_callback_body = lowerer
                .lower_expr(&binding_expr(&callback_root, "callback_body"))
                .expect("v5 nested higher-order callback body");
            lowerer.session.infer.restore_level(nested_callback_level);
            lowerer
                .function_frames
                .pop()
                .expect("nested callback frame must be balanced");
            lowerer.locals.truncate(before_nested_callback_locals);
            let nested_callback_value = lowerer.fresh_type_var();
            let nested_callback_effect = lowerer.fresh_exact_pure_effect();
            let arg = lowerer.alloc_neg(Neg::Var(nested_callback_param));
            let arg_eff = lowerer.never_neg();
            let ret_eff = lowerer.alloc_pos(Pos::Var(nested_callback_body.effect));
            let ret = lowerer.alloc_pos(Pos::Var(nested_callback_body.value));
            lowerer.constrain_lower(
                nested_callback_value,
                Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                },
            );
            let nested_callback_expr = lowerer
                .session
                .poly
                .add_expr(Expr::Lambda(nested_callback_pat, nested_callback_body.expr));
            let nested_callback = Computation::value(
                nested_callback_expr,
                nested_callback_value,
                nested_callback_effect,
            );
            let callee_ref_value = nested_with_backing.value;
            let next = lowerer.session.infer.constraints().next_type_var();
            let nested_result = lowerer.make_internal_app(nested_with_backing, nested_callback);
            assert_eq!(nested_result.value, TypeVar(next));
            assert_eq!(nested_result.effect, TypeVar(next + 1));
            let nested_call = DeferredNestedApplicationSnapshot {
                target_ref_value,
                callee_ref_value,
                argument_value: nested_callback.value,
                argument_effect: nested_callback.effect,
                result_value: TypeVar(next),
                result_effect: TypeVar(next + 1),
                call_effect: TypeVar(next + 2),
            };
            let first_stmt = LoweredLocalStmt {
                stmt: Stmt::Expr(first.expr),
                effect: first.effect,
            };
            (
                lowerer.prepend_block(first_stmt, nested_result),
                Some(nested_call),
            )
        } else {
            let callback_ref = lowerer
                .lower_name(Name("f".into()))
                .expect("v5 inner higher-order callback reference");
            let local_ref = lowerer
                .lower_name(Name("r".into()))
                .expect("v5 inner local-ref callback parameter");
            let user_result = lowerer.make_internal_app(callback_ref, local_ref);
            let read_root = parse("my item = r.get()\n");
            let read = lowerer
                .lower_expr(&binding_expr(&read_root, "item"))
                .expect("v5 inner final local-ref read");
            (lowerer.synthetic_tuple_value(vec![user_result, read]), None)
        };

        lowerer.session.infer.restore_level(callback_body_level);
        lowerer
            .function_frames
            .pop()
            .expect("v5 callback frame must be balanced");
        lowerer.locals.truncate(before_callback_locals);

        let callback_value = lowerer.fresh_type_var();
        let callback_effect = lowerer.fresh_exact_pure_effect();
        let arg = lowerer.alloc_neg(Neg::Var(callback_param));
        let arg_eff = lowerer.never_neg();
        let ret_eff = lowerer.alloc_pos(Pos::Var(body.effect));
        let ret = lowerer.alloc_pos(Pos::Var(body.value));
        lowerer.constrain_lower(
            callback_value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        let callback_fun = function_lower_bound(&lowerer, callback_value);
        let callback_expr = lowerer
            .session
            .poly
            .add_expr(Expr::Lambda(callback_pat, body.expr));
        let callback = Computation::value(callback_expr, callback_value, callback_effect);

        let next = lowerer.session.infer.constraints().next_type_var();
        let result = lowerer.make_internal_app(helper_with_init, callback);
        assert_eq!(result.value, TypeVar(next));
        assert_eq!(result.effect, TypeVar(next + 1));
        let boundary = DeferredSecondApplicationSnapshot {
            helper_ref_value,
            init_value,
            callback_expr,
            callback_value,
            callback_fun,
            callback_body_effect: body.effect,
            result_effect: result.effect,
            call_effect: TypeVar(next + 2),
        };

        let function_body =
            if let Some((higher_order_value, higher_order_pat, body_level)) = higher_order_param {
                lowerer.session.infer.restore_level(body_level);
                let value = lowerer.fresh_type_var();
                let effect = lowerer.fresh_exact_pure_effect();
                let arg = lowerer.alloc_neg(Neg::Var(higher_order_value));
                let arg_eff = lowerer.never_neg();
                let ret_eff = lowerer.alloc_pos(Pos::Var(result.effect));
                let ret = lowerer.alloc_pos(Pos::Var(result.value));
                lowerer.constrain_lower(
                    value,
                    Pos::Fun {
                        arg,
                        arg_eff,
                        ret_eff,
                        ret,
                    },
                );
                let expr = lowerer
                    .session
                    .poly
                    .add_expr(Expr::Lambda(higher_order_pat, result.expr));
                lowerer.locals.truncate(before_function_locals);
                Computation::value(expr, value, effect)
            } else {
                result
            };
        lowerer.session.infer.restore_level(enclosing_body_level);
        let param_def = lowerer.session.poly.defs.fresh();
        lowerer.session.poly.defs.set(param_def, Def::Arg);
        let pat = lowerer.session.poly.add_pat(Pat::Var(param_def));
        let function_value = lowerer.fresh_type_var();
        let function_effect = lowerer.fresh_exact_pure_effect();
        let arg = lowerer.alloc_neg(Neg::Var(init_value));
        let arg_eff = lowerer.never_neg();
        let ret_eff = lowerer.alloc_pos(Pos::Var(function_body.effect));
        let ret = lowerer.alloc_pos(Pos::Var(function_body.value));
        lowerer.constrain_lower(
            function_value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        let expr = lowerer
            .session
            .poly
            .add_expr(Expr::Lambda(pat, function_body.expr));
        (
            Computation::value(expr, function_value, function_effect),
            boundary,
            nested_call,
        )
    };

    let body_pos = body_lowerer
        .session
        .infer
        .alloc_pos(Pos::Var(function.value));
    let root_neg = body_lowerer.session.infer.alloc_neg(Neg::Var(root));
    body_lowerer
        .session
        .infer
        .subtype(body_pos, root_neg, OriginId::unknown_internal());
    let Some(Def::Let { body, .. }) = body_lowerer.session.poly.defs.get_mut(def) else {
        unreachable!()
    };
    *body = Some(function.expr);
    body_lowerer
        .session
        .record_binding_fetch(def, BindingFetch::from_evaluation(function.evaluation));
    body_lowerer
        .session
        .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
    body_lowerer.session.infer.restore_level(previous_level);

    HandBuiltNestedDefinition {
        def,
        root,
        boundary,
        nested_call,
        queued_registration: Some(queued_registration),
    }
}

fn lower_hand_built_nested_function(
    body_lowerer: &mut crate::lowering::body::BodyLowerer,
    module: ModuleId,
    helper: DefId,
    nested_target: Option<DefId>,
    callback_source: &str,
) -> HandBuiltNestedDefinition {
    let def = body_lowerer.session.poly.defs.fresh();
    body_lowerer.session.poly.defs.set(
        def,
        Def::Let {
            vis: Vis::My,
            scheme: None,
            body: None,
            children: Vec::new(),
        },
    );
    let previous_level = body_lowerer.session.infer.enter_child_level();
    let root = body_lowerer.session.infer.fresh_type_var();
    body_lowerer.typing.set_def(def, root);
    let queued_registration = DefinitionRegistration {
        queue_index: body_lowerer.session.work().len(),
        root,
    };
    body_lowerer
        .session
        .enqueue(AnalysisWork::Scc(SccInput::RegisterDef { def, root }));
    assert!(matches!(
        body_lowerer.session.work().get(queued_registration.queue_index),
        Some(AnalysisWork::Scc(SccInput::RegisterDef {
            def: registered,
            root: registered_root,
        })) if *registered == def && *registered_root == root
    ));

    let (function, boundary, nested_call) = {
        let mut lowerer = ExprLowerer::new(
            &mut body_lowerer.session,
            &body_lowerer.modules,
            module,
            ModuleOrder::from_index(u32::MAX),
            def,
        );
        let init_value = lowerer.fresh_type_var();
        let init_expr = lowerer.session.poly.add_expr(Expr::Lit(Lit::Unit));
        let init = Computation::value(init_expr, init_value, lowerer.fresh_exact_pure_effect());
        let helper_ref = lowerer.lower_resolved_value_ref("with_ref".into(), helper);
        let helper_ref_value = helper_ref.value;
        let helper_with_init = lowerer.make_internal_app(helper_ref, init);

        let callback_root = parse(callback_source);
        let callback = lowerer
            .lower_expr(&binding_expr(&callback_root, "callback"))
            .expect("nested hand-built callback lowering");
        let (callback, nested_call) = if let Some(nested_target) = nested_target {
            let (callback, nested_call) =
                wrap_callback_body_in_nested_call(&mut lowerer, callback, nested_target);
            (callback, Some(nested_call))
        } else {
            (callback, None)
        };
        let callback_fun = function_lower_bound(&lowerer, callback.value);
        let callback_body_effect =
            function_return_effect_var(lowerer.session.infer.constraints(), callback_fun);
        let next = lowerer.session.infer.constraints().next_type_var();
        let result = lowerer.make_internal_app(helper_with_init, callback);
        assert_eq!(result.value, TypeVar(next));
        assert_eq!(result.effect, TypeVar(next + 1));
        let boundary = DeferredSecondApplicationSnapshot {
            helper_ref_value,
            init_value,
            callback_expr: callback.expr,
            callback_value: callback.value,
            callback_fun,
            callback_body_effect,
            result_effect: result.effect,
            call_effect: TypeVar(next + 2),
        };

        let param_def = lowerer.session.poly.defs.fresh();
        lowerer.session.poly.defs.set(param_def, Def::Arg);
        let pat = lowerer.session.poly.add_pat(Pat::Var(param_def));
        let function_value = lowerer.fresh_type_var();
        let function_effect = lowerer.fresh_exact_pure_effect();
        let arg = lowerer.alloc_neg(Neg::Var(init_value));
        let arg_eff = lowerer.never_neg();
        let ret_eff = lowerer.alloc_pos(Pos::Var(result.effect));
        let ret = lowerer.alloc_pos(Pos::Var(result.value));
        lowerer.constrain_lower(
            function_value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        let expr = lowerer
            .session
            .poly
            .add_expr(Expr::Lambda(pat, result.expr));
        (
            Computation::value(expr, function_value, function_effect),
            boundary,
            nested_call,
        )
    };

    let body_pos = body_lowerer
        .session
        .infer
        .alloc_pos(Pos::Var(function.value));
    let root_neg = body_lowerer.session.infer.alloc_neg(Neg::Var(root));
    body_lowerer
        .session
        .infer
        .subtype(body_pos, root_neg, OriginId::unknown_internal());
    let Some(Def::Let { body, .. }) = body_lowerer.session.poly.defs.get_mut(def) else {
        unreachable!()
    };
    *body = Some(function.expr);
    body_lowerer
        .session
        .record_binding_fetch(def, BindingFetch::from_evaluation(function.evaluation));
    body_lowerer
        .session
        .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
    body_lowerer.session.infer.restore_level(previous_level);
    HandBuiltNestedDefinition {
        def,
        root,
        boundary,
        nested_call,
        queued_registration: Some(queued_registration),
    }
}

fn wrap_callback_body_in_nested_call(
    lowerer: &mut ExprLowerer<'_>,
    callback: Computation,
    nested_target: DefId,
) -> (Computation, DeferredNestedApplicationSnapshot) {
    let callback_fun = function_lower_bound(lowerer, callback.value);
    let (arg, arg_eff, body_effect, body_value) = match lowerer
        .session
        .infer
        .constraints()
        .types()
        .pos(callback_fun)
    {
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            let Pos::Var(body_effect) = lowerer.session.infer.constraints().types().pos(*ret_eff)
            else {
                panic!("nested callback body effect must use a variable slot");
            };
            let Pos::Var(body_value) = lowerer.session.infer.constraints().types().pos(*ret) else {
                panic!("nested callback body value must use a variable slot");
            };
            (*arg, *arg_eff, *body_effect, *body_value)
        }
        _ => unreachable!(),
    };
    let (pat, body) = match lowerer.session.poly.expr(callback.expr) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("nested callback must be a lambda"),
    };
    let nested_arg = Computation::computation(body, body_value, body_effect);
    let previous_level = lowerer.session.infer.enter_child_level();
    let nested_ref = lowerer.lower_resolved_value_ref("text_with_mock".into(), nested_target);
    let callee_ref_value = nested_ref.value;
    let Expr::Var(nested_ref_id) = lowerer.session.poly.expr(nested_ref.expr) else {
        unreachable!()
    };
    assert_eq!(lowerer.session.poly.ref_target(*nested_ref_id), None);
    assert!(lowerer.session.work().iter().any(|work| matches!(
        work,
        AnalysisWork::ApplyRefResolution { ref_id, target }
            if *ref_id == *nested_ref_id && *target == nested_target
    )));
    let next = lowerer.session.infer.constraints().next_type_var();
    let nested_result = lowerer.make_internal_app(nested_ref, nested_arg);
    assert_eq!(nested_result.value, TypeVar(next));
    assert_eq!(nested_result.effect, TypeVar(next + 1));
    let nested_call = DeferredNestedApplicationSnapshot {
        target_ref_value: callee_ref_value,
        callee_ref_value,
        argument_value: nested_arg.value,
        argument_effect: nested_arg.effect,
        result_value: nested_result.value,
        result_effect: nested_result.effect,
        call_effect: TypeVar(next + 2),
    };
    lowerer.session.infer.restore_level(previous_level);

    let value = lowerer.fresh_type_var();
    let effect = lowerer.fresh_exact_pure_effect();
    let ret_eff = lowerer.alloc_pos(Pos::Var(nested_result.effect));
    let ret = lowerer.alloc_pos(Pos::Var(nested_result.value));
    lowerer.constrain_lower(
        value,
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        },
    );
    let expr = lowerer
        .session
        .poly
        .add_expr(Expr::Lambda(pat, nested_result.expr));
    (Computation::value(expr, value, effect), nested_call)
}

fn assert_hand_registration_root(definition: HandBuiltNestedDefinition) {
    let registration = definition
        .queued_registration
        .expect("hand-built definition registration trace");
    assert_eq!(registration.root, definition.root);
}

fn assert_inner_generalized_before_outer_use(
    events: &[SccEvent],
    inner: HandBuiltNestedDefinition,
    outer: HandBuiltNestedDefinition,
) {
    let nested_ref_value = outer
        .nested_call
        .expect("outer definition must retain its nested call")
        .target_ref_value;
    let inner_quantify = events
        .iter()
        .position(|event| {
            matches!(
                event,
                SccEvent::QuantifyComponent { component, roots }
                    if component == &vec![inner.def] && roots == &vec![inner.root]
            )
        })
        .expect("inner definition must quantify as its own component");
    let instantiate = events
        .iter()
        .position(|event| {
            matches!(
                event,
                SccEvent::InstantiateUse {
                    parent,
                    target,
                    use_value,
                } if *parent == outer.def
                    && *target == inner.def
                    && *use_value == nested_ref_value
            )
        })
        .expect("the outer nested-ref slot must instantiate the finalized inner scheme");
    let outer_quantify = events
        .iter()
        .position(|event| {
            matches!(
                event,
                SccEvent::QuantifyComponent { component, roots }
                    if component == &vec![outer.def] && roots == &vec![outer.root]
            )
        })
        .expect("outer definition must quantify as its own component");
    assert!(
        inner_quantify < instantiate && instantiate < outer_quantify,
        "inner must finalize before the outer deferred use instantiates it: \
         inner={inner_quantify}, instantiate={instantiate}, outer={outer_quantify}"
    );
    assert!(
        !events.iter().any(|event| matches!(
            event,
            SccEvent::MergeComponents { merged, .. }
                if merged.contains(&inner.def) && merged.contains(&outer.def)
        )),
        "the acyclic nested definitions must not merge into one SCC"
    );
}

fn resolved_snapshot_family_path(
    output: &BodyLowering,
    snapshot: DeferredSecondApplicationSnapshot,
) -> Vec<String> {
    let machine = output.session.infer.constraints();
    let helper = function_lower_bound_in_machine(machine, snapshot.helper_ref_value);
    let Pos::Fun { ret, .. } = machine.types().pos(helper) else {
        unreachable!()
    };
    let Pos::Fun {
        arg: expected_callback,
        ..
    } = machine.types().pos(*ret)
    else {
        panic!("resolved helper must expose its callback argument");
    };
    let Neg::Fun { ret_eff, .. } = machine.types().neg(*expected_callback) else {
        panic!("resolved helper callback argument must be callable");
    };
    expected_family_path(machine.types(), *ret_eff)
}

fn deferred_resolution_fixture() -> (
    BodyLowering,
    DeferredSecondApplicationSnapshot,
    DeferredSecondApplicationSnapshot,
) {
    let root = parse(deferred_resolution_fixture_source());
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let (trigger, _) = binding_def_and_order(&lower.modules, root_module, "trigger");
    let local_var_act = lower.modules.synthetic_var_act_uses(trigger)[0].clone();
    let companion = lower
        .modules
        .type_companion(local_var_act.act)
        .expect("synthetic var act companion");
    let helper = lower
        .modules
        .value_decls(companion, &Name("with_ref".into()))[0]
        .def;
    let enclosing = lower
        .modules
        .value_decls(companion, &Name("enclosing".into()))[0]
        .def;
    let mut lowerer = crate::lowering::body::BodyLowerer::new(lower);
    lowerer.lower_block(&root, root_module);
    lowerer.lower_synthetic_act_copy_bodies_for_test();

    // Match `lower_binding_bodies`: snapshot after body construction, add the hand-built control,
    // then use the ordinary analysis/conformance and remaining-selection drains.
    let parsed = recover_parsed_second_application_snapshot(&lowerer.session, enclosing, helper);
    let hand_built = lower_hand_built_second_application(&mut lowerer, companion, helper, parsed);

    lowerer.drain_analysis_with_conformance();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    let output = lowerer.finish();
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    (output, parsed, hand_built)
}

fn recover_parsed_second_application_snapshot(
    session: &AnalysisSession,
    enclosing: DefId,
    helper: DefId,
) -> DeferredSecondApplicationSnapshot {
    let mut enclosing_body = match session.poly.defs.get(enclosing) {
        Some(Def::Let {
            body: Some(body), ..
        }) => *body,
        _ => panic!("parsed enclosing witness must have a lowered body"),
    };
    let mut parameter_count = 0;
    while let Expr::Lambda(_, body) = session.poly.expr(enclosing_body) {
        enclosing_body = *body;
        parameter_count += 1;
    }
    assert!(
        parameter_count > 0,
        "parsed enclosing witness must lower at least its init parameter as a lambda"
    );
    let Expr::App(helper_with_init, callback_expr) = session.poly.expr(enclosing_body) else {
        panic!("parsed enclosing body must apply helper to callback second");
    };
    let Expr::App(helper_ref_expr, _) = session.poly.expr(*helper_with_init) else {
        panic!("parsed enclosing body must apply helper to init first");
    };
    let helper_ref = expr_ref(session, *helper_ref_expr);
    let helper_ref_value = session
        .refs
        .value(helper_ref)
        .expect("helper ref value slot");
    assert!(
        session.poly.ref_target(helper_ref) == Some(helper)
            || session.work().iter().any(|work| matches!(
                work,
                AnalysisWork::ApplyRefResolution { ref_id, target }
                    if *ref_id == helper_ref && *target == helper
            )),
        "the parsed witness must retain either its deferred ApplyRefResolution or its completed \
         resolution"
    );

    let init_value = application_argument_value(session.infer.constraints(), helper_ref_value, 1);
    let callback_value =
        application_argument_value(session.infer.constraints(), helper_ref_value, 2);
    let callback_fun = function_lower_bound_in_machine(session.infer.constraints(), callback_value);
    let callback_body_effect =
        function_return_effect_var(session.infer.constraints(), callback_fun);
    let (result_effect, call_effect) =
        second_application_effect_slots(session.infer.constraints(), helper_ref_value);
    assert!(matches!(
        session.poly.expr(*callback_expr),
        Expr::Lambda(_, _)
    ));

    DeferredSecondApplicationSnapshot {
        helper_ref_value,
        init_value,
        callback_expr: *callback_expr,
        callback_value,
        callback_fun,
        callback_body_effect,
        result_effect,
        call_effect,
    }
}

fn recover_nested_application_snapshot(
    session: &AnalysisSession,
    callback_expr: ExprId,
    nested_target: DefId,
) -> DeferredNestedApplicationSnapshot {
    let nested_application = find_call_to_target(session, callback_expr, nested_target)
        .expect("parsed outer callback must call the parsed inner definition");
    let Expr::App(callee_expr, _) = session.poly.expr(nested_application) else {
        unreachable!()
    };
    let nested_ref = expr_ref(session, *callee_expr);
    assert!(
        session.poly.ref_target(nested_ref) == Some(nested_target)
            || session.work().iter().any(|work| matches!(
                work,
                AnalysisWork::ApplyRefResolution { ref_id, target }
                    if *ref_id == nested_ref && *target == nested_target
            )),
        "the parsed nested call must retain either its deferred ApplyRefResolution or its \
         completed resolution"
    );
    let callee_ref_value = session
        .refs
        .value(nested_ref)
        .expect("nested ref value slot");
    let application = function_upper_bound(session.infer.constraints(), callee_ref_value);
    let Neg::Fun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    } = session.infer.constraints().types().neg(application)
    else {
        unreachable!()
    };
    let Pos::Var(argument_value) = session.infer.constraints().types().pos(*arg) else {
        panic!("nested application argument value must use its computation slot");
    };
    let Pos::Var(argument_effect) = session.infer.constraints().types().pos(*arg_eff) else {
        panic!("nested application argument effect must use its computation slot");
    };
    let Neg::Var(call_effect) = session.infer.constraints().types().neg(*ret_eff) else {
        panic!("nested application call effect must use its fresh deferred slot");
    };
    let Neg::Var(result_value) = session.infer.constraints().types().neg(*ret) else {
        panic!("nested application result value must use its fresh slot");
    };

    DeferredNestedApplicationSnapshot {
        target_ref_value: callee_ref_value,
        callee_ref_value,
        argument_value: *argument_value,
        argument_effect: *argument_effect,
        result_value: *result_value,
        // `make_app_with_origins` allocates result value, result effect, and call effect in order.
        result_effect: TypeVar(result_value.0 + 1),
        call_effect: *call_effect,
    }
}

fn recover_second_stage_nested_application_snapshot(
    session: &AnalysisSession,
    callback_expr: ExprId,
    nested_target: DefId,
) -> DeferredNestedApplicationSnapshot {
    let first_application = find_call_to_target(session, callback_expr, nested_target)
        .expect("parsed outer callback must call the higher-order inner definition");
    let Expr::App(callee_expr, _) = session.poly.expr(first_application) else {
        unreachable!()
    };
    let nested_ref = expr_ref(session, *callee_expr);
    let target_ref_value = session
        .refs
        .value(nested_ref)
        .expect("higher-order nested ref value slot");
    let first_upper = function_upper_bound(session.infer.constraints(), target_ref_value);
    let Neg::Fun { ret, .. } = session.infer.constraints().types().neg(first_upper) else {
        unreachable!()
    };
    let Neg::Var(callee_ref_value) = session.infer.constraints().types().neg(*ret) else {
        panic!("higher-order first application must preserve its result slot");
    };
    let second_upper = function_upper_bound(session.infer.constraints(), *callee_ref_value);
    let Neg::Fun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    } = session.infer.constraints().types().neg(second_upper)
    else {
        unreachable!()
    };
    let Pos::Var(argument_value) = session.infer.constraints().types().pos(*arg) else {
        panic!("higher-order callback argument must preserve its value slot");
    };
    let Pos::Var(argument_effect) = session.infer.constraints().types().pos(*arg_eff) else {
        panic!("higher-order callback argument must preserve its evaluation-effect slot");
    };
    let Neg::Var(call_effect) = session.infer.constraints().types().neg(*ret_eff) else {
        panic!("higher-order nested call effect must preserve its slot");
    };
    let Neg::Var(result_value) = session.infer.constraints().types().neg(*ret) else {
        panic!("higher-order nested result must preserve its value slot");
    };
    DeferredNestedApplicationSnapshot {
        target_ref_value,
        callee_ref_value: *callee_ref_value,
        argument_value: *argument_value,
        argument_effect: *argument_effect,
        result_value: *result_value,
        result_effect: TypeVar(result_value.0 + 1),
        call_effect: *call_effect,
    }
}

fn find_call_to_target(session: &AnalysisSession, expr: ExprId, target: DefId) -> Option<ExprId> {
    match session.poly.expr(expr) {
        Expr::App(callee, arg) => {
            let direct_target = match session.poly.expr(*callee) {
                Expr::Var(reference) => {
                    session.poly.ref_target(*reference) == Some(target)
                        || session.work().iter().any(|work| {
                            matches!(
                                work,
                                AnalysisWork::ApplyRefResolution {
                                    ref_id,
                                    target: pending,
                                } if *ref_id == *reference && *pending == target
                            )
                        })
                }
                _ => false,
            };
            direct_target
                .then_some(expr)
                .or_else(|| find_call_to_target(session, *callee, target))
                .or_else(|| find_call_to_target(session, *arg, target))
        }
        Expr::RefSet(reference, value) => find_call_to_target(session, *reference, target)
            .or_else(|| find_call_to_target(session, *value, target)),
        Expr::Lambda(_, body) | Expr::Select(body, _) => {
            find_call_to_target(session, *body, target)
        }
        Expr::Tuple(items) | Expr::PolyVariant(_, items) => items
            .iter()
            .find_map(|item| find_call_to_target(session, *item, target)),
        Expr::Record { fields, spread } => fields
            .iter()
            .find_map(|(_, value)| find_call_to_target(session, *value, target))
            .or_else(|| match spread {
                RecordSpread::None => None,
                RecordSpread::Tail(value) | RecordSpread::Head(value) => {
                    find_call_to_target(session, *value, target)
                }
            }),
        Expr::Case(scrutinee, arms) => {
            find_call_to_target(session, *scrutinee, target).or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .and_then(|guard| find_call_to_target(session, guard, target))
                        .or_else(|| find_call_to_target(session, arm.body, target))
                })
            })
        }
        Expr::Catch(body, arms) => find_call_to_target(session, *body, target).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .and_then(|guard| find_call_to_target(session, guard, target))
                    .or_else(|| find_call_to_target(session, arm.body, target))
            })
        }),
        Expr::Block(statements, tail) => statements
            .iter()
            .find_map(|statement| find_call_in_statement(session, statement, target))
            .or_else(|| tail.and_then(|tail| find_call_to_target(session, tail, target))),
        Expr::Lit(_) | Expr::PrimitiveOp(_) | Expr::Var(_) => None,
    }
}

fn find_call_in_statement(
    session: &AnalysisSession,
    statement: &Stmt,
    target: DefId,
) -> Option<ExprId> {
    match statement {
        Stmt::Let(_, _, expr) | Stmt::Expr(expr) => find_call_to_target(session, *expr, target),
        Stmt::Module(_, statements) => statements
            .iter()
            .find_map(|statement| find_call_in_statement(session, statement, target)),
    }
}

fn lower_hand_built_second_application(
    body_lowerer: &mut crate::lowering::body::BodyLowerer,
    module: ModuleId,
    helper: DefId,
    parsed: DeferredSecondApplicationSnapshot,
) -> DeferredSecondApplicationSnapshot {
    let owner = body_lowerer.session.poly.defs.fresh();
    body_lowerer.session.poly.defs.set(
        owner,
        Def::Let {
            vis: Vis::My,
            scheme: None,
            body: None,
            children: Vec::new(),
        },
    );
    let previous_level = body_lowerer.session.infer.enter_child_level();
    let root = body_lowerer.session.infer.fresh_type_var();
    body_lowerer.typing.set_def(owner, root);
    body_lowerer
        .session
        .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
            def: owner,
            root,
        }));

    let (result, snapshot) = {
        let mut lowerer = ExprLowerer::new(
            &mut body_lowerer.session,
            &body_lowerer.modules,
            module,
            ModuleOrder::from_index(u32::MAX),
            owner,
        );
        let helper_ref = lowerer.lower_resolved_value_ref("with_ref".into(), helper);
        let helper_ref_value = helper_ref.value;
        let Expr::Var(helper_ref_id) = lowerer.session.poly.expr(helper_ref.expr) else {
            unreachable!()
        };
        assert_eq!(lowerer.session.poly.ref_target(*helper_ref_id), None);
        assert!(lowerer.session.work().iter().any(|work| matches!(
            work,
            AnalysisWork::ApplyRefResolution { ref_id, target }
                if *ref_id == *helper_ref_id && *target == helper
        )));
        let init_expr = lowerer.session.poly.add_expr(Expr::Lit(Lit::Unit));
        let init = Computation::value(
            init_expr,
            parsed.init_value,
            lowerer.fresh_exact_pure_effect(),
        );
        let helper_with_init = lowerer.make_internal_app(helper_ref, init);
        // Reuse the parsed body's slots and change only the value wrapper. This mirrors the
        // production migration shape, where an already-lowered body is wrapped in a fresh pure
        // `Fun` before the helper's second application.
        let (arg, arg_eff, ret_eff, ret) = match lowerer
            .session
            .infer
            .constraints()
            .types()
            .pos(parsed.callback_fun)
        {
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => (*arg, *arg_eff, *ret_eff, *ret),
            _ => unreachable!(),
        };
        let callback_value = lowerer.fresh_type_var();
        let callback_effect = lowerer.fresh_exact_pure_effect();
        lowerer.constrain_lower(
            callback_value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        let Expr::Lambda(pat, body) = lowerer.session.poly.expr(parsed.callback_expr) else {
            panic!("parsed comparison callback must be a lambda");
        };
        let callback_expr = lowerer.session.poly.add_expr(Expr::Lambda(*pat, *body));
        let callback = Computation::value(callback_expr, callback_value, callback_effect);
        let callback_fun = function_lower_bound(&lowerer, callback.value);
        let next = lowerer.session.infer.constraints().next_type_var();
        let result = lowerer.make_internal_app(helper_with_init, callback);
        assert_eq!(result.value, TypeVar(next));
        assert_eq!(result.effect, TypeVar(next + 1));
        let snapshot = DeferredSecondApplicationSnapshot {
            helper_ref_value,
            init_value: init.value,
            callback_expr,
            callback_value: callback.value,
            callback_fun,
            callback_body_effect: parsed.callback_body_effect,
            result_effect: result.effect,
            call_effect: TypeVar(next + 2),
        };
        (result, snapshot)
    };

    let body_pos = body_lowerer.session.infer.alloc_pos(Pos::Var(result.value));
    let root_neg = body_lowerer.session.infer.alloc_neg(Neg::Var(root));
    body_lowerer
        .session
        .infer
        .subtype(body_pos, root_neg, OriginId::unknown_internal());
    let Some(Def::Let { body, .. }) = body_lowerer.session.poly.defs.get_mut(owner) else {
        unreachable!()
    };
    *body = Some(result.expr);
    body_lowerer
        .session
        .record_binding_fetch(owner, BindingFetch::from_evaluation(result.evaluation));
    body_lowerer
        .session
        .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: owner }));
    body_lowerer.session.infer.restore_level(previous_level);
    snapshot
}

fn application_argument_value(
    machine: &crate::constraints::ConstraintMachine,
    helper_ref_value: TypeVar,
    stage: usize,
) -> TypeVar {
    let mut callee = helper_ref_value;
    for current in 1..=stage {
        let upper = function_upper_bound(machine, callee);
        let Neg::Fun { arg, ret, .. } = machine.types().neg(upper) else {
            unreachable!()
        };
        if current == stage {
            let Pos::Var(argument) = machine.types().pos(*arg) else {
                panic!("application argument must use its computation value slot");
            };
            return *argument;
        }
        let Neg::Var(result) = machine.types().neg(*ret) else {
            panic!("application result must use its fresh value slot");
        };
        callee = *result;
    }
    unreachable!()
}

fn second_application_effect_slots(
    machine: &crate::constraints::ConstraintMachine,
    helper_ref_value: TypeVar,
) -> (TypeVar, TypeVar) {
    let first_upper = function_upper_bound(machine, helper_ref_value);
    let Neg::Fun { ret, .. } = machine.types().neg(first_upper) else {
        unreachable!()
    };
    let Neg::Var(helper_with_init) = machine.types().neg(*ret) else {
        panic!("first application result must use its fresh value slot");
    };
    let second_upper = function_upper_bound(machine, *helper_with_init);
    let Neg::Fun { ret_eff, ret, .. } = machine.types().neg(second_upper) else {
        unreachable!()
    };
    let Neg::Var(result_value) = machine.types().neg(*ret) else {
        panic!("second application result must use its fresh value slot");
    };
    let Neg::Var(call_effect) = machine.types().neg(*ret_eff) else {
        panic!("second application call effect must be a bare deferred slot");
    };
    // `make_app_with_origins` allocates result value, result effect, and call effect in order.
    (TypeVar(result_value.0 + 1), *call_effect)
}

fn function_upper_bound(machine: &crate::constraints::ConstraintMachine, value: TypeVar) -> NegId {
    machine
        .bounds()
        .of(value)
        .and_then(|bounds| {
            bounds.uppers().iter().find_map(|bound| {
                matches!(machine.types().neg(bound.neg), Neg::Fun { .. }).then_some(bound.neg)
            })
        })
        .unwrap_or_else(|| panic!("value {value:?} must have an application function upper"))
}

fn function_lower_bound_in_machine(
    machine: &crate::constraints::ConstraintMachine,
    value: TypeVar,
) -> PosId {
    machine
        .bounds()
        .of(value)
        .and_then(|bounds| {
            bounds.lowers().iter().find_map(|bound| {
                matches!(machine.types().pos(bound.pos), Pos::Fun { .. }).then_some(bound.pos)
            })
        })
        .unwrap_or_else(|| panic!("value {value:?} must have a function lower"))
}

fn function_return_effect_var(
    machine: &crate::constraints::ConstraintMachine,
    function: PosId,
) -> TypeVar {
    let Pos::Fun { ret_eff, .. } = machine.types().pos(function) else {
        unreachable!()
    };
    let Pos::Var(effect) = machine.types().pos(*ret_eff) else {
        panic!("callback return effect must preserve its body slot");
    };
    *effect
}

fn post_resolution_edges(
    output: &BodyLowering,
    snapshot: DeferredSecondApplicationSnapshot,
) -> PostResolutionEdges {
    let machine = output.session.infer.constraints();
    let helper = function_lower_bound_in_machine(machine, snapshot.helper_ref_value);
    let Pos::Fun { ret, .. } = machine.types().pos(helper) else {
        unreachable!()
    };
    let Pos::Fun {
        arg: expected_callback,
        ret_eff: helper_result_effect,
        ..
    } = machine.types().pos(*ret)
    else {
        panic!("resolved helper must expose the second-stage callback application");
    };
    let Neg::Fun {
        ret_eff: expected_callback_effect,
        ..
    } = machine.types().neg(*expected_callback)
    else {
        panic!("resolved helper callback argument must be callable");
    };
    let callback_var = pos_var_id(machine.types(), snapshot.callback_value);
    let callback_effect = match machine.types().pos(snapshot.callback_fun) {
        Pos::Fun { ret_eff, .. } => {
            assert!(
                matches!(
                    machine.types().pos(*ret_eff),
                    Pos::Var(effect) if *effect == snapshot.callback_body_effect
                ),
                "the callback Fun must retain the snapshotted body-effect slot"
            );
            *ret_eff
        }
        _ => unreachable!(),
    };
    let call_effect_upper = neg_var_id(machine.types(), snapshot.call_effect);
    let result_effect_upper = neg_var_id(machine.types(), snapshot.result_effect);
    let call_effect_lower = pos_var_id(machine.types(), snapshot.call_effect);
    let has_edge = |lower, upper| {
        machine
            .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .is_some()
    };
    let family_path = expected_family_path(machine.types(), *expected_callback_effect);
    let family_row = family_row_reaching_var(machine, snapshot.callback_body_effect, &family_path);

    PostResolutionEdges {
        callback_to_expected: has_edge(callback_var, *expected_callback),
        callback_fun_to_expected: has_edge(snapshot.callback_fun, *expected_callback),
        callback_effect_to_expected: has_edge(callback_effect, *expected_callback_effect),
        family_row_to_expected: has_edge(family_row, *expected_callback_effect),
        helper_effect_to_call: has_edge(*helper_result_effect, call_effect_upper),
        call_to_result: has_edge(call_effect_lower, result_effect_upper),
        result_has_family_lower: var_reaches_family(machine, snapshot.result_effect, &family_path),
    }
}

fn v5_nested_boundary_trace(
    output: &BodyLowering,
    definition: HandBuiltNestedDefinition,
    inner_family: &[String],
) -> V5NestedBoundaryTrace {
    let snapshot = definition
        .nested_call
        .expect("outer definition must retain its nested-call slots");
    let machine = output.session.infer.constraints();
    let resolved_fun = function_lower_bound_in_machine(machine, snapshot.callee_ref_value);
    let Pos::Fun {
        arg: expected_callback,
        ret_eff: inner_return_effect,
        ..
    } = machine.types().pos(resolved_fun)
    else {
        unreachable!()
    };
    let application = function_upper_bound(machine, snapshot.callee_ref_value);
    let Neg::Fun { arg_eff, .. } = machine.types().neg(application) else {
        unreachable!()
    };
    let Pos::Var(argument_effect) = machine.types().pos(*arg_eff) else {
        panic!("nested callback evaluation effect must preserve its variable slot");
    };
    assert_eq!(*argument_effect, snapshot.argument_effect);
    let Neg::Fun {
        ret_eff: expected_callback_effect,
        ..
    } = machine.types().neg(*expected_callback)
    else {
        panic!("higher-order inner callback argument must remain callable");
    };
    let Neg::Row(_, expected_callback_tail) = machine.types().neg(*expected_callback_effect) else {
        panic!("higher-order inner callback must expose its handled family and residual tail");
    };
    let Neg::Var(expected_residual) = machine.types().neg(*expected_callback_tail) else {
        panic!("higher-order inner callback residual must instantiate as a variable");
    };
    let Pos::Var(inner_return_var) = machine.types().pos(*inner_return_effect) else {
        panic!("higher-order inner return effect must be the instantiated residual variable");
    };
    assert_eq!(
        inner_return_var, expected_residual,
        "the inner result effect must reuse the callback contract's residual"
    );
    let actual_callback_fun = function_lower_bound_in_machine(machine, snapshot.argument_value);
    let actual_callback_body_effect = function_return_effect_var(machine, actual_callback_fun);
    let callback_body_effect = definition.boundary.callback_body_effect;
    let callback_ret_eff = function_return_effect_var(machine, definition.boundary.callback_fun);
    let has_edge = |lower, upper| {
        machine
            .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .is_some()
    };
    let residual_upper = neg_var_id(machine.types(), *inner_return_var);
    let callback_body_to_residual_explanation = machine
        .bounds()
        .of(actual_callback_body_effect)
        .and_then(|bounds| {
            bounds
                .uppers()
                .iter()
                .position(|upper| upper.neg == residual_upper)
                .map(|index| bounds.upper_record_ids()[index])
        })
        .and_then(|record| {
            machine
                .why_upper_bound(
                    actual_callback_body_effect,
                    record,
                    ExplanationBudget::default(),
                )
                .ok()
        });
    let callback_body_to_residual_rules = callback_body_to_residual_explanation
        .iter()
        .flat_map(|explanation| explanation.edges.iter())
        .filter_map(|edge| match &edge.kind {
            ExplanationEdgeKind::Structural(rule) => Some(*rule),
            _ => None,
        })
        .collect();
    let callback_body_to_residual_row_rules = callback_body_to_residual_explanation
        .iter()
        .flat_map(|explanation| explanation.edges.iter())
        .filter_map(|edge| match &edge.kind {
            ExplanationEdgeKind::Row(rule) => Some(*rule),
            _ => None,
        })
        .collect();

    V5NestedBoundaryTrace {
        instantiated_inner_return_effect: effect_slot_trace(
            machine,
            *inner_return_var,
            inner_family,
        ),
        actual_callback_body_effect: effect_slot_trace(
            machine,
            actual_callback_body_effect,
            inner_family,
        ),
        inner_return_family_lower_path: family_lower_path(machine, *inner_return_var, inner_family),
        callback_body_to_residual_rules,
        callback_body_to_residual_row_rules,
        argument_effect: effect_slot_trace(machine, snapshot.argument_effect, inner_family),
        call_effect: effect_slot_trace(machine, snapshot.call_effect, inner_family),
        result_effect: effect_slot_trace(machine, snapshot.result_effect, inner_family),
        outer_aggregate_effect: effect_slot_trace(machine, callback_body_effect, inner_family),
        outer_callback_ret_eff: callback_ret_eff,
        outer_second_application_effect: effect_slot_trace(
            machine,
            definition.boundary.result_effect,
            inner_family,
        ),
        argument_effect_to_call: has_edge(
            pos_var_id(machine.types(), snapshot.argument_effect),
            neg_var_id(machine.types(), snapshot.call_effect),
        ),
        inner_return_effect_to_call: has_edge(
            *inner_return_effect,
            neg_var_id(machine.types(), snapshot.call_effect),
        ),
        call_to_result: has_edge(
            pos_var_id(machine.types(), snapshot.call_effect),
            neg_var_id(machine.types(), snapshot.result_effect),
        ),
        result_to_outer_aggregate: has_edge(
            pos_var_id(machine.types(), snapshot.result_effect),
            neg_var_id(machine.types(), callback_body_effect),
        ),
    }
}

fn nested_application_edges(
    output: &BodyLowering,
    definition: HandBuiltNestedDefinition,
) -> NestedApplicationEdges {
    let snapshot = definition
        .nested_call
        .expect("outer definition must retain its nested-call slots");
    let machine = output.session.infer.constraints();
    let resolved_fun = function_lower_bound_in_machine(machine, snapshot.callee_ref_value);
    let Pos::Fun {
        arg: instantiated_argument,
        arg_eff: inner_argument_effect,
        ret_eff: inner_return_effect,
        ..
    } = machine.types().pos(resolved_fun)
    else {
        unreachable!()
    };
    assert!(
        matches!(machine.types().neg(*inner_argument_effect), Neg::Bot),
        "both nested targets take an ordinary pure function parameter"
    );
    let instantiated_argument_birth_level =
        if let Neg::Var(instantiated_argument) = machine.types().neg(*instantiated_argument) {
            machine.birth_level_of(*instantiated_argument)
        } else {
            TypeLevel::secondary()
        };

    let application = function_upper_bound(machine, snapshot.callee_ref_value);
    let Neg::Fun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    } = machine.types().neg(application)
    else {
        unreachable!()
    };
    assert!(
        matches!(machine.types().pos(*arg), Pos::Var(var) if *var == snapshot.argument_value),
        "the nested application must retain the snapshotted argument value"
    );
    assert!(
        matches!(
            machine.types().pos(*arg_eff),
            Pos::Var(var) if *var == snapshot.argument_effect
        ),
        "the nested application must retain the snapshotted argument-evaluation effect"
    );
    assert!(
        matches!(
            machine.types().neg(*ret_eff),
            Neg::Var(var) if *var == snapshot.call_effect
        ),
        "the nested application must retain the snapshotted call effect"
    );
    assert!(
        matches!(
            machine.types().neg(*ret),
            Neg::Var(var) if *var == snapshot.result_value
        ),
        "the nested application must retain the snapshotted result value"
    );

    let callee_ref = pos_var_id(machine.types(), snapshot.callee_ref_value);
    let argument_effect = pos_var_id(machine.types(), snapshot.argument_effect);
    let call_effect_upper = neg_var_id(machine.types(), snapshot.call_effect);
    let call_effect_lower = pos_var_id(machine.types(), snapshot.call_effect);
    let result_effect_upper = neg_var_id(machine.types(), snapshot.result_effect);
    let result_effect_lower = pos_var_id(machine.types(), snapshot.result_effect);
    let callback_body_effect = definition.boundary.callback_body_effect;
    let result_is_callback_body = snapshot.result_effect == callback_body_effect;
    let has_edge = |lower, upper| {
        machine
            .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .is_some()
    };
    let outer_family = resolved_snapshot_family_path(output, definition.boundary);
    let inner_return_family = concrete_effect_family_path(machine.types(), *inner_return_effect);

    NestedApplicationEdges {
        callee_ref_to_application: has_edge(callee_ref, application),
        resolved_fun_to_application: has_edge(resolved_fun, application),
        // A pure `Pos::Fun.arg_eff` makes function decomposition pass the application's
        // argument-evaluation effect into the same call-effect upper used by `ret_eff`.
        argument_effect_to_call: has_edge(argument_effect, call_effect_upper),
        inner_return_effect_to_call: has_edge(*inner_return_effect, call_effect_upper),
        call_to_result: has_edge(call_effect_lower, result_effect_upper),
        result_to_callback_body: !result_is_callback_body
            && has_edge(
                result_effect_lower,
                neg_var_id(machine.types(), callback_body_effect),
            ),
        result_is_callback_body,
        callback_body_reaches_result: var_reaches_var(
            machine,
            callback_body_effect,
            snapshot.result_effect,
        ),
        argument_effect_has_outer_family_lower: var_reaches_family(
            machine,
            snapshot.argument_effect,
            &outer_family,
        ),
        argument_outer_family_row_count: family_rows_reaching_var(
            machine,
            snapshot.argument_effect,
            &outer_family,
        )
        .len(),
        argument_outer_family_source_count: family_source_vars_reaching_var(
            machine,
            snapshot.argument_effect,
            &outer_family,
        )
        .len(),
        argument_effect_has_inner_return_family_lower: var_reaches_family(
            machine,
            snapshot.argument_effect,
            &inner_return_family,
        ),
        nested_result_has_outer_family_lower: var_reaches_family(
            machine,
            snapshot.result_effect,
            &outer_family,
        ),
        callback_body_has_outer_family_lower: var_reaches_family(
            machine,
            callback_body_effect,
            &outer_family,
        ),
        outer_result_has_outer_family_lower: var_reaches_family(
            machine,
            definition.boundary.result_effect,
            &outer_family,
        ),
        callee_ref_birth_level: machine.birth_level_of(snapshot.callee_ref_value),
        argument_effect_birth_level: machine.birth_level_of(snapshot.argument_effect),
        result_effect_birth_level: machine.birth_level_of(snapshot.result_effect),
        call_effect_birth_level: machine.birth_level_of(snapshot.call_effect),
        instantiated_argument_birth_level,
    }
}

fn concrete_effect_family_path(types: &TypeArena, effect: PosId) -> Vec<String> {
    let Pos::Row(items) = types.pos(effect) else {
        panic!("the nested target's finalized return effect must instantiate as a concrete row");
    };
    items
        .iter()
        .find_map(|item| match types.pos(*item) {
            Pos::Con(path, _) => Some(path.clone()),
            _ => None,
        })
        .expect("the nested target return effect must contain its concrete residual family")
}

fn var_reaches_var(
    machine: &crate::constraints::ConstraintMachine,
    root: TypeVar,
    target: TypeVar,
) -> bool {
    let mut pending = vec![root];
    let mut visited = rustc_hash::FxHashSet::default();
    while let Some(var) = pending.pop() {
        if var == target {
            return true;
        }
        if !visited.insert(var) {
            continue;
        }
        let Some(bounds) = machine.bounds().of(var) else {
            continue;
        };
        for lower in bounds.lowers() {
            if let Pos::Var(next) = machine.types().pos(lower.pos) {
                pending.push(*next);
            }
        }
    }
    false
}

fn family_row_reaching_var(
    machine: &crate::constraints::ConstraintMachine,
    root: TypeVar,
    family_path: &[String],
) -> PosId {
    let mut pending = vec![root];
    let mut visited = rustc_hash::FxHashSet::default();
    while let Some(var) = pending.pop() {
        if !visited.insert(var) {
            continue;
        }
        let Some(bounds) = machine.bounds().of(var) else {
            continue;
        };
        for lower in bounds.lowers() {
            match machine.types().pos(lower.pos) {
                Pos::Row(items)
                    if items.iter().any(|item| {
                        matches!(
                            machine.types().pos(*item),
                            Pos::Con(path, _) if path == family_path
                        )
                    }) =>
                {
                    return lower.pos;
                }
                Pos::Var(next) => pending.push(*next),
                _ => {}
            }
        }
    }
    panic!("callback body effect must retain its concrete local-family row")
}

fn family_rows_reaching_var(
    machine: &crate::constraints::ConstraintMachine,
    root: TypeVar,
    family_path: &[String],
) -> rustc_hash::FxHashSet<PosId> {
    let mut rows = rustc_hash::FxHashSet::default();
    let mut pending = vec![root];
    let mut visited = rustc_hash::FxHashSet::default();
    while let Some(var) = pending.pop() {
        if !visited.insert(var) {
            continue;
        }
        let Some(bounds) = machine.bounds().of(var) else {
            continue;
        };
        for lower in bounds.lowers() {
            match machine.types().pos(lower.pos) {
                Pos::Row(items)
                    if items.iter().any(|item| {
                        matches!(
                            machine.types().pos(*item),
                            Pos::Con(path, _) if path == family_path
                        )
                    }) =>
                {
                    rows.insert(lower.pos);
                }
                Pos::Var(next) => pending.push(*next),
                _ => {}
            }
        }
    }
    rows
}

fn family_source_vars_reaching_var(
    machine: &crate::constraints::ConstraintMachine,
    root: TypeVar,
    family_path: &[String],
) -> rustc_hash::FxHashSet<TypeVar> {
    let mut sources = rustc_hash::FxHashSet::default();
    let mut pending = vec![root];
    let mut visited = rustc_hash::FxHashSet::default();
    while let Some(var) = pending.pop() {
        if !visited.insert(var) {
            continue;
        }
        let Some(bounds) = machine.bounds().of(var) else {
            continue;
        };
        for lower in bounds.lowers() {
            match machine.types().pos(lower.pos) {
                Pos::Row(items)
                    if items.iter().any(|item| {
                        matches!(
                            machine.types().pos(*item),
                            Pos::Con(path, _) if path == family_path
                        )
                    }) =>
                {
                    sources.insert(var);
                }
                Pos::Var(next) => pending.push(*next),
                _ => {}
            }
        }
    }
    sources
}

fn pos_var_id(types: &TypeArena, var: TypeVar) -> PosId {
    types
        .pos_nodes()
        .iter()
        .position(|node| matches!(node, Pos::Var(found) if *found == var))
        .map(|index| PosId(index as u32))
        .unwrap_or_else(|| panic!("positive use for {var:?}"))
}

fn neg_var_id(types: &TypeArena, var: TypeVar) -> NegId {
    types
        .neg_nodes()
        .iter()
        .position(|node| matches!(node, Neg::Var(found) if *found == var))
        .map(|index| NegId(index as u32))
        .unwrap_or_else(|| panic!("negative use for {var:?}"))
}

fn expected_family_path(types: &TypeArena, expected_effect: NegId) -> Vec<String> {
    let Neg::Row(items, _) = types.neg(expected_effect) else {
        panic!("helper callback effect must expose a concrete family prefix");
    };
    let family = items
        .iter()
        .find_map(|item| match types.neg(*item) {
            Neg::Con(path, _) => Some(path),
            _ => None,
        })
        .expect("helper callback effect family");
    family.clone()
}

fn multi_statement_single_boundary_fixture_source() -> &'static str {
    concat!(
        "pub mod std:\n",
        "  pub mod control:\n",
        "    pub mod var:\n",
        "      pub type ref 'e 'a with:\n",
        "        struct self:\n",
        "          get: () -> ['e] 'a\n",
        "      pub act single_var 't:\n",
        "        pub get: () -> 't\n",
        "        pub set: 't -> ()\n",
        "        my var_ref(): std::control::var::ref '[single_var 't] 't = ",
        "std::control::var::ref { get: \\() -> get() }\n",
        "        my run(v: 't, x: [_] 'r): 'r = catch x:\n",
        "          get(), k -> run v: k v\n",
        "          set v, k -> run v: k()\n",
        "        my with_ref(\n",
        "          init: 'p,\n",
        "          callback: std::control::var::ref _ 'p -> [_] 'r,\n",
        "        ) = run init (callback var_ref())\n",
        "        pub parsed_enclosing(init: 'p) = with_ref init: \\r ->\n",
        "          r.get()\n",
        "          r.get()\n",
        "          r.get()\n",
    )
}

fn nested_deferred_resolution_fixture_source() -> &'static str {
    concat!(
        "pub mod std:\n",
        "  pub mod control:\n",
        "    pub mod var:\n",
        "      pub act observe 'a:\n",
        "        pub mark: 'a -> 'a\n",
        "      pub act ref_update 'a:\n",
        "        pub update: 'a -> 'a\n",
        "      pub type ref 'e 'a with:\n",
        "        struct self:\n",
        "          get: () -> ['e] 'a\n",
        "          update_effect: () -> [ref_update 'a; 'e] ()\n",
        "        pub r.update f =\n",
        "          my loop(x: [_] _) = catch x:\n",
        "            ref_update::update v, k -> loop:k:f v\n",
        "          loop:r.update_effect()\n",
        "      pub act var 't:\n",
        "        pub get: () -> 't\n",
        "        pub set: 't -> ()\n",
        "        my var_ref(): std::control::var::ref '[var 't] 't = std::control::var::ref {\n",
        "          get: \\() -> get(),\n",
        "          update_effect: \\() -> set:std::control::var::ref_update::update:get()\n",
        "        }\n",
        "        my run(v: 't, x: [_] 'r): 'r = catch x:\n",
        "          get(), k -> run v: k v\n",
        "          set v, k -> run v: k()\n",
        "        my with_ref(\n",
        "          init: 'p,\n",
        "          callback: std::control::var::ref _ 'p -> [_] 'r,\n",
        "        ) = run init (callback var_ref())\n",
        "      pub act inner_var 't:\n",
        "        pub get: () -> 't\n",
        "        pub set: 't -> ()\n",
        "        my var_ref(): std::control::var::ref '[inner_var 't] 't = std::control::var::ref {\n",
        "          get: \\() -> get(),\n",
        "          update_effect: \\() -> set:std::control::var::ref_update::update:get()\n",
        "        }\n",
        "        my run(v: 't, x: [_] 'r): 'r = catch x:\n",
        "          get(), k -> run v: k v\n",
        "          set v, k -> run v: k()\n",
        "        my with_ref(\n",
        "          init: 'p,\n",
        "          callback: std::control::var::ref _ 'p -> [_] 'r,\n",
        "        ) = run init (callback var_ref())\n",
        "        pub enclosing(init: 'p) = with_ref init: \\r ->\n",
        "          my before = r.get()\n",
        "          r.update (\\_ -> before)\n",
        "          std::control::var::observe::mark:r.get()\n",
        "        pub higher_inner(\n",
        "          init: 'p,\n",
        "          callback: std::control::var::ref _ 'p -> [_] 'r,\n",
        "        ) = with_ref init: \\r ->\n",
        "          (callback r, r.get())\n",
        "      pub act outer_var 't:\n",
        "        pub get: () -> 't\n",
        "        pub set: 't -> ()\n",
        "        my var_ref(): std::control::var::ref '[outer_var 't] 't = std::control::var::ref {\n",
        "          get: \\() -> get(),\n",
        "          update_effect: \\() -> set:std::control::var::ref_update::update:get()\n",
        "        }\n",
        "        my run(v: 't, x: [_] 'r): 'r = catch x:\n",
        "          get(), k -> run v: k v\n",
        "          set v, k -> run v: k()\n",
        "        my with_ref(\n",
        "          init: 'p,\n",
        "          callback: std::control::var::ref _ 'p -> [_] 'r,\n",
        "        ) = run init (callback var_ref())\n",
        "        my enclosing(init: 'p) = with_ref init: \\r ->\n",
        "          my before = r.get()\n",
        "          r.update (\\_ -> before)\n",
        "          std::control::var::inner_var::enclosing:r.get()\n",
        "        my higher_outer(init: 'p) = with_ref init: \\r ->\n",
        "          r.get()\n",
        "          std::control::var::inner_var::higher_inner r.get(): \\inner_r ->\n",
        "            my before = inner_r.get()\n",
        "            inner_r.update (\\_ -> before)\n",
        "            std::control::var::observe::mark:inner_r.get()\n",
        "my text_with_mock_trigger(init: 'p) =\n",
        "  my $buffer = init\n",
        "  $buffer\n",
        "my run_trigger(init: 'p) =\n",
        "  my $store = init\n",
        "  $store\n",
    )
}

fn deferred_resolution_fixture_source() -> &'static str {
    concat!(
        "pub mod std:\n",
        "  pub mod control:\n",
        "    pub mod var:\n",
        "      pub act observe 'a:\n",
        "        pub mark: 'a -> 'a\n",
        "      pub act ref_update 'a:\n",
        "        pub update: 'a -> 'a\n",
        "      pub type ref 'e 'a with:\n",
        "        struct self:\n",
        "          get: () -> ['e] 'a\n",
        "          update_effect: () -> [ref_update 'a; 'e] ()\n",
        "        pub r.update f =\n",
        "          my loop(x: [_] _) = catch x:\n",
        "            ref_update::update v, k -> loop:k:f v\n",
        "          loop:r.update_effect()\n",
        "      pub act var 't:\n",
        "        pub get: () -> 't\n",
        "        pub set: 't -> ()\n",
        "        my var_ref(): std::control::var::ref '[var 't] 't = std::control::var::ref {\n",
        "          get: \\() -> get(),\n",
        "          update_effect: \\() -> set:std::control::var::ref_update::update:get()\n",
        "        }\n",
        "        my run(v: 't, x: [_] 'r): 'r = catch x:\n",
        "          get(), k -> run v: k v\n",
        "          set v, k -> run v: k()\n",
        "        my with_ref(\n",
        "          init: 'p,\n",
        "          callback: std::control::var::ref _ 'p -> [_] 'r,\n",
        "        ) = run init (callback var_ref())\n",
        "        my enclosing(init: 'p) = with_ref init: \\r ->\n",
        "          my before = r.get()\n",
        "          r.update (\\_ -> before)\n",
        "          std::control::var::observe::mark:r.get()\n",
        "my trigger(init: 'p) =\n",
        "  my $x = init\n",
        "  $x\n",
    )
}

fn boundary_fixture() -> (BodyLowering, DefId, DefId, ModuleOrder) {
    let root = parse(concat!(
        "pub mod std:\n",
        "  pub mod control:\n",
        "    pub mod var:\n",
        "      pub act ref_update 'a:\n",
        "        pub update: 'a -> 'a\n",
        "      pub type ref 'e 'a with:\n",
        "        struct self:\n",
        "          get: () -> ['e] 'a\n",
        "          update_effect: () -> [ref_update 'a; 'e] ()\n",
        "      pub act var 't:\n",
        "        pub get: () -> 't\n",
        "        pub set: 't -> ()\n",
        "        my var_ref(): std::control::var::ref '[var 't] 't = std::control::var::ref {\n",
        "          get: \\() -> get(),\n",
        "          update_effect: \\() -> set:std::control::var::ref_update::update:get()\n",
        "        }\n",
        "        my run(v: 't, x: [_] 'r): 'r = catch x:\n",
        "          get(), k -> run v: k v\n",
        "          set v, k -> run v: k()\n",
        "        my with_ref(\n",
        "          init: 'p,\n",
        "          callback: std::control::var::ref _ 'p -> [_] 'r,\n",
        "        ) = run init (callback var_ref())\n",
        "my trigger(init: 'p) =\n",
        "  my $x = init\n",
        "  $x\n",
    ));
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, root_module, "trigger");
    let local_var_act = lower.modules.synthetic_var_act_uses(owner)[0].clone();
    let companion = lower
        .modules
        .type_companion(local_var_act.act)
        .expect("synthetic var act companion");
    let helper = lower
        .modules
        .value_decls(companion, &Name("with_ref".into()))[0]
        .def;
    let output = lower_binding_bodies(&root, lower);
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    (output, helper, owner, site)
}

fn instantiated_helper_family_path(types: &TypeArena, helper: PosId) -> Vec<String> {
    let Pos::Fun { ret, .. } = types.pos(helper) else {
        panic!("helper must take init first");
    };
    let Pos::Fun { arg, .. } = types.pos(*ret) else {
        panic!("helper must take callback second");
    };
    let Neg::Fun { ret_eff, .. } = types.neg(*arg) else {
        panic!("helper callback argument must be callable");
    };
    let Neg::Row(items, _) = types.neg(*ret_eff) else {
        panic!("helper callback effect must have a concrete family prefix");
    };
    let [item] = items.as_slice() else {
        panic!("helper callback effect must have one concrete family");
    };
    let Neg::Con(path, _) = types.neg(*item) else {
        panic!("helper callback effect item must be nominal");
    };
    path.clone()
}
