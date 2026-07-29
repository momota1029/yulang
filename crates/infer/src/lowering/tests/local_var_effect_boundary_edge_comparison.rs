//! LVB callback construction comparison at the second application boundary.
//!
//! `ConstraintMachine` does not expose a full constraint-record iterator. The harness therefore
//! snapshots the second application's three fresh slots, recovers the structural endpoints from
//! their bounds, and queries each expected canonical edge with `debug_constraint_record_id`.
//! This keeps the comparison structural without adding production-only introspection.

use super::*;

use crate::constraints::{ConstraintWeights, OriginId, TypeLevel};
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
    queued_registration: Option<DefinitionRegistration>,
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
    let (mut output, parsed_inner, parsed_outer, hand_inner, hand_outer) =
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

fn nested_deferred_resolution_fixture() -> (
    BodyLowering,
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
        queued_registration: None,
    };
    let parsed_outer = HandBuiltNestedDefinition {
        def: parsed_outer_def,
        root: lowerer
            .typing
            .def(parsed_outer_def)
            .expect("parsed outer generalization root"),
        boundary: recover_parsed_second_application_snapshot(
            &lowerer.session,
            parsed_outer_def,
            parsed_outer_helper,
        ),
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

    lowerer.drain_analysis_with_conformance();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    let output = lowerer.finish();
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    (output, parsed_inner, parsed_outer, hand_inner, hand_outer)
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

    let (function, boundary) = {
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
        let callback = if let Some(nested_target) = nested_target {
            wrap_callback_body_in_nested_call(&mut lowerer, callback, nested_target)
        } else {
            callback
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
        queued_registration: Some(queued_registration),
    }
}

fn wrap_callback_body_in_nested_call(
    lowerer: &mut ExprLowerer<'_>,
    callback: Computation,
    nested_target: DefId,
) -> Computation {
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
    let nested_result = lowerer.make_internal_app(nested_ref, nested_arg);
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
    Computation::value(expr, value, effect)
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
                SccEvent::InstantiateUse { parent, target, .. }
                    if *parent == outer.def && *target == inner.def
            )
        })
        .expect("outer use must instantiate the finalized inner scheme");
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
    let Expr::Lambda(_, enclosing_body) =
        session.poly.expr(match session.poly.defs.get(enclosing) {
            Some(Def::Let {
                body: Some(body), ..
            }) => *body,
            _ => panic!("parsed enclosing witness must have a lowered body"),
        })
    else {
        panic!("parsed enclosing witness must lower its init parameter as a lambda");
    };
    let Expr::App(helper_with_init, callback_expr) = session.poly.expr(*enclosing_body) else {
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
