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
