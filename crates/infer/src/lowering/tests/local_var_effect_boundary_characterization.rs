use super::*;

use crate::compact::{
    CompactBounds, CompactFun, CompactRoot, CompactType, compact_type_var_for_scheme,
};
use crate::constraints::{ConstraintMachine, LeftConstraintWeight, OriginId, TypeLevel};
use crate::generalize::{finalize_generalized_compact_root, generalize_compact_root};
use crate::instantiate::instantiate_scheme;
use rustc_hash::FxHashSet;

const FAMILY_PATH: [&str; 2] = ["synthetic", "local_state"];
const REF_PATH: [&str; 2] = ["synthetic", "ref"];
const OBSERVE_PATH: [&str; 4] = ["std", "control", "var", "observe"];

#[test]
fn real_run_single_source_transport_reaches_callback_without_a_second_stack_owner() {
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
        "my h(init: 'p, callback: std::control::var::ref _ 'p -> [_] 'r) =\n",
        "  my $x = init\n",
        "  callback &x\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");
    let local_var_act = lower.modules.synthetic_var_act_uses(h)[0].clone();
    let local_var_companion = lower.modules.type_companion(local_var_act.act).unwrap();
    let run = lower
        .modules
        .value_decls(local_var_companion, &Name("run".into()))[0]
        .def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let run_scheme = def_scheme(&output, run);
    assert!(
        output.session.generalized_scheme_record(run).is_some(),
        "the synthetic run definition must be generalized through the ordinary analysis path"
    );
    assert!(
        run_scheme.stack_quantifiers.is_empty(),
        "run must materialize its family row before the resolved use is instantiated"
    );
    let run_boundary = extract_real_run_boundary(&output.session.poly.typ, run_scheme.predicate);

    let callback_ref = assert_real_run_two_step_application(&output, h, run);
    assert_callback_call_uses_bare_return_effect(&output, callback_ref);
    assert_no_helper_owned_stack_source(
        output.session.infer.constraints().types(),
        &run_boundary.family_path,
    );

    let helper_scheme = def_scheme(&output, h);
    assert!(helper_scheme.stack_quantifiers.is_empty());
    let helper_boundary =
        extract_real_run_helper_boundary(&output.session.poly.typ, helper_scheme.predicate);
    assert_eq!(helper_boundary.family_path, run_boundary.family_path);
    assert_ne!(
        helper_boundary.payload, run_boundary.payload,
        "the resolved run scheme must be freshened at the helper use site"
    );
    assert_ne!(
        helper_boundary.residual, run_boundary.residual,
        "the resolved run residual must be freshened at the helper use site"
    );

    let mut instances = crate::arena::Arena::new();
    let first = instantiate_scheme(
        &output.session.poly.typ,
        &mut instances,
        TypeLevel::root(),
        helper_scheme,
    );
    let second = instantiate_scheme(
        &output.session.poly.typ,
        &mut instances,
        TypeLevel::root(),
        helper_scheme,
    );
    let first = extract_real_run_helper_boundary(instances.constraints().types(), first);
    let second = extract_real_run_helper_boundary(instances.constraints().types(), second);
    assert_ne!(first.payload, helper_boundary.payload);
    assert_ne!(first.residual, helper_boundary.residual);
    assert_ne!(second.payload, helper_boundary.payload);
    assert_ne!(second.residual, helper_boundary.residual);
    assert_ne!(first.payload, second.payload);
    assert_ne!(first.residual, second.residual);
}

#[test]
fn separately_resolved_helper_preserves_single_source_transport_across_two_call_sites() {
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
        "        my first(\n",
        "          init: 'p,\n",
        "          callback: std::control::var::ref _ 'p -> [_] 'r,\n",
        "        ) = with_ref init callback\n",
        "        my second(\n",
        "          init: 'p,\n",
        "          callback: std::control::var::ref _ 'p -> [_] 'r,\n",
        "        ) = with_ref init callback\n",
        "my trigger(init: 'p) =\n",
        "  my $x = init\n",
        "  $x\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (trigger, _) = binding_def_and_order(&lower.modules, module, "trigger");
    let local_var_act = lower.modules.synthetic_var_act_uses(trigger)[0].clone();
    let local_var_companion = lower.modules.type_companion(local_var_act.act).unwrap();
    let with_ref = lower
        .modules
        .value_decls(local_var_companion, &Name("with_ref".into()))[0]
        .def;
    let first = lower
        .modules
        .value_decls(local_var_companion, &Name("first".into()))[0]
        .def;
    let second = lower
        .modules
        .value_decls(local_var_companion, &Name("second".into()))[0]
        .def;
    assert!(
        lower.modules.synthetic_var_act_uses(with_ref).is_empty()
            && lower.modules.synthetic_var_act_uses(first).is_empty()
            && lower.modules.synthetic_var_act_uses(second).is_empty(),
        "the copied helper and callers must not recursively enter local-var lowering"
    );
    let run = lower
        .modules
        .value_decls(local_var_companion, &Name("run".into()))[0]
        .def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let run_scheme = def_scheme(&output, run);
    assert!(run_scheme.stack_quantifiers.is_empty());
    let run_boundary = extract_real_run_boundary(&output.session.poly.typ, run_scheme.predicate);

    let callback_ref = assert_flat_real_run_two_step_application(&output, with_ref, run);
    assert_callback_call_uses_bare_return_effect(&output, callback_ref);
    assert_no_helper_owned_stack_source(
        output.session.infer.constraints().types(),
        &run_boundary.family_path,
    );

    let helper_scheme = def_scheme(&output, with_ref);
    let first_scheme = def_scheme(&output, first);
    let second_scheme = def_scheme(&output, second);
    for (label, scheme) in [
        ("separate helper", helper_scheme),
        ("first caller", first_scheme),
        ("second caller", second_scheme),
    ] {
        assert!(
            scheme.stack_quantifiers.is_empty(),
            "{label} must not retain a raw subtraction owner"
        );
    }

    assert_resolved_helper_two_step_application(&output, first, with_ref);
    assert_resolved_helper_two_step_application(&output, second, with_ref);

    let helper_boundary =
        extract_real_run_helper_boundary(&output.session.poly.typ, helper_scheme.predicate);
    let first_boundary =
        extract_real_run_helper_boundary(&output.session.poly.typ, first_scheme.predicate);
    let second_boundary =
        extract_real_run_helper_boundary(&output.session.poly.typ, second_scheme.predicate);
    assert_eq!(helper_boundary.family_path, run_boundary.family_path);
    assert_eq!(first_boundary.family_path, helper_boundary.family_path);
    assert_eq!(second_boundary.family_path, helper_boundary.family_path);
    assert_ne!(helper_boundary.payload, run_boundary.payload);
    assert_ne!(helper_boundary.residual, run_boundary.residual);
    assert_ne!(first_boundary.payload, helper_boundary.payload);
    assert_ne!(first_boundary.residual, helper_boundary.residual);
    assert_ne!(second_boundary.payload, helper_boundary.payload);
    assert_ne!(second_boundary.residual, helper_boundary.residual);
    assert_ne!(first_boundary.payload, second_boundary.payload);
    assert_ne!(first_boundary.residual, second_boundary.residual);
}

#[test]
fn concrete_callback_application_discharge_reaches_enclosing_generalized_scheme() {
    let root = parse(concat!(
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
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (trigger, _) = binding_def_and_order(&lower.modules, module, "trigger");
    let local_var_act = lower.modules.synthetic_var_act_uses(trigger)[0].clone();
    let local_var_companion = lower.modules.type_companion(local_var_act.act).unwrap();
    let run = lower
        .modules
        .value_decls(local_var_companion, &Name("run".into()))[0]
        .def;
    let with_ref = lower
        .modules
        .value_decls(local_var_companion, &Name("with_ref".into()))[0]
        .def;
    let enclosing = lower
        .modules
        .value_decls(local_var_companion, &Name("enclosing".into()))[0]
        .def;
    assert!(
        lower.modules.synthetic_var_act_uses(enclosing).is_empty(),
        "the concrete caller must stay at the same primitive layer as the corrected LVB-A3 helper"
    );

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let run_scheme = def_scheme(&output, run);
    let run_boundary = extract_real_run_boundary(&output.session.poly.typ, run_scheme.predicate);
    let callback_body =
        assert_concrete_callback_enclosing_application(&output, enclosing, with_ref);
    assert!(
        find_select_by_name(&output.session, callback_body, "get").is_some(),
        "the concrete callback must actually read through its ref argument"
    );
    assert!(
        find_select_by_name(&output.session, callback_body, "update").is_some(),
        "the concrete callback must actually update through its ref argument"
    );

    let enclosing_scheme = def_scheme(&output, enclosing);
    assert!(
        output
            .session
            .generalized_scheme_record(enclosing)
            .is_some(),
        "the enclosing definition must pass through ordinary generalization"
    );
    assert!(
        enclosing_scheme.stack_quantifiers.is_empty(),
        "the enclosing finalized scheme must not retain a raw subtraction owner"
    );
    assert_enclosing_observe_only_scheme(
        &output.session.poly.typ,
        enclosing_scheme,
        &[&run_boundary.family_path],
    );
}

#[test]
fn nested_concrete_callback_boundaries_discharge_both_families_from_outer_scheme() {
    let root = parse(concat!(
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
        "my trigger = 0\n",
    ));
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let std = lower.modules.module_decls(root_module, &Name("std".into()))[0].module;
    let control = lower.modules.module_decls(std, &Name("control".into()))[0].module;
    let var = lower.modules.module_decls(control, &Name("var".into()))[0].module;
    let inner_act = lower.modules.type_decls(var, &Name("inner_var".into()))[0].id;
    let outer_act = lower.modules.type_decls(var, &Name("outer_var".into()))[0].id;
    let inner_companion = lower.modules.type_companion(inner_act).unwrap();
    let outer_companion = lower.modules.type_companion(outer_act).unwrap();
    let inner_run = lower
        .modules
        .value_decls(inner_companion, &Name("run".into()))[0]
        .def;
    let inner_helper = lower
        .modules
        .value_decls(inner_companion, &Name("with_ref".into()))[0]
        .def;
    let inner_enclosing = lower
        .modules
        .value_decls(inner_companion, &Name("enclosing".into()))[0]
        .def;
    let outer_run = lower
        .modules
        .value_decls(outer_companion, &Name("run".into()))[0]
        .def;
    let outer_helper = lower
        .modules
        .value_decls(outer_companion, &Name("with_ref".into()))[0]
        .def;
    let outer_enclosing = lower
        .modules
        .value_decls(outer_companion, &Name("enclosing".into()))[0]
        .def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let inner_boundary = extract_real_run_boundary(
        &output.session.poly.typ,
        def_scheme(&output, inner_run).predicate,
    );
    let outer_boundary = extract_real_run_boundary(
        &output.session.poly.typ,
        def_scheme(&output, outer_run).predicate,
    );
    assert_ne!(
        inner_boundary.family_path, outer_boundary.family_path,
        "the nested witness must use two distinct local families"
    );

    let inner_callback =
        assert_concrete_callback_enclosing_application(&output, inner_enclosing, inner_helper);
    let outer_callback =
        assert_concrete_callback_enclosing_application(&output, outer_enclosing, outer_helper);
    for (label, callback) in [
        ("inner callback", inner_callback),
        ("outer callback", outer_callback),
    ] {
        assert!(
            find_select_by_name(&output.session, callback, "get").is_some(),
            "{label} must actually read through its ref argument"
        );
        assert!(
            find_select_by_name(&output.session, callback, "update").is_some(),
            "{label} must actually update through its ref argument"
        );
    }

    for (label, enclosing) in [
        ("inner enclosing definition", inner_enclosing),
        ("outer enclosing definition", outer_enclosing),
    ] {
        let scheme = def_scheme(&output, enclosing);
        assert!(
            output
                .session
                .generalized_scheme_record(enclosing)
                .is_some(),
            "{label} must pass through ordinary generalization"
        );
        assert!(
            scheme.stack_quantifiers.is_empty(),
            "{label} must not retain a raw subtraction owner"
        );
        assert_enclosing_observe_only_scheme(
            &output.session.poly.typ,
            scheme,
            &[&inner_boundary.family_path, &outer_boundary.family_path],
        );
    }
}

#[test]
fn duplicate_callback_stack_control_reproduces_empty_set_same_id_collision() {
    let id = SubtractId(0);
    let run_owned_empty = LeftConstraintWeight::push(id, Subtractability::Empty);
    let callback_owned_set =
        LeftConstraintWeight::push(id, Subtractability::Set(family_path(), vec![NeuId(0)]));

    let collision = std::panic::catch_unwind(|| run_owned_empty.compose(&callback_owned_set))
        .expect_err("Empty and Set on one SubtractId must hit stop condition 6");
    let message = panic_message(collision);
    assert!(message.contains("one stack id must not use multiple families"));
    assert!(message.contains("Empty"));
    assert!(message.contains("Set"));
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RealRunBoundary {
    family_path: Vec<String>,
    payload: TypeVar,
    residual: TypeVar,
}

fn extract_real_run_boundary(types: &TypeArena, predicate: PosId) -> RealRunBoundary {
    let Pos::Fun {
        arg: init,
        ret: run_with_init,
        ..
    } = types.pos(predicate)
    else {
        panic!("run must take init first");
    };
    let Neg::Var(init) = types.neg(*init) else {
        panic!("run init must be an ordinary payload variable");
    };
    let Pos::Fun {
        arg: computation_result,
        arg_eff: computation_effect,
        ret_eff: result_effect,
        ret: result,
    } = types.pos(*run_with_init)
    else {
        panic!("run must take the handled computation second");
    };
    let Neg::Var(computation_result) = types.neg(*computation_result) else {
        panic!("run computation result must be an ordinary variable");
    };
    let Pos::Var(result) = types.pos(*result) else {
        panic!("run result must preserve the computation value");
    };
    assert_eq!(computation_result, result);

    let (family_path, family_payload, residual) =
        negative_single_family_row(types, *computation_effect);
    let Pos::Var(result_residual) = types.pos(*result_effect) else {
        panic!("run result effect must be the ordinary residual rho");
    };
    assert_eq!(
        residual, *result_residual,
        "run input tail and result effect must share rho"
    );
    assert_eq!(
        *init, family_payload,
        "run init P and handled family F(P) must preserve the invariant payload"
    );

    RealRunBoundary {
        family_path,
        payload: *init,
        residual,
    }
}

fn extract_real_run_helper_boundary(types: &TypeArena, predicate: PosId) -> RealRunBoundary {
    let Pos::Fun {
        arg: init,
        ret: with_init,
        ..
    } = types.pos(predicate)
    else {
        panic!("helper must take init first");
    };
    let Neg::Var(init) = types.neg(*init) else {
        panic!("helper init must be an ordinary payload variable");
    };
    let Pos::Fun {
        arg: callback,
        ret_eff: helper_effect,
        ret: helper_result,
        ..
    } = types.pos(*with_init)
    else {
        panic!("helper must take callback second");
    };
    let Neg::Fun {
        arg: callback_arg,
        ret_eff: callback_effect,
        ret: callback_result,
        ..
    } = types.neg(*callback)
    else {
        panic!("helper callback must be callable");
    };
    let Neg::Var(callback_result) = types.neg(*callback_result) else {
        panic!("callback result must be an ordinary result variable");
    };
    let Pos::Var(helper_result) = types.pos(*helper_result) else {
        panic!("helper result must be an ordinary result variable");
    };
    assert_eq!(
        callback_result, helper_result,
        "callback and helper must preserve the same result R"
    );
    let (family_path, family_payload, residual) =
        negative_single_family_row(types, *callback_effect);
    let Pos::Var(helper_residual) = types.pos(*helper_effect) else {
        panic!("helper result effect must be the ordinary residual rho");
    };
    assert_eq!(
        residual, *helper_residual,
        "callback row tail and helper result must share rho"
    );
    assert_eq!(*init, family_payload);

    let Pos::Con(ref_path, ref_args) = types.pos(*callback_arg) else {
        panic!("callback must receive the local ref capability");
    };
    assert_eq!(ref_path, &crate::std_paths::control_var_ref_type());
    assert_eq!(ref_args.len(), 2);
    assert_eq!(
        invariant_var(types, ref_args[1]),
        *init,
        "ref payload and handled family payload must be the same invariant P"
    );
    let Neu::Bounds(ref_effect_lower, _) = types.neu(ref_args[0]) else {
        panic!("ref effect must retain structural bounds");
    };
    let Pos::Row(ref_effect_items) = types.pos(*ref_effect_lower) else {
        panic!("ref effect lower must be the concrete F(P) row");
    };
    let [ref_effect_item] = ref_effect_items.as_slice() else {
        panic!("ref effect must contain exactly one local family");
    };
    let Pos::Con(ref_family_path, ref_family_args) = types.pos(*ref_effect_item) else {
        panic!("ref effect item must be the local family constructor");
    };
    assert_eq!(ref_family_path, &family_path);
    let [ref_family_payload] = ref_family_args.as_slice() else {
        panic!("local family must carry its payload");
    };
    assert_eq!(invariant_var(types, *ref_family_payload), *init);

    RealRunBoundary {
        family_path,
        payload: *init,
        residual,
    }
}

fn negative_single_family_row(types: &TypeArena, effect: NegId) -> (Vec<String>, TypeVar, TypeVar) {
    let Neg::Row(items, tail) = types.neg(effect) else {
        panic!(
            "effect must be a concrete F(P) prefix with an ordinary tail, got {:?}",
            types.neg(effect)
        );
    };
    let [item] = items.as_slice() else {
        panic!("effect row must contain exactly one handled family");
    };
    let Neg::Con(path, args) = types.neg(*item) else {
        panic!("effect row item must be a family constructor");
    };
    let [payload] = args.as_slice() else {
        panic!("handled family must carry one payload");
    };
    let payload = invariant_var(types, *payload);
    let Neg::Var(residual) = types.neg(*tail) else {
        panic!("effect row must keep an ordinary residual tail");
    };
    (path.clone(), payload, *residual)
}

fn assert_real_run_two_step_application(output: &BodyLowering, helper: DefId, run: DefId) -> RefId {
    let (callback, helper_body) = helper_callback_and_body(output, helper);
    let Expr::Block(_, Some(after_init)) = output.session.poly.expr(helper_body) else {
        panic!("local var lowering must introduce its init block");
    };
    let Expr::Block(_, Some(wrapped)) = output.session.poly.expr(*after_init) else {
        panic!("local var lowering must introduce its ref block");
    };
    assert_run_application(output, *wrapped, callback, run)
}

fn assert_flat_real_run_two_step_application(
    output: &BodyLowering,
    helper: DefId,
    run: DefId,
) -> RefId {
    let (callback, helper_body) = helper_callback_and_body(output, helper);
    assert!(
        matches!(output.session.poly.expr(helper_body), Expr::App(_, _)),
        "the copied helper must directly contain the flat run application"
    );
    assert_run_application(output, helper_body, callback, run)
}

fn helper_callback_and_body(output: &BodyLowering, helper: DefId) -> (DefId, ExprId) {
    let Expr::Lambda(_, helper_after_init) =
        output.session.poly.expr(binding_body_id(output, helper))
    else {
        panic!("helper must lower init as its first lambda");
    };
    let Expr::Lambda(callback_pat, helper_body) = output.session.poly.expr(*helper_after_init)
    else {
        panic!("helper must lower callback as its second lambda");
    };
    let Pat::Var(callback) = output.session.poly.pat(*callback_pat) else {
        panic!("callback parameter must be a local definition");
    };
    (*callback, *helper_body)
}

fn assert_run_application(
    output: &BodyLowering,
    application: ExprId,
    callback: DefId,
    run: DefId,
) -> RefId {
    let Expr::App(run_with_init, callback_call) = output.session.poly.expr(application) else {
        panic!("wrapper must apply run to the callback computation");
    };
    let Expr::App(run_ref, _) = output.session.poly.expr(*run_with_init) else {
        panic!("wrapper must apply run to init first");
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, *run_ref)),
        Some(run),
        "the first callee must be a resolved ref to the generalized synthetic run definition"
    );
    let Expr::App(callback_ref, _) = output.session.poly.expr(*callback_call) else {
        panic!("run's second argument must be callback var_ref()");
    };
    let callback_ref = expr_ref(&output.session, *callback_ref);
    assert_eq!(output.session.poly.ref_target(callback_ref), Some(callback));
    callback_ref
}

fn assert_resolved_helper_two_step_application(
    output: &BodyLowering,
    caller: DefId,
    helper: DefId,
) {
    let Expr::Lambda(_, caller_after_init) =
        output.session.poly.expr(binding_body_id(output, caller))
    else {
        panic!("caller must lower init as its first lambda");
    };
    let Expr::Lambda(_, caller_body) = output.session.poly.expr(*caller_after_init) else {
        panic!("caller must lower callback as its second lambda");
    };
    let Expr::App(helper_with_init, _) = output.session.poly.expr(*caller_body) else {
        panic!("caller must apply the separate helper to callback second");
    };
    let Expr::App(helper_ref, _) = output.session.poly.expr(*helper_with_init) else {
        panic!("caller must apply the separate helper to init first");
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, *helper_ref)),
        Some(helper),
        "caller must use a normally resolved reference to the separate helper definition"
    );
}

fn assert_concrete_callback_enclosing_application(
    output: &BodyLowering,
    enclosing: DefId,
    helper: DefId,
) -> ExprId {
    let Expr::Lambda(_, enclosing_body) =
        output.session.poly.expr(binding_body_id(output, enclosing))
    else {
        panic!("enclosing definition must lower its init parameter as a lambda");
    };
    let Expr::App(helper_with_init, callback) = output.session.poly.expr(*enclosing_body) else {
        panic!("enclosing body must apply the helper to the concrete callback second");
    };
    let Expr::App(helper_ref, _) = output.session.poly.expr(*helper_with_init) else {
        panic!("enclosing body must apply the helper to init first");
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, *helper_ref)),
        Some(helper),
        "enclosing body must resolve and instantiate the separate helper definition"
    );
    let Expr::Lambda(callback_param, callback_body) = output.session.poly.expr(*callback) else {
        panic!("helper caller must supply a concrete callback lambda");
    };
    assert!(
        matches!(output.session.poly.pat(*callback_param), Pat::Var(_)),
        "the concrete callback must bind the ref capability it actually uses"
    );
    *callback_body
}

fn assert_enclosing_observe_only_scheme(
    types: &TypeArena,
    scheme: &poly::types::Scheme,
    local_family_paths: &[&[String]],
) {
    assert!(
        scheme.role_predicates.is_empty() && scheme.recursive_bounds.is_empty(),
        "the simple enclosing witness must keep its complete effect structure in the predicate"
    );
    let Pos::Fun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    } = types.pos(scheme.predicate)
    else {
        panic!("enclosing scheme must be a function");
    };
    let Neg::Var(input) = types.neg(*arg) else {
        panic!("enclosing input must remain an ordinary payload variable");
    };
    assert!(
        matches!(types.neg(*arg_eff), Neg::Bot),
        "evaluating the enclosing function argument must stay pure"
    );
    let Pos::Row(effect_items) = types.pos(*ret_eff) else {
        panic!(
            "enclosing result effect must finalize as the ordinary observe row, got {:?}",
            types.pos(*ret_eff)
        );
    };
    let [effect_item] = effect_items.as_slice() else {
        panic!("enclosing result effect must contain only the ordinary observe family");
    };
    let Pos::Con(effect_path, effect_args) = types.pos(*effect_item) else {
        panic!("enclosing ordinary residual effect must be a concrete family");
    };
    assert_eq!(effect_path, &observe_path());
    for local_family_path in local_family_paths {
        assert_ne!(
            effect_path, local_family_path,
            "a concrete local family F(P) must not leak into the enclosing finalized scheme"
        );
    }
    let [effect_payload] = effect_args.as_slice() else {
        panic!("the ordinary observe family must retain its payload");
    };
    assert_eq!(
        invariant_var(types, *effect_payload),
        *input,
        "the ordinary residual effect must retain the enclosing payload"
    );
    let Pos::Var(result) = types.pos(*ret) else {
        panic!("the concrete callback must produce an ordinary result value");
    };
    assert_eq!(
        result, input,
        "the enclosing result must be produced from the concrete callback's ref read"
    );
}

fn assert_callback_call_uses_bare_return_effect(output: &BodyLowering, callback: RefId) {
    let callback = output
        .session
        .refs
        .value(callback)
        .expect("callback reference use type");
    let bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(callback)
        .expect("callback should have callable upper bounds");
    let types = output.session.infer.constraints().types();
    let ret_effects = bounds
        .uppers()
        .iter()
        .filter_map(|bound| match types.neg(bound.neg) {
            Neg::Fun { ret_eff, .. } => Some(*ret_eff),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(!ret_effects.is_empty());
    assert!(
        ret_effects
            .iter()
            .any(|effect| matches!(types.neg(*effect), Neg::Var(_))),
        "the resolved callback call must start from a bare fresh return-effect variable"
    );
    assert!(
        ret_effects
            .iter()
            .all(|effect| !matches!(types.neg(*effect), Neg::Stack { .. })),
        "the callback call must not enter the generic unannotated Empty stack path"
    );
}

fn assert_no_helper_owned_stack_source(types: &TypeArena, family_path: &[String]) {
    let family_ids = types
        .pos_nodes()
        .iter()
        .filter_map(|node| match node {
            Pos::Stack { weight, .. } | Pos::NonSubtract(_, weight) => Some(weight),
            _ => None,
        })
        .chain(types.neg_nodes().iter().filter_map(|node| match node {
            Neg::Stack { weight, .. } => Some(weight),
            _ => None,
        }))
        .flat_map(|weight| weight.entries())
        .filter(|entry| {
            entry.stack.iter().any(
                |family| matches!(family, Subtractability::Set(path, _) if path == family_path),
            )
        })
        .map(|entry| entry.id)
        .collect::<FxHashSet<_>>();
    assert!(
        family_ids.is_empty(),
        "the finalized run row must reach the helper without a helper-owned family stack ID"
    );
}

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    match payload.downcast::<String>() {
        Ok(message) => *message,
        Err(payload) => payload
            .downcast::<&'static str>()
            .map(|message| (*message).to_string())
            .unwrap_or_else(|_| "<non-string panic>".into()),
    }
}

struct NegativeCallbackBoundaryWitness {
    machine: ConstraintMachine,
    root: TypeVar,
    callback_ret_eff: NegId,
    ref_effect_bounds: NeuId,
    payload: TypeVar,
    residual: TypeVar,
    family_args: Vec<NeuId>,
    subtract: SubtractId,
}

struct DirectRowControlWitness {
    machine: ConstraintMachine,
    root: TypeVar,
    ref_effect_bounds: NeuId,
    callback_residual: TypeVar,
    helper_residual: TypeVar,
}

fn negative_callback_boundary_witness(payload_bearing: bool) -> NegativeCallbackBoundaryWitness {
    let mut machine = ConstraintMachine::new();
    let root = TypeVar(0);
    let payload = TypeVar(1);
    let residual = TypeVar(2);
    let result = TypeVar(3);
    for var in [root, payload, residual, result] {
        machine.register_type_var(var, TypeLevel::root().child());
    }

    let payload_lower = machine.alloc_pos(Pos::Var(payload));
    let payload_upper = machine.alloc_neg(Neg::Var(payload));
    let payload_bounds = machine.alloc_neu(Neu::Bounds(payload_lower, payload_upper));
    let family_args = payload_bearing
        .then_some(payload_bounds)
        .into_iter()
        .collect::<Vec<_>>();

    let family_path = family_path();
    let ref_effect_lower_item =
        machine.alloc_pos(Pos::Con(family_path.clone(), family_args.clone()));
    let ref_effect_lower = machine.alloc_pos(Pos::Row(vec![ref_effect_lower_item]));
    let ref_effect_upper_item =
        machine.alloc_neg(Neg::Con(family_path.clone(), family_args.clone()));
    let ref_effect_upper_tail = machine.alloc_neg(Neg::Bot);
    let ref_effect_upper =
        machine.alloc_neg(Neg::Row(vec![ref_effect_upper_item], ref_effect_upper_tail));
    let ref_effect_bounds = machine.alloc_neu(Neu::Bounds(ref_effect_lower, ref_effect_upper));

    let callback_arg = machine.alloc_pos(Pos::Con(
        ref_path(),
        vec![ref_effect_bounds, payload_bounds],
    ));
    let callback_arg_eff = machine.alloc_pos(Pos::Bot);
    let callback_ret_eff_tail = machine.alloc_neg(Neg::Var(residual));
    let subtract = SubtractId(0);
    let family = Subtractability::Set(family_path, family_args.clone());
    let callback_ret_eff = machine.alloc_neg(Neg::Stack {
        inner: callback_ret_eff_tail,
        weight: StackWeight::push(subtract, family),
    });
    let callback_ret = machine.alloc_neg(Neg::Var(result));
    let callback = machine.alloc_neg(Neg::Fun {
        arg: callback_arg,
        arg_eff: callback_arg_eff,
        ret_eff: callback_ret_eff,
        ret: callback_ret,
    });

    let helper_arg_eff = machine.alloc_neg(Neg::Bot);
    let helper_ret_eff = machine.alloc_pos(Pos::Var(residual));
    let helper_ret = machine.alloc_pos(Pos::Var(result));
    let helper = machine.alloc_pos(Pos::Fun {
        arg: callback,
        arg_eff: helper_arg_eff,
        ret_eff: helper_ret_eff,
        ret: helper_ret,
    });
    let root_upper = machine.alloc_neg(Neg::Var(root));
    machine.subtype(helper, root_upper, OriginId::unknown_internal());

    NegativeCallbackBoundaryWitness {
        machine,
        root,
        callback_ret_eff,
        ref_effect_bounds,
        payload,
        residual,
        family_args,
        subtract,
    }
}

#[test]
fn negative_callback_boundary_materializes_payload_family_and_shared_residual() {
    let mut witness = negative_callback_boundary_witness(true);
    let expected_family = Subtractability::Set(family_path(), witness.family_args.clone());

    let Neg::Stack { inner, weight } = witness.machine.types().neg(witness.callback_ret_eff) else {
        panic!("callback ret_eff should be a negative stack");
    };
    assert_eq!(
        witness.machine.types().neg(*inner),
        &Neg::Var(witness.residual)
    );
    assert_eq!(
        weight,
        &StackWeight::push(witness.subtract, expected_family)
    );
    assert_precompact_ref_effect_is_exact_direct_row(
        witness.machine.types(),
        witness.ref_effect_bounds,
        true,
    );

    let compact = compact_type_var_for_scheme(&mut witness.machine, witness.root);
    let (callback, helper) = compact_callback_and_helper(&compact);
    let row =
        callback.ret_eff.rows.first().unwrap_or_else(|| {
            panic!("callback ret_eff should contain a concrete row: {compact:?}")
        });
    let payload_args = row
        .items
        .get(&family_path())
        .unwrap_or_else(|| panic!("callback ret_eff should materialize F(P): {compact:?}"));
    assert_eq!(payload_args.len(), 1, "{compact:?}");
    assert!(
        compact_contains_plain_var(&row.tail, witness.residual),
        "callback row tail should retain rho: {compact:?}"
    );
    assert!(
        compact_contains_plain_var(&helper.ret_eff, witness.residual),
        "helper result effect should retain the same rho: {compact:?}"
    );

    let generalized = generalize_compact_root(
        &mut witness.machine,
        TypeLevel::root(),
        compact,
        &FxHashSet::default(),
    );
    assert!(
        generalized.stack_quantifiers.is_empty(),
        "materialized callback prefixes must not retain raw stack binders: {generalized:?}"
    );
    let mut scheme_types = TypeArena::new();
    let finalized =
        finalize_generalized_compact_root(&mut scheme_types, &witness.machine, &generalized);
    assert!(finalized.scheme.stack_quantifiers.is_empty());

    let finalized_vars = extract_boundary_instance(&scheme_types, finalized.scheme.predicate, true);
    assert_eq!(finalized_vars.residual, witness.residual);
    assert_eq!(finalized_vars.payload, Some(witness.payload));
    assert!(finalized.scheme.quantifiers.contains(&witness.residual));
    assert!(finalized.scheme.quantifiers.contains(&witness.payload));

    let mut instances = crate::arena::Arena::new();
    let first = instantiate_scheme(
        &scheme_types,
        &mut instances,
        TypeLevel::root(),
        &finalized.scheme,
    );
    let second = instantiate_scheme(
        &scheme_types,
        &mut instances,
        TypeLevel::root(),
        &finalized.scheme,
    );
    let first_vars = extract_boundary_instance(instances.constraints().types(), first, true);
    let second_vars = extract_boundary_instance(instances.constraints().types(), second, true);

    assert_ne!(first_vars.residual, witness.residual);
    assert_ne!(second_vars.residual, witness.residual);
    assert_ne!(first_vars.residual, second_vars.residual);
    assert_ne!(first_vars.payload, second_vars.payload);
}

#[test]
fn negative_callback_boundary_materializes_argumentless_family_through_same_path() {
    let mut witness = negative_callback_boundary_witness(false);
    let expected_family = Subtractability::Set(family_path(), Vec::new());
    let Neg::Stack { inner, weight } = witness.machine.types().neg(witness.callback_ret_eff) else {
        panic!("callback ret_eff should be a negative stack");
    };
    assert_eq!(
        witness.machine.types().neg(*inner),
        &Neg::Var(witness.residual)
    );
    assert_eq!(
        weight,
        &StackWeight::push(witness.subtract, expected_family)
    );
    assert_precompact_ref_effect_is_exact_direct_row(
        witness.machine.types(),
        witness.ref_effect_bounds,
        false,
    );

    let compact = compact_type_var_for_scheme(&mut witness.machine, witness.root);
    let (callback, helper) = compact_callback_and_helper(&compact);
    let row =
        callback.ret_eff.rows.first().unwrap_or_else(|| {
            panic!("callback ret_eff should contain a concrete row: {compact:?}")
        });
    assert_eq!(
        row.items
            .get(&family_path())
            .unwrap_or_else(|| panic!("callback ret_eff should materialize F: {compact:?}"))
            .len(),
        0
    );
    assert!(compact_contains_plain_var(&row.tail, witness.residual));
    assert!(compact_contains_plain_var(
        &helper.ret_eff,
        witness.residual
    ));

    let generalized = generalize_compact_root(
        &mut witness.machine,
        TypeLevel::root(),
        compact,
        &FxHashSet::default(),
    );
    assert!(generalized.stack_quantifiers.is_empty());
    let mut scheme_types = TypeArena::new();
    let finalized =
        finalize_generalized_compact_root(&mut scheme_types, &witness.machine, &generalized);
    assert!(finalized.scheme.stack_quantifiers.is_empty());
    let finalized_vars =
        extract_boundary_instance(&scheme_types, finalized.scheme.predicate, false);
    assert_eq!(finalized_vars.residual, witness.residual);
    assert_eq!(finalized_vars.payload, None);

    let mut instances = crate::arena::Arena::new();
    let first = instantiate_scheme(
        &scheme_types,
        &mut instances,
        TypeLevel::root(),
        &finalized.scheme,
    );
    let second = instantiate_scheme(
        &scheme_types,
        &mut instances,
        TypeLevel::root(),
        &finalized.scheme,
    );
    let first_vars = extract_boundary_instance(instances.constraints().types(), first, false);
    let second_vars = extract_boundary_instance(instances.constraints().types(), second, false);
    assert_ne!(first_vars.residual, second_vars.residual);
}

#[test]
fn invariant_direct_row_push_only_control_does_not_create_residual_correspondence() {
    let mut witness = direct_row_control_witness();
    assert_precompact_ref_effect_contains_push_only_carrier(
        witness.machine.types(),
        witness.ref_effect_bounds,
    );
    let compact = compact_type_var_for_scheme(&mut witness.machine, witness.root);
    let (callback, helper) = compact_callback_and_helper(&compact);

    let ref_effect = compact_ref_effect_bounds(callback);
    let CompactBounds::Interval { lower, upper } = ref_effect else {
        panic!("ref effect argument should compact as invariant bounds: {compact:?}");
    };
    assert!(
        compact_has_family_row(lower),
        "the old direct [F(P)] lower itself should survive compact: {compact:?}"
    );
    assert!(
        compact_has_family_row(upper),
        "the old direct [F(P)] upper itself should survive compact: {compact:?}"
    );
    assert!(
        !compact_has_family_row(&callback.ret_eff),
        "push-only ref evidence must not materialize F(P) on callback ret_eff: {compact:?}"
    );
    assert!(
        compact_contains_plain_var(&callback.ret_eff, witness.callback_residual),
        "callback residual should remain structurally observable: {compact:?}"
    );
    assert!(
        compact_contains_plain_var(&helper.ret_eff, witness.helper_residual),
        "helper residual should remain structurally observable: {compact:?}"
    );
    assert_ne!(
        witness.callback_residual, witness.helper_residual,
        "the old carrier supplies no ordinary callback/result rho correspondence"
    );
}

fn direct_row_control_witness() -> DirectRowControlWitness {
    let mut machine = ConstraintMachine::new();
    let root = TypeVar(0);
    let payload = TypeVar(1);
    let callback_residual = TypeVar(2);
    let helper_residual = TypeVar(3);
    let result = TypeVar(4);
    for var in [root, payload, callback_residual, helper_residual, result] {
        machine.register_type_var(var, TypeLevel::root().child());
    }

    let payload_lower = machine.alloc_pos(Pos::Var(payload));
    let payload_upper = machine.alloc_neg(Neg::Var(payload));
    let payload_bounds = machine.alloc_neu(Neu::Bounds(payload_lower, payload_upper));
    let family_args = vec![payload_bounds];
    let family = Subtractability::Set(family_path(), family_args.clone());
    let lower_item = machine.alloc_pos(Pos::Con(family_path(), family_args.clone()));
    let lower_row = machine.alloc_pos(Pos::Row(vec![lower_item]));
    let lower_with_push = machine.alloc_pos(Pos::Stack {
        inner: lower_row,
        weight: StackWeight::push(SubtractId(0), family),
    });
    let upper_item = machine.alloc_neg(Neg::Con(family_path(), family_args));
    let upper_tail = machine.alloc_neg(Neg::Bot);
    let upper_row = machine.alloc_neg(Neg::Row(vec![upper_item], upper_tail));
    let ref_effect_bounds = machine.alloc_neu(Neu::Bounds(lower_with_push, upper_row));

    let callback_arg = machine.alloc_pos(Pos::Con(
        ref_path(),
        vec![ref_effect_bounds, payload_bounds],
    ));
    let callback_arg_eff = machine.alloc_pos(Pos::Bot);
    let callback_ret_eff = machine.alloc_neg(Neg::Var(callback_residual));
    let callback_ret = machine.alloc_neg(Neg::Var(result));
    let callback = machine.alloc_neg(Neg::Fun {
        arg: callback_arg,
        arg_eff: callback_arg_eff,
        ret_eff: callback_ret_eff,
        ret: callback_ret,
    });
    let helper_arg_eff = machine.alloc_neg(Neg::Bot);
    let helper_ret_eff = machine.alloc_pos(Pos::Var(helper_residual));
    let helper_ret = machine.alloc_pos(Pos::Var(result));
    let helper = machine.alloc_pos(Pos::Fun {
        arg: callback,
        arg_eff: helper_arg_eff,
        ret_eff: helper_ret_eff,
        ret: helper_ret,
    });
    let root_upper = machine.alloc_neg(Neg::Var(root));
    machine.subtype(helper, root_upper, OriginId::unknown_internal());

    DirectRowControlWitness {
        machine,
        root,
        ref_effect_bounds,
        callback_residual,
        helper_residual,
    }
}

#[test]
fn callback_contract_metadata_exposes_only_the_concrete_payload_family() {
    let root = parse(concat!(
        "act local_state 'p;\n",
        "my h(f: _ -> [local_state int; 'e] _) = f 0\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let param = first_lambda_param_def(&output, h);
    let contract = output
        .session
        .poly
        .arg_effect_contracts
        .get(&param)
        .expect("callback parameter should retain its explicit effect contract");
    assert_eq!(
        contract.markers,
        vec![poly::expr::ArgEffectContractMarker {
            path: vec!["local_state".into()],
            depth: 1,
            resume: poly::expr::ContractResumePolicy::PreserveMatchingPath,
        }],
        "the concrete F(P), but not ambient rho, is visible to the handler contract"
    );
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BoundaryInstance {
    residual: TypeVar,
    payload: Option<TypeVar>,
}

fn extract_boundary_instance(
    types: &TypeArena,
    predicate: PosId,
    payload_bearing: bool,
) -> BoundaryInstance {
    let Pos::Fun {
        arg: callback,
        ret_eff: helper_ret_eff,
        ..
    } = types.pos(predicate)
    else {
        panic!("expected helper function, got {:?}", types.pos(predicate));
    };
    let Neg::Fun {
        arg: callback_arg,
        ret_eff: callback_ret_eff,
        ..
    } = types.neg(*callback)
    else {
        panic!("expected callback function, got {:?}", types.neg(*callback));
    };
    let Neg::Row(items, tail) = types.neg(*callback_ret_eff) else {
        panic!(
            "callback ret_eff should finalize as a concrete row, got {:?}",
            types.neg(*callback_ret_eff)
        );
    };
    let family_args = items
        .iter()
        .find_map(|item| match types.neg(*item) {
            Neg::Con(path, args) if path == &family_path() => Some(args),
            _ => None,
        })
        .unwrap_or_else(|| panic!("callback row should contain F(P)"));
    let Neg::Var(callback_residual) = types.neg(*tail) else {
        panic!("callback row should retain an ordinary residual tail");
    };
    let Pos::Var(helper_residual) = types.pos(*helper_ret_eff) else {
        panic!("helper result should retain an ordinary residual");
    };
    assert_eq!(
        callback_residual, helper_residual,
        "callback and helper result must share the same structural rho"
    );

    let Pos::Con(path, ref_args) = types.pos(*callback_arg) else {
        panic!("callback argument should be the exact ref capability");
    };
    assert_eq!(path, &ref_path());
    assert_eq!(ref_args.len(), 2);
    assert_exact_ref_effect(types, ref_args[0], payload_bearing);
    let ref_payload = invariant_var(types, ref_args[1]);

    let payload = if payload_bearing {
        assert_eq!(family_args.len(), 1);
        let family_payload = invariant_var(types, family_args[0]);
        assert_eq!(
            family_payload, ref_payload,
            "F(P) and ref payload must preserve the same invariant P"
        );
        Some(family_payload)
    } else {
        assert!(family_args.is_empty());
        None
    };

    BoundaryInstance {
        residual: *callback_residual,
        payload,
    }
}

fn assert_exact_ref_effect(types: &TypeArena, bounds: NeuId, payload_bearing: bool) {
    let Neu::Bounds(lower, upper) = types.neu(bounds) else {
        panic!("ref effect argument should remain invariant bounds");
    };
    let Pos::Row(lower_items) = types.pos(*lower) else {
        panic!("ref effect lower should remain an exact direct row");
    };
    let Neg::Row(upper_items, upper_tail) = types.neg(*upper) else {
        panic!("ref effect upper should remain an exact direct row");
    };
    assert_eq!(lower_items.len(), 1);
    assert_eq!(upper_items.len(), 1);
    assert!(matches!(types.neg(*upper_tail), Neg::Bot));

    let Pos::Con(lower_path, lower_args) = types.pos(lower_items[0]) else {
        panic!("ref effect lower row should contain F(P)");
    };
    let Neg::Con(upper_path, upper_args) = types.neg(upper_items[0]) else {
        panic!("ref effect upper row should contain F(P)");
    };
    assert_eq!(lower_path, &family_path());
    assert_eq!(upper_path, &family_path());
    assert_eq!(lower_args.len(), usize::from(payload_bearing));
    assert_eq!(upper_args.len(), usize::from(payload_bearing));
    if payload_bearing {
        assert_eq!(
            invariant_var(types, lower_args[0]),
            invariant_var(types, upper_args[0])
        );
    }
}

fn invariant_var(types: &TypeArena, bounds: NeuId) -> TypeVar {
    let Neu::Bounds(lower, upper) = types.neu(bounds) else {
        panic!("expected invariant bounds");
    };
    let Pos::Var(lower) = types.pos(*lower) else {
        panic!("expected invariant variable lower");
    };
    let Neg::Var(upper) = types.neg(*upper) else {
        panic!("expected invariant variable upper");
    };
    assert_eq!(lower, upper);
    *lower
}

fn assert_precompact_ref_effect_is_exact_direct_row(
    types: &TypeArena,
    bounds: NeuId,
    payload_bearing: bool,
) {
    let Neu::Bounds(lower, upper) = types.neu(bounds) else {
        panic!("ref effect should use invariant bounds");
    };
    let Pos::Row(lower_items) = types.pos(*lower) else {
        panic!("ref lower must be a direct row, not a stack carrier");
    };
    let Neg::Row(upper_items, upper_tail) = types.neg(*upper) else {
        panic!("ref upper must be a direct row, not a stack carrier");
    };
    assert_eq!(lower_items.len(), 1);
    assert_eq!(upper_items.len(), 1);
    assert!(matches!(types.neg(*upper_tail), Neg::Bot));
    let Pos::Con(lower_path, lower_args) = types.pos(lower_items[0]) else {
        panic!("ref lower row should contain F");
    };
    let Neg::Con(upper_path, upper_args) = types.neg(upper_items[0]) else {
        panic!("ref upper row should contain F");
    };
    assert_eq!(lower_path, &family_path());
    assert_eq!(upper_path, &family_path());
    assert_eq!(lower_args.len(), usize::from(payload_bearing));
    assert_eq!(upper_args.len(), usize::from(payload_bearing));
    if payload_bearing {
        assert_eq!(
            invariant_var(types, lower_args[0]),
            invariant_var(types, upper_args[0])
        );
    }
}

fn assert_precompact_ref_effect_contains_push_only_carrier(types: &TypeArena, bounds: NeuId) {
    let Neu::Bounds(lower, upper) = types.neu(bounds) else {
        panic!("old ref effect should use invariant bounds");
    };
    let Pos::Stack { inner, weight } = types.pos(*lower) else {
        panic!("old ref lower should contain push-only evidence");
    };
    let Pos::Row(items) = types.pos(*inner) else {
        panic!("old ref carrier should wrap the exact direct row");
    };
    assert_eq!(items.len(), 1);
    assert!(matches!(
        types.pos(items[0]),
        Pos::Con(path, args) if path == &family_path() && args.len() == 1
    ));
    assert!(weight.entries().iter().any(|entry| {
        entry.stack.iter().any(|family| {
            matches!(family, Subtractability::Set(path, args)
                if path == &family_path() && args.len() == 1)
        })
    }));
    assert!(matches!(types.neg(*upper), Neg::Row(_, _)));
}

fn compact_callback_and_helper(compact: &CompactRoot) -> (&CompactFun, &CompactFun) {
    let helper = compact
        .root
        .funs
        .first()
        .unwrap_or_else(|| panic!("expected helper function: {compact:?}"));
    let callback = helper
        .arg
        .funs
        .first()
        .unwrap_or_else(|| panic!("expected callback argument function: {compact:?}"));
    (callback, helper)
}

fn compact_ref_effect_bounds(callback: &CompactFun) -> &CompactBounds {
    let ref_args = callback
        .arg
        .cons
        .get(&ref_path())
        .unwrap_or_else(|| panic!("callback argument should contain the ref constructor"));
    &ref_args[0]
}

fn compact_has_family_row(compact: &CompactType) -> bool {
    compact
        .rows
        .iter()
        .any(|row| row.items.contains_key(&family_path()))
}

fn compact_contains_plain_var(compact: &CompactType, expected: TypeVar) -> bool {
    compact
        .vars
        .iter()
        .any(|var| var.var == expected && var.weight.is_empty())
}

fn family_path() -> Vec<String> {
    FAMILY_PATH
        .iter()
        .map(|segment| (*segment).into())
        .collect()
}

fn ref_path() -> Vec<String> {
    REF_PATH.iter().map(|segment| (*segment).into()).collect()
}

fn observe_path() -> Vec<String> {
    OBSERVE_PATH
        .iter()
        .map(|segment| (*segment).into())
        .collect()
}
