use super::*;

/// Stage 0 characterization oracle for generic role-impl conformance.
///
/// These snapshots deliberately record the current behavior, including invalid
/// explicit associated assignments which are still accepted. Stage 5 of the
/// conformance specification will replace those expectations with rejection
/// witnesses after the proof kernel is connected.
#[test]
fn generic_role_impl_conformance_stage0_symbolic_oracle() {
    for fixture in conformance_fixtures() {
        let actual = characterize(fixture.source, fixture.role);
        assert_eq!(actual, fixture.current, "fixture: {}", fixture.name);
    }
}

/// Alpha renaming must not change the observable scheme/candidate shape even
/// before conformance enforcement exists.
#[test]
fn generic_role_impl_conformance_stage0_alpha_renaming_oracle() {
    let fixtures = conformance_fixtures();
    let left = fixtures
        .iter()
        .find(|fixture| fixture.name == "alpha-renamed-a")
        .expect("alpha-renamed-a fixture");
    let right = fixtures
        .iter()
        .find(|fixture| fixture.name == "alpha-renamed-b")
        .expect("alpha-renamed-b fixture");

    assert_eq!(
        characterize(left.source, left.role),
        characterize(right.source, right.role),
    );
}

#[test]
fn generic_role_impl_conformance_stage3_slice3a_dumps_stage0_shadow_pairs() {
    const EXPECTED: &[(&str, &str)] = &[
        (
            "explicit-bool-concrete-int",
            "contract=0 role=Index method=index impl=explicit declared=available actual=available outcome=Mismatch",
        ),
        (
            "explicit-bool-universal-a",
            "contract=0 role=Index method=index impl=explicit declared=available actual=unavailable outcome=Unavailable",
        ),
        (
            "explicit-a-same-a",
            "contract=0 role=Index method=index impl=explicit declared=available actual=unavailable outcome=Unavailable",
        ),
        (
            "explicit-list-a-nested-binder",
            "contract=0 role=Index method=index impl=explicit declared=available actual=unavailable outcome=Unavailable",
        ),
        (
            "omitted-associated-one-method",
            "contract=0 role=Index method=index impl=explicit declared=unavailable actual=missing outcome=NotCaptured",
        ),
        (
            "omitted-associated-shared-two-methods",
            concat!(
                "contract=0 role=Access method=get impl=explicit declared=unavailable actual=missing outcome=NotCaptured\n",
                "contract=0 role=Access method=peek impl=explicit declared=unavailable actual=missing outcome=NotCaptured",
            ),
        ),
        (
            "partial-explicit-multiple-associated",
            concat!(
                "contract=0 role=PairView method=first impl=explicit declared=unavailable actual=missing outcome=NotCaptured\n",
                "contract=0 role=PairView method=second impl=explicit declared=unavailable actual=missing outcome=NotCaptured",
            ),
        ),
        (
            "residual-prerequisite-absent-present",
            concat!(
                "contract=0 role=Box method=get impl=explicit declared=available actual=available outcome=Conforms\n",
                "contract=1 role=Box method=get impl=explicit declared=available actual=unavailable outcome=Unavailable",
            ),
        ),
        (
            "effectful-shared-row-binder",
            "contract=0 role=Flow method=run impl=explicit declared=unavailable actual=missing outcome=NotCaptured",
        ),
        (
            "alpha-renamed-a",
            "contract=0 role=Index method=index impl=explicit declared=available actual=unavailable outcome=Unavailable",
        ),
        (
            "alpha-renamed-b",
            "contract=0 role=Index method=index impl=explicit declared=available actual=unavailable outcome=Unavailable",
        ),
        (
            "malformed-unused-impl",
            "contract=0 role=Index method=index impl=explicit declared=available actual=unavailable outcome=Unavailable",
        ),
    ];

    let fixtures = conformance_fixtures();
    assert_eq!(fixtures.len(), EXPECTED.len(), "Stage 0 fixture coverage");
    let actual = fixtures
        .iter()
        .map(|fixture| {
            let dump = shadow_conformance_pair_dump(fixture.source);
            eprintln!("Stage 3 Slice 3a {}:\n{dump}", fixture.name);
            (fixture.name, dump)
        })
        .collect::<Vec<_>>();
    let expected = fixtures
        .iter()
        .map(|fixture| {
            let expected = EXPECTED
                .iter()
                .find_map(|(name, expected)| (*name == fixture.name).then_some(*expected))
                .unwrap_or_else(|| panic!("missing Slice 3a expectation for {}", fixture.name));
            (fixture.name, expected.to_string())
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
}

#[test]
fn generic_role_impl_conformance_stage3_stage0_field_selection_value_is_non_atomic() {
    use crate::role_impl_conformance::view::{
        ActualMethodConformanceView, ActualMethodConformanceViewUnavailable, ConformanceTypeView,
        DeclaredTypeView,
    };
    use crate::role_impl_conformance::{RoleImplMethodActualSurface, ShadowConformanceOutcome};

    const FIXTURES: &[&str] = &[
        "explicit-bool-universal-a",
        "explicit-a-same-a",
        "explicit-list-a-nested-binder",
        "alpha-renamed-a",
        "alpha-renamed-b",
        "malformed-unused-impl",
    ];
    let expected_value = ActualMethodConformanceView::Unavailable(
        ActualMethodConformanceViewUnavailable::NonAtomicSurface,
    );
    let expected_effect = ActualMethodConformanceView::Available(ConformanceTypeView::Bottom);

    for name in FIXTURES {
        let output = lower_conformance_fixture(fixture_source(name));
        let pairs = output
            .role_impl_conformance_contracts()
            .iter()
            .flat_map(|contract| contract.shadow_conformance_pairs(&output.modules))
            .collect::<Vec<_>>();
        let [pair] = pairs.as_slice() else {
            panic!("fixture {name}: expected one shadow conformance pair, got {pairs:?}")
        };

        assert_eq!(
            pair.outcome,
            ShadowConformanceOutcome::Unavailable,
            "fixture: {name}",
        );
        assert!(
            matches!(pair.declared.as_ref(), Some(DeclaredTypeView::Available(_))),
            "fixture {name}: declared value surface must be available",
        );
        assert!(
            matches!(
                pair.declared_effect.as_ref(),
                Some(DeclaredTypeView::Available(_))
            ),
            "fixture {name}: declared effect surface must be available",
        );
        let Some(RoleImplMethodActualSurface::Receiver(actual)) = pair.actual.as_ref() else {
            panic!("fixture {name}: expected a captured receiver actual surface")
        };
        assert_eq!(
            actual.value, expected_value,
            "fixture {name}: value surface",
        );
        assert_eq!(
            actual.effect, expected_effect,
            "fixture {name}: effect surface",
        );
    }
}

#[test]
fn generic_role_impl_conformance_stage3_eq1_groups_accessor_instantiations_with_u0() {
    use crate::role_impl_conformance::view::ConformanceBinder;

    for name in ["explicit-a-same-a", "explicit-list-a-nested-binder"] {
        let witness = receiver_exact_equivalence_witness(fixture_source(name), "index");
        assert_eq!(
            witness.bridge_identities,
            vec![ConformanceBinder::Universal(
                crate::role_impl_conformance::ImplUniversalBinderId(0),
            )],
            "fixture: {name}",
        );
        assert_eq!(
            witness.accessor_instantiations.len(),
            1,
            "fixture {name}: the two-member class must contain one non-bridge accessor instantiation; {witness:?}",
        );
        for accessor in &witness.accessor_instantiations {
            assert!(
                witness.exact_class.contains(accessor),
                "fixture {name}: accessor v{} must share U0's exact class; {witness:?}",
                accessor.0,
            );
        }
        assert_eq!(
            witness.exact_class.len(),
            2,
            "fixture {name}: unrelated solver variables must not enter the exact class; {witness:?}",
        );
        for unrelated in &witness.unrelated_anchors {
            assert!(
                !witness.exact_class.contains(unrelated),
                "fixture {name}: unrelated anchor v{} entered U0's exact class; {witness:?}",
                unrelated.0,
            );
        }
    }
}

#[test]
fn generic_role_impl_conformance_stage3_eq1_keeps_one_way_and_weighted_edges_separate() {
    use crate::constraints::{ConstraintMachine, ConstraintWeights};
    use crate::role_impl_conformance::view::ExactEquivalenceClasses;

    let a = TypeVar(0);
    let b = TypeVar(1);

    let mut one_way = ConstraintMachine::new();
    add_var_constraint(&mut one_way, a, ConstraintWeights::empty(), b);
    let mut one_way_classes = ExactEquivalenceClasses::new(&one_way);
    assert_eq!(one_way_classes.class(a), vec![a]);
    assert_eq!(one_way_classes.class(b), vec![b]);

    let mut weighted_return = ConstraintMachine::new();
    add_var_constraint(&mut weighted_return, a, ConstraintWeights::empty(), b);
    add_var_constraint(
        &mut weighted_return,
        b,
        ConstraintWeights::empty().with_left(SubtractId(0)),
        a,
    );
    assert!(weighted_return.bounds().of(b).is_some_and(|bounds| {
        bounds.projection_uppers().any(|upper| {
            matches!(weighted_return.types().neg(upper.neg), Neg::Var(var) if *var == a)
                && !upper.weights.is_empty()
        })
    }));
    let mut weighted_classes = ExactEquivalenceClasses::new(&weighted_return);
    assert_eq!(weighted_classes.class(a), vec![a]);
    assert_eq!(weighted_classes.class(b), vec![b]);
}

#[test]
fn generic_role_impl_conformance_stage3_eq1_characterizes_zero_one_and_multiple_bridge_identities()
{
    use crate::constraints::{ConstraintMachine, ConstraintWeights};
    use crate::role_impl_conformance::view::{ConformanceBinder, ExactEquivalenceClasses};
    use crate::role_impl_conformance::{
        AssociatedInferenceBinderId, ImplUniversalBinderId, RoleImplConformanceBinderBridge,
    };

    let a = TypeVar(0);
    let b = TypeVar(1);
    let mut unbridged_machine = ConstraintMachine::new();
    add_var_constraint(&mut unbridged_machine, a, ConstraintWeights::empty(), b);
    add_var_constraint(&mut unbridged_machine, b, ConstraintWeights::empty(), a);
    let mut unbridged_classes = ExactEquivalenceClasses::new(&unbridged_machine);
    let unbridged_class = unbridged_classes.class(a);
    let no_bridge = RoleImplConformanceBinderBridge {
        universals: Vec::new(),
        inferred_associated: Vec::new(),
    };
    assert_eq!(bridge_identities_in_class(&no_bridge, &unbridged_class), []);

    let one_bridge = RoleImplConformanceBinderBridge {
        universals: vec![(ImplUniversalBinderId(0), a)],
        inferred_associated: Vec::new(),
    };
    assert_eq!(
        bridge_identities_in_class(&one_bridge, &unbridged_class),
        [ConformanceBinder::Universal(ImplUniversalBinderId(0))],
    );

    // This source-level spelling is the realistic overlap already characterized by Stage 1:
    // the impl-head U0 and omitted associated A0 retain distinct identities on one solver var.
    let overlapping_source = concat!(
        "role Box 'a:\n",
        "  type value\n",
        "  our x.get: value\n",
        "impl 'value: Box:\n",
        "  our x.get = x\n",
    );
    let overlapping = lower_conformance_fixture(overlapping_source);
    let [overlapping_contract] = overlapping.role_impl_conformance_contracts() else {
        panic!("overlap fixture must retain one contract")
    };
    let overlapping_bridge = overlapping_contract
        .binder_bridge
        .as_ref()
        .expect("overlap fixture bridge");
    let [(u0, universal_var)] = overlapping_bridge.universals.as_slice() else {
        panic!("overlap fixture universal bridge: {overlapping_bridge:?}")
    };
    let [(a0, associated_var)] = overlapping_bridge.inferred_associated.as_slice() else {
        panic!("overlap fixture associated bridge: {overlapping_bridge:?}")
    };
    assert_eq!(
        (*u0, *a0),
        (ImplUniversalBinderId(0), AssociatedInferenceBinderId(0))
    );
    assert_eq!(universal_var, associated_var);
    let mut overlapping_classes =
        ExactEquivalenceClasses::new(overlapping.session.infer.constraints());
    let overlapping_class = overlapping_classes.class(*universal_var);
    assert_eq!(
        bridge_identities_in_class(overlapping_bridge, &overlapping_class),
        [
            ConformanceBinder::Universal(*u0),
            ConformanceBinder::InferredAssociated(*a0),
        ],
        "EQ1 exposes both identities; the fail-closed policy remains deferred to EQ4",
    );
}

#[test]
fn generic_role_impl_conformance_stage3_eq1_pins_cross_surface_qm_collision_baseline() {
    use crate::constraints::{ConstraintMachine, ConstraintWeights};
    use crate::role_impl_conformance::ActualMethodConformanceView;
    use crate::role_impl_conformance::RoleImplConformanceBinderBridge;
    use crate::role_impl_conformance::view::{
        ConformanceBinder, ConformanceTypeView, ExactEquivalenceClasses,
    };

    // Existing role/impl syntax for a parameterized act introduces an additional exact alias and
    // therefore reaches today's NonAtomicSurface guard before Qm allocation. This minimal settled
    // receiver-surface fixture isolates the independent allocator bug without claiming otherwise.
    let mut machine = ConstraintMachine::new();
    let value_anchor = TypeVar(0);
    let value_member = TypeVar(1);
    let effect_anchor = TypeVar(2);
    let effect_argument = TypeVar(3);
    add_var_constraint(
        &mut machine,
        value_member,
        ConstraintWeights::empty(),
        value_anchor,
    );
    let effect_argument_lower = machine.alloc_pos(Pos::Var(effect_argument));
    let effect_argument_upper = machine.alloc_neg(Neg::Var(effect_argument));
    let effect_argument_bounds =
        machine.alloc_neu(Neu::Bounds(effect_argument_lower, effect_argument_upper));
    let effect_item =
        machine.alloc_pos(Pos::Con(vec!["tick".into()], vec![effect_argument_bounds]));
    let effect_row = machine.alloc_pos(Pos::Row(vec![effect_item]));
    let effect_upper = machine.alloc_neg(Neg::Var(effect_anchor));
    machine.subtype(effect_row, effect_upper);
    let bridge = Ok(RoleImplConformanceBinderBridge {
        universals: Vec::new(),
        inferred_associated: Vec::new(),
    });

    let actual = crate::role_impl_conformance::capture_receiver_actual_view(
        &machine,
        value_anchor,
        effect_anchor,
        &bridge,
    );
    assert_eq!(
        actual.value,
        ActualMethodConformanceView::Available(ConformanceTypeView::Binder(
            ConformanceBinder::MethodQuantifier(0),
        )),
    );
    assert_eq!(
        actual.effect,
        ActualMethodConformanceView::Available(ConformanceTypeView::Nominal {
            path: vec!["tick".into()],
            args: vec![ConformanceTypeView::Binder(
                ConformanceBinder::MethodQuantifier(1),
            )],
        }),
        "the shared value-before-effect resolver gives the distinct effect class Qm1",
    );

    let bridge = bridge.as_ref().expect("constructed bridge");
    let mut classes = ExactEquivalenceClasses::new(&machine);
    let value_class = classes.class(value_member);
    let effect_argument_class = classes.class(effect_argument);
    assert_eq!(value_class, vec![value_member]);
    assert_eq!(effect_argument_class, vec![effect_argument]);
    assert_ne!(
        value_class, effect_argument_class,
        "the colliding Qm0 views come from genuinely different exact classes",
    );
    assert_eq!(bridge_identities_in_class(bridge, &value_class), []);
    assert_eq!(
        bridge_identities_in_class(bridge, &effect_argument_class),
        [],
    );
}

#[test]
fn generic_role_impl_conformance_stage3_slice3b_compares_available_builtin_pairs() {
    let conforms = concat!(
        "role Make 'subject:\n",
        "  type output\n",
        "  our make: output\n",
        "impl Make int:\n",
        "  type output = int\n",
        "  our make = 1\n",
    );
    let mismatch = concat!(
        "role Make 'subject:\n",
        "  type output\n",
        "  our make: output\n",
        "impl Make int:\n",
        "  type output = int\n",
        "  our make = true\n",
    );

    assert_eq!(
        shadow_conformance_pair_dump(conforms),
        "contract=0 role=Make method=make impl=explicit declared=available actual=available outcome=Conforms",
    );
    assert_eq!(
        shadow_conformance_pair_dump(mismatch),
        "contract=0 role=Make method=make impl=explicit declared=available actual=available outcome=Mismatch",
        "Slice 3a intentionally deferred this int/bool comparison to Slice 3b",
    );
}

#[test]
fn generic_role_impl_conformance_stage3_aligns_receiver_result_before_comparison() {
    let conforms = concat!(
        "role Read 'subject:\n",
        "  our x.read: int\n",
        "impl int: Read:\n",
        "  our x.read = 1\n",
    );
    let mismatch = concat!(
        "role Read 'subject:\n",
        "  our x.read: int\n",
        "impl int: Read:\n",
        "  our x.read = true\n",
    );

    let (conforming_output, conforming_member) =
        lower_receiver_conformance_shadow(conforms, true, false, false);
    let conforming_actual = persisted_receiver_actual_view(&conforming_output, conforming_member);
    assert_eq!(conforming_actual.tail_parameter_count, Some(0));
    assert_eq!(
        shadow_conformance_pair_dump_from_output(&conforming_output),
        "contract=0 role=Read method=read impl=explicit declared=available actual=available outcome=Conforms",
    );

    let [contract] = conforming_output.role_impl_conformance_contracts() else {
        panic!("expected one receiver conformance contract")
    };
    let declared = contract.declared_view(&conforming_output.modules);
    let requirement = contract.methods[0]
        .declared_requirement
        .as_ref()
        .expect("declared receiver requirement");
    assert_eq!(
        crate::role_impl_conformance::view::declared_receiver_result_view(
            contract,
            &conforming_output.modules,
            &declared.inputs,
            &declared.associated,
            &requirement.signature,
            1,
        ),
        None,
        "a measured tail-arity mismatch must not be forced into a comparison",
    );

    let (mismatching_output, mismatching_member) =
        lower_receiver_conformance_shadow(mismatch, true, false, false);
    let mismatching_actual =
        persisted_receiver_actual_view(&mismatching_output, mismatching_member);
    assert_eq!(mismatching_actual.tail_parameter_count, Some(0));
    assert_eq!(
        shadow_conformance_pair_dump_from_output(&mismatching_output),
        "contract=0 role=Read method=read impl=explicit declared=available actual=available outcome=Mismatch",
    );
}

#[test]
fn generic_role_impl_conformance_stage3_compares_receiver_value_and_effect_surfaces() {
    use crate::role_impl_conformance::RoleImplMethodActualSurface;
    use crate::role_impl_conformance::ShadowConformanceOutcome;
    use crate::role_impl_conformance::view::{
        ActualMethodConformanceView, ConformanceTypeView, DeclaredTypeView, DeclaredViewUnavailable,
    };

    let pair = |source| {
        let (output, _) = lower_receiver_conformance_shadow(source, true, false, false);
        let [contract] = output.role_impl_conformance_contracts() else {
            panic!("expected one receiver conformance contract")
        };
        let [pair] = contract
            .shadow_conformance_pairs(&output.modules)
            .try_into()
            .unwrap_or_else(|pairs: Vec<_>| panic!("expected one shadow pair, got {pairs:?}"));
        pair
    };

    let pure = pair(concat!(
        "role Run 'subject:\n",
        "  our x.run: unit\n",
        "impl int: Run:\n",
        "  our x.run = ()\n",
    ));
    assert_eq!(
        pure.declared_effect,
        Some(DeclaredTypeView::Available(ConformanceTypeView::Bottom)),
    );
    let Some(RoleImplMethodActualSurface::Receiver(pure_actual)) = pure.actual else {
        panic!("expected pure receiver actual surface")
    };
    assert_eq!(
        pure_actual.effect,
        ActualMethodConformanceView::Available(ConformanceTypeView::Bottom),
    );
    assert_eq!(pure.outcome, ShadowConformanceOutcome::Conforms);

    let matching_effect = pair(concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Run 'subject:\n",
        "  our x.run: [tick] unit\n",
        "impl int: Run:\n",
        "  our x.run = tick::ping()\n",
    ));
    let expected_tick = ConformanceTypeView::Nominal {
        path: vec!["tick".into()],
        args: Vec::new(),
    };
    assert_eq!(
        matching_effect.declared_effect,
        Some(DeclaredTypeView::Available(expected_tick.clone())),
    );
    let Some(RoleImplMethodActualSurface::Receiver(matching_actual)) = matching_effect.actual
    else {
        panic!("expected effectful receiver actual surface")
    };
    assert_eq!(
        matching_actual.effect,
        ActualMethodConformanceView::Available(expected_tick.clone()),
    );
    assert_eq!(matching_effect.outcome, ShadowConformanceOutcome::Conforms);

    let mismatching_effect = pair(concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Run 'subject:\n",
        "  our x.run: unit\n",
        "impl int: Run:\n",
        "  our x.run = tick::ping()\n",
    ));
    assert_eq!(
        mismatching_effect.declared_effect,
        Some(DeclaredTypeView::Available(ConformanceTypeView::Bottom)),
    );
    let Some(RoleImplMethodActualSurface::Receiver(mismatching_actual)) = mismatching_effect.actual
    else {
        panic!("expected mismatching receiver actual surface")
    };
    assert_eq!(
        mismatching_actual.effect,
        ActualMethodConformanceView::Available(expected_tick),
    );
    assert_eq!(
        mismatching_effect.outcome,
        ShadowConformanceOutcome::Mismatch,
    );

    let unsupported_union = pair(concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "act flip:\n",
        "  pub pong: () -> ()\n",
        "role Run 'subject:\n",
        "  our x.run: [tick, flip] unit\n",
        "impl int: Run:\n",
        "  our x.run = tick::ping()\n",
    ));
    assert_eq!(
        unsupported_union.declared_effect,
        Some(DeclaredTypeView::Unavailable(
            DeclaredViewUnavailable::UnsupportedEffectRow,
        )),
    );
    assert_eq!(
        unsupported_union.outcome,
        ShadowConformanceOutcome::Unavailable,
    );
}

#[test]
fn generic_role_impl_conformance_stage3_slice3b_matches_same_contract_universal_binder() {
    use crate::role_impl_conformance::ActualMethodConformanceView;
    use crate::role_impl_conformance::view::{DeclaredAssociatedView, DeclaredTypeView};

    let source = concat!(
        "role Same 'subject:\n",
        "  type output\n",
        "  our x.same: output\n",
        "impl 'a: Same:\n",
        "  type output = 'a\n",
        "  our x.same = x\n",
    );
    let (output, member) = lower_receiver_conformance_shadow(source, true, false, false);
    let [contract] = output.role_impl_conformance_contracts() else {
        panic!("expected one source conformance contract")
    };
    let declared = contract.declared_view(&output.modules);
    let [
        DeclaredAssociatedView::Explicit {
            value: DeclaredTypeView::Available(requirement),
            ..
        },
    ] = declared.associated.as_slice()
    else {
        panic!("expected explicit first-order associated view: {declared:?}")
    };
    let ActualMethodConformanceView::Available(actual) =
        &persisted_receiver_actual_view(&output, member).value
    else {
        panic!("expected available receiver value handoff")
    };

    assert_eq!(actual, requirement, "both views should name contract U0");
    assert!(crate::role_impl_conformance::view::first_order_conforms(
        actual,
        requirement,
    ));
}

#[test]
fn generic_role_impl_conformance_stage3_slice3a_marks_non_explicit_provisions_not_captured() {
    let source = concat!(
        "role Demo 'subject:\n",
        "  our x.defaulted = ()\n",
        "  our x.missing: unit\n",
        "impl int: Demo:\n",
    );

    assert_eq!(
        shadow_conformance_pair_dump(source),
        concat!(
            "contract=0 role=Demo method=defaulted impl=none declared=unavailable actual=missing outcome=NotCaptured\n",
            "contract=0 role=Demo method=missing impl=none declared=unavailable actual=missing outcome=NotCaptured",
        ),
    );
}

#[test]
fn generic_role_impl_conformance_stage1_slice1_captures_binder_provenance() {
    let fixtures = conformance_fixtures();
    let dump = |name| {
        let fixture = fixtures
            .iter()
            .find(|fixture| fixture.name == name)
            .unwrap_or_else(|| panic!("missing fixture {name}"));
        characterize_contract(fixture.source)
    };

    assert_eq!(
        dump("explicit-bool-universal-a"),
        "role=Index universals=[U0] inputs=[{U0},{}] associated=[value=explicit{}]",
    );
    assert_eq!(
        dump("explicit-a-same-a"),
        "role=Index universals=[U0] inputs=[{U0},{}] associated=[value=explicit{U0}]",
    );
    assert_eq!(
        dump("explicit-list-a-nested-binder"),
        "role=Index universals=[U0] inputs=[{U0},{}] associated=[value=explicit{U0}]",
    );
    assert_eq!(
        dump("omitted-associated-one-method"),
        "role=Index universals=[U0] inputs=[{U0},{}] associated=[value=inferred(A0)]",
    );
    assert_eq!(
        dump("partial-explicit-multiple-associated"),
        "role=PairView universals=[U0] inputs=[{U0}] associated=[first=explicit{U0},second=inferred(A0)]",
    );
}

#[test]
fn generic_role_impl_conformance_stage1_slice1_is_alpha_stable() {
    let fixtures = conformance_fixtures();
    let left = fixtures
        .iter()
        .find(|fixture| fixture.name == "alpha-renamed-a")
        .expect("alpha-renamed-a fixture");
    let right = fixtures
        .iter()
        .find(|fixture| fixture.name == "alpha-renamed-b")
        .expect("alpha-renamed-b fixture");

    assert_eq!(
        characterize_contract(left.source),
        characterize_contract(right.source),
    );
}

#[test]
fn generic_role_impl_conformance_stage1_slice1_covers_self_alias_and_imported_nominal() {
    let attached = concat!(
        "role Index 'container 'key:\n",
        "  type value\n",
        "  our c.index: 'key -> value\n",
        "type box 'a with:\n",
        "  struct self:\n",
        "    item: 'a\n",
        "  impl Index int:\n",
        "    type value = 'a\n",
        "    our c.index i = c.item\n",
    );
    assert_eq!(
        characterize_attached_contract(attached, "box"),
        "role=Index universals=[U0] inputs=[{U0},{}] associated=[value=explicit{U0}]",
    );

    let imported = concat!(
        "mod types:\n",
        "  pub type box 'a\n",
        "use types::*\n",
        "role Index 'container 'key:\n",
        "  type value\n",
        "  our c.index: 'key -> value\n",
        "impl Index (box 'a) int:\n",
        "  type value = 'a\n",
    );
    assert_eq!(
        characterize_contract(imported),
        "role=Index universals=[U0] inputs=[{U0},{}] associated=[value=explicit{U0}]",
    );
}

#[test]
fn generic_role_impl_conformance_stage1_slice1_records_synthetic_name_overlap() {
    let source = concat!(
        "role Box 'a:\n",
        "  type value\n",
        "  our x.get: value\n",
        "impl 'value: Box:\n",
        "  our x.get = x\n",
    );

    assert_eq!(
        characterize_contract(source),
        "role=Box universals=[U0] inputs=[{U0}] associated=[value=inferred(A0;annotation-overlap=U0)]",
    );
}

#[test]
fn generic_role_impl_conformance_stage1_slice2_captures_slot_substitution() {
    let fixtures = conformance_fixtures();
    let dump = |name| {
        let fixture = fixtures
            .iter()
            .find(|fixture| fixture.name == name)
            .unwrap_or_else(|| panic!("missing fixture {name}"));
        characterize_method_contract(fixture.source)
    };

    assert_eq!(
        dump("explicit-a-same-a"),
        concat!(
            "substitution=inputs=[container->input0,key->input1] associated=[value->U0] ambiguous=[]\n",
            "methods=[index=explicit(1);refs=[input0,input1,U0]] unmatched=[]",
        ),
    );
    assert_eq!(
        dump("omitted-associated-one-method"),
        concat!(
            "substitution=inputs=[container->input0,key->input1] associated=[value->A0] ambiguous=[]\n",
            "methods=[index=explicit(1);refs=[input0,input1,A0]] unmatched=[]",
        ),
    );
    assert_eq!(dump("alpha-renamed-a"), dump("alpha-renamed-b"),);
}

/// Stage 1 exit witness: the immutable contract survives normal lowering, and the impl head,
/// explicit associated assignment, and substituted method requirement all point at logical U0.
#[test]
fn generic_role_impl_conformance_stage1_exit_preserves_u_through_lowering_handoff() {
    let fixtures = conformance_fixtures();
    let source = |name| {
        fixtures
            .iter()
            .find(|fixture| fixture.name == name)
            .unwrap_or_else(|| panic!("missing fixture {name}"))
            .source
    };
    let expected = concat!(
        "role=Index universals=[U0] inputs=[{U0},{}] associated=[value=explicit{U0}]\n",
        "substitution=inputs=[container->input0,key->input1] associated=[value->U0] ambiguous=[]\n",
        "methods=[index=explicit(1);refs=[input0,input1,U0]] unmatched=[]",
    );

    assert_eq!(lowered_contract_dump(source("explicit-a-same-a")), expected);
    assert_eq!(
        lowered_contract_dump(source("alpha-renamed-a")),
        lowered_contract_dump(source("alpha-renamed-b")),
    );
}

#[test]
fn generic_role_impl_conformance_stage2_slice0_traces_u_and_a_into_final_schemes() {
    let explicit = lower_conformance_fixture(fixture_source("explicit-a-same-a"));
    let explicit_contract = &explicit.role_impl_conformance_contracts()[0];
    let universal = &explicit_contract.universal_binders[0];
    let explicit_associated_ann = match &explicit_contract.associated[0] {
        crate::role_impl_conformance::AssociatedAssignment::Explicit { ty, .. } => {
            let AnnType::Var(var) = &ty.annotation else {
                panic!("explicit value = 'a should retain its source binder");
            };
            var.id
        }
        assignment => panic!("expected explicit associated assignment, got {assignment:?}"),
    };
    assert_eq!(explicit_associated_ann, universal.annotation_var);
    let universal_solver_var = explicit_contract
        .solver_var_for_annotation(universal.annotation_var)
        .expect("U0 annotation should have an inference bridge");
    let explicit_scheme = first_contract_method_scheme(&explicit, explicit_contract);
    let universal_final_location = scheme_var_location(
        &explicit.session.poly.typ,
        explicit_scheme,
        universal_solver_var,
    );
    assert_eq!(universal_final_location, "free");

    let inferred = lower_conformance_fixture(fixture_source("omitted-associated-one-method"));
    let inferred_contract = &inferred.role_impl_conformance_contracts()[0];
    let inferred_binder = match &inferred_contract.associated[0] {
        crate::role_impl_conformance::AssociatedAssignment::Inferred { binder, .. } => binder,
        assignment => panic!("expected inferred associated assignment, got {assignment:?}"),
    };
    let inferred_solver_var = inferred_contract
        .solver_var_for_annotation(inferred_binder.annotation_var)
        .expect("A0 annotation should have an inference bridge");
    let inferred_scheme = first_contract_method_scheme(&inferred, inferred_contract);
    let inferred_final_location = scheme_var_location(
        &inferred.session.poly.typ,
        inferred_scheme,
        inferred_solver_var,
    );
    assert_eq!(inferred_final_location, "free");

    eprintln!(
        "Stage 2 bridge trace: U0 ann={} -> infer=v{} -> final={}; A0 ann={} -> infer=v{} -> final={}",
        universal.annotation_var.0,
        universal_solver_var.0,
        universal_final_location,
        inferred_binder.annotation_var.0,
        inferred_solver_var.0,
        inferred_final_location,
    );
}

#[test]
fn generic_role_impl_conformance_stage2_slice0_characterizes_requirement_contamination() {
    let concrete_bool = fixture_source("explicit-bool-concrete-int");
    let concrete_int = concrete_bool.replacen("type value = bool", "type value = int", 1);
    let universal_bool = fixture_source("explicit-bool-universal-a");
    let universal_a = fixture_source("explicit-a-same-a");

    let concrete_bool_scheme = finalized_contract_method_scheme(concrete_bool);
    let concrete_int_scheme = finalized_contract_method_scheme(&concrete_int);
    let universal_bool_scheme = finalized_contract_method_scheme(universal_bool);
    let universal_a_scheme = finalized_contract_method_scheme(universal_a);

    assert_eq!(concrete_bool_scheme, "box 'a -> int -> int");
    assert_eq!(universal_bool_scheme, "box('a & 'b) -> int -> 'a");
    assert_eq!(concrete_bool_scheme, concrete_int_scheme);
    assert_eq!(universal_bool_scheme, universal_a_scheme);
    assert!(!concrete_bool_scheme.contains("bool"));
    assert!(!universal_bool_scheme.contains("bool"));

    let no_declared_requirement =
        universal_bool.replacen("our c.index: 'key -> value", "our c.index = ()", 1);
    let no_requirement_scheme = finalized_contract_method_scheme(&no_declared_requirement);
    assert_ne!(universal_bool_scheme, no_requirement_scheme);

    eprintln!(
        "Stage 2 contamination trace: concrete bool={concrete_bool_scheme}; concrete control={concrete_int_scheme}; universal bool={universal_bool_scheme}; universal control={universal_a_scheme}; no declared requirement={no_requirement_scheme}",
    );
}

#[test]
fn generic_role_impl_conformance_stage2_slice1_builds_declared_first_order_view() {
    use crate::role_impl_conformance::view::{
        ConformanceBinder, ConformanceTypeView, DeclaredAssociatedView, DeclaredTypeReferenceView,
        DeclaredTypeView, DeclaredViewUnavailable,
    };

    let output = lower_conformance_fixture(fixture_source("explicit-list-a-nested-binder"));
    let view = output.role_impl_conformance_contracts()[0].declared_view(&output.modules);
    let u0 = ConformanceBinder::Universal(
        output.role_impl_conformance_contracts()[0].universal_binders[0].id,
    );
    let nominal = |name: &str, args| {
        DeclaredTypeView::Available(ConformanceTypeView::Nominal {
            path: vec![name.to_string()],
            args,
        })
    };

    assert_eq!(
        view.inputs,
        vec![
            nominal("box", vec![ConformanceTypeView::Binder(u0)]),
            DeclaredTypeView::Available(ConformanceTypeView::Builtin(BuiltinType::Int)),
        ],
    );
    assert_eq!(
        view.associated,
        vec![DeclaredAssociatedView::Explicit {
            name: "value".into(),
            value: nominal("list", vec![ConformanceTypeView::Binder(u0)]),
        }],
    );
    assert_eq!(
        view.input_substitution[0].references,
        vec![DeclaredTypeReferenceView::DeclaredInput(0)],
    );
    assert_eq!(view.input_substitution[0].value, view.inputs[0]);
    assert_eq!(
        view.associated_substitution[0].references,
        vec![DeclaredTypeReferenceView::Binder(u0)],
    );
    assert_eq!(
        view.associated_substitution[0].value,
        match &view.associated[0] {
            DeclaredAssociatedView::Explicit { value, .. } => value.clone(),
            assignment => panic!("expected explicit assignment, got {assignment:?}"),
        },
    );
    assert_eq!(
        view.methods[0].requirement,
        DeclaredTypeView::Unavailable(DeclaredViewUnavailable::UnsupportedFunction),
    );

    let inferred_output =
        lower_conformance_fixture(fixture_source("omitted-associated-one-method"));
    let inferred_view = inferred_output.role_impl_conformance_contracts()[0]
        .declared_view(&inferred_output.modules);
    let inferred = ConformanceBinder::InferredAssociated(
        match &inferred_output.role_impl_conformance_contracts()[0].associated[0] {
            crate::role_impl_conformance::AssociatedAssignment::Inferred { binder, .. } => {
                binder.id
            }
            assignment => panic!("expected inferred assignment, got {assignment:?}"),
        },
    );
    assert_eq!(
        inferred_view.associated,
        vec![DeclaredAssociatedView::Inferred {
            name: "value".into(),
            binder: inferred,
        }],
    );
    assert_eq!(
        inferred_view.associated_substitution[0].value,
        DeclaredTypeView::Available(ConformanceTypeView::Binder(inferred)),
    );
    assert_eq!(
        inferred_view.associated_substitution[0].references,
        vec![DeclaredTypeReferenceView::Binder(inferred)],
    );

    let tuple_source = concat!(
        "type box 'a with:\n",
        "  struct self:\n",
        "    item: ('a, int)\n",
        "role Read 'container:\n",
        "  type value\n",
        "  our c.read: value\n",
        "impl (box 'a): Read:\n",
        "  type value = ('a, int)\n",
        "  our c.read = c.item\n",
    );
    let tuple_output = lower_conformance_fixture(tuple_source);
    let tuple_view =
        tuple_output.role_impl_conformance_contracts()[0].declared_view(&tuple_output.modules);
    assert!(matches!(
        &tuple_view.associated[0],
        DeclaredAssociatedView::Explicit {
            value: DeclaredTypeView::Available(ConformanceTypeView::Tuple(items)),
            ..
        } if matches!(items.as_slice(), [
            ConformanceTypeView::Binder(ConformanceBinder::Universal(_)),
            ConformanceTypeView::Builtin(BuiltinType::Int),
        ])
    ));

    let imported_source = concat!(
        "mod types:\n",
        "  pub type wrapped 'a\n",
        "use types::*\n",
        "role Read 'container:\n",
        "  type value\n",
        "  our c.read = ()\n",
        "impl (wrapped 'a): Read:\n",
        "  type value = 'a\n",
    );
    let imported_output = lower_conformance_fixture(imported_source);
    let imported_view = imported_output.role_impl_conformance_contracts()[0]
        .declared_view(&imported_output.modules);
    assert!(matches!(
        &imported_view.inputs[0],
        DeclaredTypeView::Available(ConformanceTypeView::Nominal { path, args })
            if path == &["types".to_string(), "wrapped".to_string()]
                && matches!(args.as_slice(), [ConformanceTypeView::Binder(ConformanceBinder::Universal(_))])
    ));

    assert_ne!(ConformanceTypeView::Top, ConformanceTypeView::Bottom);
    assert_ne!(ConformanceTypeView::Top, ConformanceTypeView::Unknown);
    assert_ne!(ConformanceTypeView::Bottom, ConformanceTypeView::Unknown);
}

#[test]
fn generic_role_impl_conformance_stage2_slice1_is_alpha_stable_and_binder_sensitive() {
    let fixtures = conformance_fixtures();
    let source = |name| {
        fixtures
            .iter()
            .find(|fixture| fixture.name == name)
            .unwrap_or_else(|| panic!("missing fixture {name}"))
            .source
    };
    assert_eq!(
        declared_contract_view(source("alpha-renamed-a")),
        declared_contract_view(source("alpha-renamed-b")),
    );

    let left = concat!(
        "type pair 'a 'b with:\n",
        "  struct self:\n",
        "    left: 'a\n",
        "    right: 'b\n",
        "role Pick 'container:\n",
        "  type value\n",
        "  our c.pick: value\n",
        "impl (pair 'a 'b): Pick:\n",
        "  type value = 'a\n",
        "  our c.pick = c.left\n",
    );
    let alpha = left.replace("'a", "'x").replace("'b", "'y");
    let swapped = left
        .replacen("type value = 'a", "type value = 'b", 1)
        .replacen("our c.pick = c.left", "our c.pick = c.right", 1);

    assert_eq!(declared_contract_view(left), declared_contract_view(&alpha));
    assert_ne!(
        declared_contract_view(left),
        declared_contract_view(&swapped),
    );
}

#[test]
fn generic_role_impl_conformance_stage2_slice1_keeps_unavailable_and_ambiguous_explicit() {
    use crate::role_impl_conformance::view::{
        DeclaredTypeView, DeclaredViewAmbiguity, DeclaredViewUnavailable,
    };

    let same_name = concat!(
        "role Clash 'a:\n",
        "  type a\n",
        "  our x.read: a\n",
        "impl int: Clash:\n",
        "  type a = int\n",
        "  our x.read = 1\n",
    );
    let same_name_view = declared_contract_view(same_name);
    assert_eq!(
        same_name_view.methods[0].requirement,
        DeclaredTypeView::Ambiguous(DeclaredViewAmbiguity::InputAssociatedNameCollision(
            "a".into(),
        )),
    );

    let unannotated_default = concat!(
        "role Demo 'subject:\n",
        "  our x.defaulted = ()\n",
        "impl int: Demo:\n",
    );
    let default_view = declared_contract_view(unannotated_default);
    assert_eq!(
        default_view.methods[0].requirement,
        DeclaredTypeView::Unavailable(DeclaredViewUnavailable::UnannotatedRequirement),
    );
}

/// Slice 0 witness for the current role-impl method lifecycle. Body lowering is synchronous,
/// while every SCC input stays queued until analysis starts draining. Keeping the role declaration
/// after the impl makes the member-to-requirement dependency observable as a component edge instead
/// of letting the role method quantify before the dependency input reaches the SCC machine.
#[test]
fn role_impl_method_lifecycle_slice0_records_current_event_order() {
    for fixture in lifecycle_fixtures() {
        let root = parse(fixture.source);
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let implementation = lower.modules.role_impls(module)[0].clone();
        let members = implementation
            .methods
            .iter()
            .map(|method| method.def)
            .collect::<Vec<_>>();
        let role = lower.modules.type_decls(module, &Name(fixture.role.into()))[0].clone();
        let requirements = lower
            .modules
            .role_methods(role.id)
            .iter()
            .map(|method| method.def)
            .collect::<Vec<_>>();
        let ordinary = fixture.ordinary_binding.map(|name| {
            lower
                .modules
                .value_decls(implementation.body_module, &Name(name.into()))[0]
                .def
        });
        let mut lowerer = super::super::body::BodyLowerer::new(lower);
        lowerer.set_receiverless_conformance_shadow_enabled(false);

        lowerer.lower_block(&root, module);

        assert_eq!(lowerer.errors, Vec::new(), "fixture: {}", fixture.name);
        for member in &members {
            assert!(
                lowerer.typing.def(*member).is_some(),
                "body lowering assigned the method root before drain: {}",
                fixture.name,
            );
            assert_eq!(
                lowerer.session.scc.root_of(*member),
                None,
                "RegisterDef is still queued after body/requirement lowering: {}",
                fixture.name,
            );
            assert!(!lowerer.session.scc.is_quantified(*member));
            assert!(matches!(
                lowerer.session.poly.defs.get(*member),
                Some(Def::Let {
                    scheme: None,
                    body: Some(_),
                    ..
                })
            ));
        }

        let mut timeline = Vec::new();
        let mut registered = rustc_hash::FxHashSet::default();
        while lowerer.session.step() {
            for member in &members {
                if !registered.contains(member) && lowerer.session.scc.root_of(*member).is_some() {
                    registered.insert(*member);
                    timeline.push(LifecycleEvent::RegisterDef(*member));
                }
            }
            for event in lowerer.session.take_scc_events() {
                match event {
                    SccEvent::ComponentEdgeAdded { from, to }
                        if from.iter().any(|def| members.contains(def))
                            && to.iter().any(|def| requirements.contains(def)) =>
                    {
                        let member = *from
                            .iter()
                            .find(|def| members.contains(def))
                            .expect("member dependency source");
                        timeline.push(LifecycleEvent::RequirementDependency(member))
                    }
                    SccEvent::MergeComponents { merged, .. } => {
                        timeline.push(LifecycleEvent::Merge(merged))
                    }
                    SccEvent::QuantifyComponent { component, .. } => {
                        timeline.push(LifecycleEvent::Quantify(component))
                    }
                    _ => {}
                }
            }
        }

        // `step` empties the ordinary queue but does not run the unresolved-role pass. Recursive
        // fixtures need the same role-progress phase that `drain_work` owns before their SCC can
        // merge and quantify.
        lowerer.session.drain_work();
        for event in lowerer.session.take_scc_events() {
            match event {
                SccEvent::MergeComponents { merged, .. } => {
                    timeline.push(LifecycleEvent::Merge(merged))
                }
                SccEvent::QuantifyComponent { component, .. } => {
                    timeline.push(LifecycleEvent::Quantify(component))
                }
                _ => {}
            }
        }

        assert_eq!(registered.len(), members.len(), "fixture: {}", fixture.name);
        if fixture.observe_dependency_edge {
            assert_eq!(
                timeline
                    .iter()
                    .filter(|event| matches!(event, LifecycleEvent::RequirementDependency(_)))
                    .count(),
                members.len(),
                "one queued DependencyAdded per role impl member: {}",
                fixture.name,
            );
        }
        for member in &members {
            let register = timeline_position(
                &timeline,
                |event| matches!(event, LifecycleEvent::RegisterDef(def) if def == member),
            );
            let quantify = timeline_position(
                &timeline,
                |event| matches!(event, LifecycleEvent::Quantify(component) if component.contains(member)),
            );
            if fixture.observe_dependency_edge {
                let dependency = timeline_position(
                    &timeline,
                    |event| matches!(event, LifecycleEvent::RequirementDependency(def) if def == member),
                );
                assert!(
                    register < dependency,
                    "fixture: {}; {timeline:?}",
                    fixture.name
                );
                assert!(
                    dependency < quantify,
                    "fixture: {}; {timeline:?}",
                    fixture.name
                );
            } else {
                assert!(
                    register < quantify,
                    "fixture: {}; {timeline:?}",
                    fixture.name
                );
            }
            assert!(lowerer.session.scc.is_quantified(*member));
            assert!(matches!(
                lowerer.session.poly.defs.get(*member),
                Some(Def::Let {
                    scheme: Some(_),
                    ..
                })
            ));
        }

        if fixture.expect_multi_member_component {
            assert!(
                timeline.iter().any(|event| {
                    matches!(event, LifecycleEvent::Merge(component)
                    if members.iter().all(|member| component.contains(member)))
                }),
                "fixture: {}; {timeline:?}",
                fixture.name
            );
            assert!(
                timeline.iter().any(|event| {
                    matches!(event, LifecycleEvent::Quantify(component)
                    if members.iter().all(|member| component.contains(member)))
                }),
                "fixture: {}; {timeline:?}",
                fixture.name
            );
        }
        if let Some(ordinary) = ordinary {
            assert!(
                timeline.iter().any(|event| {
                    matches!(event, LifecycleEvent::Quantify(component)
                    if component.contains(&members[0]) && component.contains(&ordinary))
                }),
                "fixture: {}; {timeline:?}",
                fixture.name
            );
        }

        eprintln!("lifecycle {}: {timeline:?}", fixture.name);
    }
}

#[test]
fn role_impl_method_lifecycle_slice0_counts_current_requirement_connections() {
    let receiverless = concat!(
        "role Make 'subject:\n",
        "  our make: int\n",
        "impl Make int:\n",
        "  our make = 1\n",
    );
    with_requirement_harness(
        receiverless,
        "make",
        |lowerer, requirement, bindings, vars| {
            let method_value = lowerer.fresh_type_var();
            let before = upper_bound_count(lowerer, method_value);
            lowerer
                .connect_impl_method_requirement(method_value, requirement, bindings, vars, true)
                .expect("receiverless requirement connection");
            assert_eq!(upper_bound_count(lowerer, method_value) - before, 1);
        },
    );

    let receiver_zero = concat!(
        "role Read 'subject:\n",
        "  our x.read: int\n",
        "impl int: Read:\n",
        "  our x.read = 1\n",
    );
    with_requirement_harness(
        receiver_zero,
        "read",
        |lowerer, requirement, bindings, vars| {
            assert_receiver_requirement_connections(lowerer, requirement, bindings, vars, 0);
        },
    );

    let receiver_multiple = concat!(
        "role Choose 'subject:\n",
        "  our x.choose: int -> int -> int\n",
        "impl int: Choose:\n",
        "  our x.choose a b = a\n",
    );
    with_requirement_harness(
        receiver_multiple,
        "choose",
        |lowerer, requirement, bindings, vars| {
            assert_receiver_requirement_connections(lowerer, requirement, bindings, vars, 2);
        },
    );

    let mutual = lifecycle_fixtures()
        .into_iter()
        .find(|fixture| fixture.name == "mutual-with-ordinary-binding")
        .expect("mutual lifecycle fixture");
    with_requirement_harness(
        mutual.source,
        "eval",
        |lowerer, requirement, bindings, vars| {
            assert_receiver_requirement_connections(lowerer, requirement, bindings, vars, 0);
        },
    );

    for method in ["left", "right"] {
        let multi = lifecycle_fixtures()
            .into_iter()
            .find(|fixture| fixture.name == "two-role-impl-methods-one-component")
            .expect("multi-method lifecycle fixture");
        with_requirement_harness(
            multi.source,
            method,
            |lowerer, requirement, bindings, vars| {
                assert_receiver_requirement_connections(lowerer, requirement, bindings, vars, 0);
            },
        );
    }
}

#[test]
fn role_impl_method_lifecycle_slice0_expected_lowering_mutates_effect_bridge_before_connection() {
    let plain_u = concat!(
        "type box 'a\n",
        "role Read 'subject:\n",
        "  our x.read: 'subject\n",
        "impl (box 'a): Read:\n",
        "  our x.read = x\n",
    );
    with_requirement_harness(plain_u, "read", |lowerer, requirement, bindings, vars| {
        let bridge = solver_var_named(bindings, vars, "a");
        let before = bridge_state(lowerer, bridge);
        let epoch = lowerer.session.infer.constraints().epoch();
        let plan = lowerer
            .impl_method_requirement_plan(&requirement.signature, 0, true, bindings, vars)
            .expect("plain U requirement plan");
        assert!(plan.body.is_some());
        assert_eq!(bridge_state(lowerer, bridge), before);
        assert_eq!(lowerer.session.infer.constraints().epoch(), epoch);
        assert_eq!(solver_var_named(bindings, vars, "a"), bridge);
    });

    let plain_a = concat!(
        "role Read 'subject:\n",
        "  type value\n",
        "  our x.read: value\n",
        "impl int: Read:\n",
        "  our x.read = 1\n",
    );
    with_requirement_harness(plain_a, "read", |lowerer, requirement, bindings, vars| {
        let bridge = solver_var_named(bindings, vars, "value");
        let before = bridge_state(lowerer, bridge);
        let epoch = lowerer.session.infer.constraints().epoch();
        let plan = lowerer
            .impl_method_requirement_plan(&requirement.signature, 0, true, bindings, vars)
            .expect("plain A requirement plan");
        assert!(plan.body.is_some());
        assert_eq!(bridge_state(lowerer, bridge), before);
        assert_eq!(lowerer.session.infer.constraints().epoch(), epoch);
        assert_eq!(solver_var_named(bindings, vars, "value"), bridge);
    });

    let effect_u = concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Flow 'subject 'effect:\n",
        "  our x.run: unit -> [tick; 'effect] unit\n",
        "impl Flow int 'e:\n",
        "  our x.run u = ()\n",
    );
    with_requirement_harness(effect_u, "run", |lowerer, requirement, bindings, vars| {
        let bridge = solver_var_named(bindings, vars, "e");
        let before = bridge_state(lowerer, bridge);
        let epoch = lowerer.session.infer.constraints().epoch();
        let plan = lowerer
            .impl_method_requirement_plan(&requirement.signature, 1, true, bindings, vars)
            .expect("effect-tail U requirement plan");
        let after = bridge_state(lowerer, bridge);
        assert!(plan.body.is_some(), "temporary body upper was lowered");
        assert_eq!(after.bounds, before.bounds);
        assert_eq!(after.subtract_facts.len(), before.subtract_facts.len() + 1);
        assert!(lowerer.session.infer.constraints().epoch() > epoch);
        assert_eq!(solver_var_named(bindings, vars, "e"), bridge);
        eprintln!(
            "expected lowering bridge mutation: U(e)=v{} bounds unchanged, subtract facts {} -> {}, epoch {} -> {}",
            bridge.0,
            before.subtract_facts.len(),
            after.subtract_facts.len(),
            epoch.as_u64(),
            lowerer.session.infer.constraints().epoch().as_u64(),
        );
    });

    let effect_a = concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Flow 'subject:\n",
        "  type effect\n",
        "  our x.run: unit -> [tick; effect] unit\n",
        "impl int: Flow:\n",
        "  our x.run u = ()\n",
    );
    with_requirement_harness(effect_a, "run", |lowerer, requirement, bindings, vars| {
        let bridge = solver_var_named(bindings, vars, "effect");
        let before = bridge_state(lowerer, bridge);
        let epoch = lowerer.session.infer.constraints().epoch();
        let plan = lowerer
            .impl_method_requirement_plan(&requirement.signature, 1, true, bindings, vars)
            .expect("effect-tail A requirement plan");
        let after = bridge_state(lowerer, bridge);
        assert!(plan.body.is_some(), "temporary body upper was lowered");
        assert_eq!(after.bounds, before.bounds);
        assert_eq!(after.subtract_facts.len(), before.subtract_facts.len() + 1);
        assert!(lowerer.session.infer.constraints().epoch() > epoch);
        assert_eq!(solver_var_named(bindings, vars, "effect"), bridge);
        eprintln!(
            "expected lowering bridge mutation: A(effect)=v{} bounds unchanged, subtract facts {} -> {}, epoch {} -> {}",
            bridge.0,
            before.subtract_facts.len(),
            after.subtract_facts.len(),
            epoch.as_u64(),
            lowerer.session.infer.constraints().epoch().as_u64(),
        );
    });

    let effect_row_parameter_u = concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Consume 'subject 'effect:\n",
        "  our x.consume: '[tick; 'effect] -> unit\n",
        "impl Consume int 'e:\n",
        "  our x.consume action = ()\n",
    );
    with_requirement_harness(
        effect_row_parameter_u,
        "consume",
        |lowerer, requirement, bindings, vars| {
            let bridge = solver_var_named(bindings, vars, "e");
            let before = bridge_state(lowerer, bridge);
            let epoch = lowerer.session.infer.constraints().epoch();
            let plan = lowerer
                .impl_method_requirement_plan(&requirement.signature, 1, true, bindings, vars)
                .expect("effect-row parameter U requirement plan");
            let after = bridge_state(lowerer, bridge);
            let bounds = after
                .bounds
                .as_ref()
                .expect("temporary parameter upper mutates the bridge bounds");
            assert!(plan.param_uppers[0].is_some());
            assert!(!bounds.lowers().is_empty());
            assert!(!bounds.uppers().is_empty());
            assert_ne!(after.bounds, before.bounds);
            assert!(lowerer.session.infer.constraints().epoch() > epoch);
            assert_eq!(solver_var_named(bindings, vars, "e"), bridge);
            eprintln!(
                "expected lowering bridge mutation: parameter U(e)=v{} bounds {:?} -> lowers={}, uppers={}, epoch {} -> {}",
                bridge.0,
                before.bounds,
                bounds.lowers().len(),
                bounds.uppers().len(),
                epoch.as_u64(),
                lowerer.session.infer.constraints().epoch().as_u64(),
            );
        },
    );
}

#[test]
fn role_impl_method_lifecycle_slice0_signature_lowerer_reuses_internal_state() {
    let method_local = concat!(
        "role Same 'subject:\n",
        "  our x.same: 'm -> 'm\n",
        "impl int: Same:\n",
        "  our x.same value = value\n",
    );
    with_requirement_harness(
        method_local,
        "same",
        |lowerer, requirement, bindings, vars| {
            let plan = lowerer
                .impl_method_requirement_plan(&requirement.signature, 1, true, bindings, vars)
                .expect("method-local signature variable plan");
            let parameter = neg_var(
                lowerer.session.infer.constraints().types(),
                plan.param_uppers[0].expect("parameter upper"),
            );
            let body = neg_var(
                lowerer.session.infer.constraints().types(),
                plan.body.expect("body upper").value_upper,
            );
            assert_eq!(parameter, body);
            assert!(!vars.values().any(|bridge| *bridge == parameter));
        },
    );

    let closed_effect = concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Run 'subject:\n",
        "  our x.run: (unit -> [tick] unit) -> [tick] unit\n",
        "impl int: Run:\n",
        "  our x.run action = action()\n",
    );
    with_requirement_harness(
        closed_effect,
        "run",
        |lowerer, requirement, bindings, vars| {
            let plan = lowerer
                .impl_method_requirement_plan(&requirement.signature, 1, true, bindings, vars)
                .expect("closed effect row plan");
            let types = lowerer.session.infer.constraints().types();
            let parameter_effect = match types.neg(plan.param_uppers[0].expect("parameter upper")) {
                Neg::Fun { ret_eff, .. } => stacked_neg_var(types, *ret_eff),
                other => panic!("expected function parameter upper, got {other:?}"),
            };
            let body_effect = stacked_neg_var(types, plan.body.expect("body upper").effect_upper);
            assert_eq!(parameter_effect, body_effect);
            assert!(!vars.values().any(|bridge| *bridge == parameter_effect));
        },
    );

    assert_signature_lowerer_reuses_private_data_effect_tail();
}

#[test]
fn role_impl_method_lifecycle_slice1b_pause_resume_preserves_signature_lowerer_state() {
    let method_local = concat!(
        "role Same 'subject:\n",
        "  our x.same: 'm -> 'm\n",
        "impl int: Same:\n",
        "  our x.same value = value\n",
    );
    with_requirement_harness(
        method_local,
        "same",
        |lowerer, requirement, bindings, vars| {
            let witness =
                pause_resume_requirement_parameter_and_body(lowerer, requirement, bindings, vars);
            let types = lowerer.session.infer.constraints().types();
            let parameter = neg_var(types, witness.parameter_upper);
            let body = neg_var(types, witness.body.value_upper);
            let resumed_fresh = neg_var(types, witness.resumed_fresh_upper);
            assert_eq!(parameter, body);
            assert!(!vars.values().any(|bridge| *bridge == parameter));
            assert_eq!(
                lowerer.session.infer.constraints().level_of(parameter),
                witness.captured_level,
            );
            assert_eq!(
                lowerer.session.infer.constraints().level_of(resumed_fresh),
                witness.captured_level,
            );
        },
    );

    let closed_effect = concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Run 'subject:\n",
        "  our x.run: (unit -> [tick] unit) -> [tick] unit\n",
        "impl int: Run:\n",
        "  our x.run action = action()\n",
    );
    with_requirement_harness(
        closed_effect,
        "run",
        |lowerer, requirement, bindings, vars| {
            let witness =
                pause_resume_requirement_parameter_and_body(lowerer, requirement, bindings, vars);
            let types = lowerer.session.infer.constraints().types();
            let parameter_effect = match types.neg(witness.parameter_upper) {
                Neg::Fun { ret_eff, .. } => stacked_neg_var(types, *ret_eff),
                other => panic!("expected function parameter upper, got {other:?}"),
            };
            let body_effect = stacked_neg_var(types, witness.body.effect_upper);
            assert_eq!(parameter_effect, body_effect);
            assert!(!vars.values().any(|bridge| *bridge == parameter_effect));
        },
    );

    assert_signature_lowerer_pause_resume_reuses_private_data_effect_tail();
}

#[test]
fn role_impl_method_lifecycle_slice1c_builds_inactive_descriptor_and_audits_parameters() {
    let plain_u = concat!(
        "type box 'a\n",
        "role Read 'subject:\n",
        "  our x.read: 'subject\n",
        "impl (box 'a): Read:\n",
        "  our x.read = x\n",
    );
    let plain_a = concat!(
        "role Read 'subject:\n",
        "  type value\n",
        "  our x.read: value\n",
        "impl int: Read:\n",
        "  our x.read = 1\n",
    );
    for (source, bridge_name) in [(plain_u, "a"), (plain_a, "value")] {
        with_requirement_harness(source, "read", |lowerer, requirement, bindings, vars| {
            let receiver = lowerer.fresh_type_var();
            let bridge = solver_var_named(bindings, vars, bridge_name);
            let before = bridge_state(lowerer, bridge);
            let epoch = lowerer.session.infer.constraints().epoch();
            let pending = lowerer
                .deferred_impl_method_requirement(
                    DeferredRequirementAnchor::Receiver { receiver },
                    Arc::clone(requirement),
                    0,
                    true,
                    bindings,
                    vars,
                )
                .expect("plain U/A pending descriptor");

            assert_eq!(
                pending.anchor,
                DeferredRequirementAnchor::Receiver { receiver }
            );
            assert!(Arc::ptr_eq(&pending.requirement, requirement));
            assert!(pending.parameter_uppers.is_empty());
            assert_eq!(
                pending.body_cursor,
                RequirementSpineCursor::FunctionResult {
                    consumed_function_layers: 1,
                }
            );
            assert_eq!(
                pending.parameter_context,
                RequirementParameterContextStatus::Clean(
                    NonMutatingRequirementClass::PlainValueParameters { count: 0 }
                )
            );
            assert!(!pending.final_metadata.connect_value_upper);
            assert_eq!(
                pending.final_metadata.signature_vars.get(bridge_name),
                Some(&bridge)
            );
            assert_eq!(bridge_state(lowerer, bridge), before);
            assert_eq!(lowerer.session.infer.constraints().epoch(), epoch);
        });
    }

    let receiverless = concat!(
        "impl Make int:\n",
        "  our make = 1\n",
        "role Make 'subject:\n",
        "  our make: int\n",
    );
    with_requirement_harness(
        receiverless,
        "make",
        |lowerer, requirement, bindings, vars| {
            let value = lowerer.fresh_type_var();
            let pending = lowerer
                .deferred_impl_method_requirement(
                    DeferredRequirementAnchor::Receiverless { value },
                    Arc::clone(requirement),
                    0,
                    false,
                    bindings,
                    vars,
                )
                .expect("receiverless pending descriptor");
            assert_eq!(
                pending.anchor,
                DeferredRequirementAnchor::Receiverless { value }
            );
            assert_eq!(pending.body_cursor, RequirementSpineCursor::WholeValue);
            assert!(pending.final_metadata.connect_value_upper);
            assert!(pending.parameter_uppers.is_empty());
        },
    );

    let effect_u = concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Flow 'subject 'effect:\n",
        "  our x.run: unit -> [tick; 'effect] unit\n",
        "impl Flow int 'e:\n",
        "  our x.run u = ()\n",
    );
    let effect_a = concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Flow 'subject:\n",
        "  type effect\n",
        "  our x.run: unit -> [tick; effect] unit\n",
        "impl int: Flow:\n",
        "  our x.run u = ()\n",
    );
    for (source, bridge_name) in [(effect_u, "e"), (effect_a, "effect")] {
        with_requirement_harness(source, "run", |lowerer, requirement, bindings, vars| {
            let receiver = lowerer.fresh_type_var();
            let bridge = solver_var_named(bindings, vars, bridge_name);
            let before_bridge = bridge_state(lowerer, bridge);
            let before_epoch = lowerer.session.infer.constraints().epoch();
            let pending = lowerer
                .deferred_impl_method_requirement(
                    DeferredRequirementAnchor::Receiver { receiver },
                    Arc::clone(requirement),
                    1,
                    true,
                    bindings,
                    vars,
                )
                .expect("effect-result pending descriptor");
            assert_eq!(
                pending.parameter_context,
                RequirementParameterContextStatus::Clean(
                    NonMutatingRequirementClass::PlainValueParameters { count: 1 }
                )
            );
            assert!(pending.parameter_uppers[0].is_some());
            assert_eq!(
                pending.body_cursor,
                RequirementSpineCursor::FunctionResult {
                    consumed_function_layers: 2,
                }
            );
            assert_eq!(pending.continuation.vars.get(bridge_name), Some(&bridge));
            assert_eq!(
                pending.final_metadata.signature_vars.get(bridge_name),
                Some(&bridge)
            );
            assert_eq!(bridge_state(lowerer, bridge), before_bridge);
            assert_eq!(lowerer.session.infer.constraints().epoch(), before_epoch);

            // The defensive audit is deliberately negative-only. Running the legacy complete
            // plan crosses the deferred body boundary and must classify the observed effect-tail
            // mutation as unavailable rather than retroactively treating it as clean context.
            let before = lowerer.requirement_bridge_audit_snapshot(bindings, vars);
            lowerer
                .impl_method_requirement_plan(&requirement.signature, 1, true, bindings, vars)
                .expect("legacy complete effect-result plan");
            let status = lowerer.requirement_parameter_context_since(
                NonMutatingRequirementClass::PlainValueParameters { count: 1 },
                before,
                bindings,
                vars,
            );
            let RequirementParameterContextStatus::MutatedBridge(audit) = status else {
                panic!("expected bridge mutation audit")
            };
            assert!(audit.epoch_after > audit.epoch_before);
            assert!(!audit.unexplained_epoch_advance);
            assert!(audit.affected.iter().any(|mutation| {
                mutation.solver_var == bridge
                    && !mutation.bounds_changed
                    && mutation.subtract_facts_changed
            }));
        });
    }

    let effect_row_parameter_u = concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Consume 'subject 'effect:\n",
        "  our x.consume: '[tick; 'effect] -> unit\n",
        "impl Consume int 'e:\n",
        "  our x.consume action = ()\n",
    );
    with_requirement_harness(
        effect_row_parameter_u,
        "consume",
        |lowerer, requirement, bindings, vars| {
            let receiver = lowerer.fresh_type_var();
            let bridge = solver_var_named(bindings, vars, "e");
            let before = bridge_state(lowerer, bridge);
            let epoch = lowerer.session.infer.constraints().epoch();
            let pending = lowerer
                .deferred_impl_method_requirement(
                    DeferredRequirementAnchor::Receiver { receiver },
                    Arc::clone(requirement),
                    1,
                    true,
                    bindings,
                    vars,
                )
                .expect("effect-row parameter pending descriptor");

            assert_eq!(pending.parameter_uppers, vec![None]);
            assert!(matches!(
                pending.parameter_context,
                RequirementParameterContextStatus::Unsupported(
                    RequirementParameterContextUnavailable {
                        parameter_index: 0,
                        reason: RequirementParameterUnsupportedReason::EffectRow,
                    }
                )
            ));
            assert_eq!(bridge_state(lowerer, bridge), before);
            assert_eq!(lowerer.session.infer.constraints().epoch(), epoch);
        },
    );

    let effect_family_parameter = concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Consume 'subject:\n",
        "  our x.consume: tick -> unit\n",
        "impl int: Consume:\n",
        "  our x.consume action = ()\n",
    );
    with_requirement_harness(
        effect_family_parameter,
        "consume",
        |lowerer, requirement, bindings, vars| {
            let receiver = lowerer.fresh_type_var();
            let pending = lowerer
                .deferred_impl_method_requirement(
                    DeferredRequirementAnchor::Receiver { receiver },
                    Arc::clone(requirement),
                    1,
                    true,
                    bindings,
                    vars,
                )
                .expect("effect-family parameter pending descriptor");
            assert!(matches!(
                pending.parameter_context,
                RequirementParameterContextStatus::Unsupported(
                    RequirementParameterContextUnavailable {
                        parameter_index: 0,
                        reason: RequirementParameterUnsupportedReason::EffectFamily { .. },
                    }
                )
            ));
            assert_eq!(pending.parameter_uppers, vec![None]);
        },
    );
}

#[test]
fn role_impl_method_lifecycle_slice3_receiverless_shadow_matches_immediate_baseline() {
    use crate::role_impl_conformance::ActualMethodConformanceView;
    use crate::role_impl_conformance::view::ConformanceTypeView;

    let source = concat!(
        "role Make 'subject:\n",
        "  type output\n",
        "  our make: output\n",
        "impl Make int:\n",
        "  type output = int\n",
        "  our make = 1\n",
        "my observed = make\n",
    );
    let delayed = lower_receiverless_conformance_shadow(source, true);
    let immediate = lower_receiverless_conformance_shadow(source, false);

    assert_eq!(
        receiverless_production_surface(&delayed, "Make"),
        receiverless_production_surface(&immediate, "Make"),
        "delayed connection must preserve schemes, candidates, selections, diagnostics, and runtime IR",
    );
    assert_eq!(delayed.errors, immediate.errors);

    let [witness] = delayed.receiverless_conformance_shadow() else {
        panic!("expected one receiverless shadow witness")
    };
    assert_eq!(
        witness.actual_view,
        ActualMethodConformanceView::Available(ConformanceTypeView::Builtin(BuiltinType::Int)),
    );
    assert_eq!(witness.edge_applications, 1);
    assert_eq!(witness.releases, 1);
    assert_eq!(
        persisted_receiverless_actual_view(&delayed, witness.member),
        &witness.actual_view,
    );
    let delayed_transitions = delayed.session.scc.conformance_transition_counts();
    assert_eq!(delayed_transitions.pending, 1);
    assert_eq!(delayed_transitions.released, 1);
    assert_eq!(delayed_transitions.ignored_pending, 0);
    assert_eq!(delayed_transitions.ignored_released, 0);
    assert!(immediate.receiverless_conformance_shadow().is_empty());
    assert_eq!(
        immediate.session.scc.conformance_transition_counts(),
        crate::scc::ConformanceTransitionCounts::default(),
    );
}

#[test]
fn role_impl_method_lifecycle_slice3_unavailable_capture_still_releases() {
    use crate::role_impl_conformance::{
        ActualMethodConformanceView, ActualMethodConformanceViewUnavailable,
    };

    let source = concat!(
        "role Make 'subject:\n",
        "  our make: 'subject\n",
        "impl Make 'a:\n",
        "  our make = \\x -> x\n",
    );
    let output = lower_receiverless_conformance_shadow(source, true);
    let [witness] = output.receiverless_conformance_shadow() else {
        panic!("expected one failed receiverless shadow witness")
    };
    assert_eq!(
        witness.actual_view,
        ActualMethodConformanceView::Unavailable(
            ActualMethodConformanceViewUnavailable::UnsupportedFunction,
        ),
    );
    assert_eq!(witness.edge_applications, 1);
    assert_eq!(witness.releases, 1);
    assert_eq!(
        persisted_receiverless_actual_view(&output, witness.member),
        &witness.actual_view,
    );
    let transitions = output.session.scc.conformance_transition_counts();
    assert_eq!((transitions.pending, transitions.released), (1, 1));
    assert!(!output.session.has_pending_work());
    assert!(output.session.scc.is_quantified(witness.member));
}

#[test]
fn role_impl_method_lifecycle_slice3_keeps_out_of_scope_methods_immediate() {
    let inferred_associated = concat!(
        "role Make 'subject:\n",
        "  type output\n",
        "  our make: output\n",
        "impl Make int:\n",
        "  our make = 1\n",
    );
    let unsupported_declared_function = concat!(
        "role Make 'subject:\n",
        "  our make: int -> int\n",
        "impl Make int:\n",
        "  our make x = x\n",
    );

    for source in [inferred_associated, unsupported_declared_function] {
        let output = lower_receiverless_conformance_shadow(source, true);
        assert!(output.receiverless_conformance_shadow().is_empty());
        assert!(
            output
                .role_impl_conformance_contracts()
                .iter()
                .all(|contract| contract.actual_method_views().is_empty()),
            "an out-of-scope receiverless method has no pending snapshot to hand off",
        );
        assert_eq!(
            output.session.scc.conformance_transition_counts(),
            crate::scc::ConformanceTransitionCounts::default(),
        );
    }
}

#[test]
fn role_impl_method_lifecycle_slice3_ordinary_blocker_fails_capture_without_deadlock() {
    use crate::role_impl_conformance::{
        ActualMethodConformanceView, ActualMethodConformanceViewUnavailable,
    };

    let source = concat!(
        "role Make 'subject:\n",
        "  our make: 'subject\n",
        "impl Make 'a:\n",
        "  our make = \\x -> x.value\n",
    );
    let output = lower_receiverless_conformance_shadow(source, true);
    let [witness] = output.receiverless_conformance_shadow() else {
        panic!("expected one ordinary-blocker shadow witness")
    };
    assert_eq!(
        witness.actual_view,
        ActualMethodConformanceView::Unavailable(
            ActualMethodConformanceViewUnavailable::OrdinarySccBlocker,
        ),
    );
    assert_eq!((witness.edge_applications, witness.releases), (1, 1));
    assert_eq!(
        persisted_receiverless_actual_view(&output, witness.member),
        &witness.actual_view,
    );
    let transitions = output.session.scc.conformance_transition_counts();
    assert_eq!((transitions.pending, transitions.released), (1, 1));
    assert!(!output.session.has_pending_work());
    assert!(output.session.scc.is_quantified(witness.member));
}

#[test]
fn role_impl_method_lifecycle_slice4a_split_is_identical_to_uninterrupted_plan() {
    let zero_tail = concat!(
        "type box 'a\n",
        "role Read 'subject:\n",
        "  our x.read: 'subject\n",
        "impl (box 'a): Read:\n",
        "  our x.read = x\n",
    );
    let multiple_tail = concat!(
        "type box 'a\n",
        "role Choose 'subject:\n",
        "  our x.choose: 'subject -> 'subject -> 'subject\n",
        "impl (box 'a): Choose:\n",
        "  our x.choose a b = a\n",
    );

    for (source, method, parameter_count) in [
        (zero_tail, "read", 0usize),
        (multiple_tail, "choose", 2usize),
    ] {
        let uninterrupted = slice4a_requirement_plan_witness(
            source,
            method,
            parameter_count,
            Slice4aRequirementPlanMode::Uninterrupted,
        );
        let split = slice4a_requirement_plan_witness(
            source,
            method,
            parameter_count,
            Slice4aRequirementPlanMode::Split,
        );
        assert_eq!(split, uninterrupted, "method: {method}");

        let anchors = receiver_method_anchor_witness(source, method, false).anchors;
        assert_eq!(anchors.tail_parameters.len(), parameter_count);
        assert_eq!(anchors.parameter_requirement_edges, parameter_count);
        assert_eq!(anchors.body_value_requirement_edges, 1);
        assert_eq!(anchors.body_effect_requirement_edges, 1);
        assert_eq!(anchors.method_value_requirement_edges, 0);
        assert_ne!(anchors.receiver, anchors.method_value);
        assert_ne!(anchors.body_value, anchors.method_value);
        if let Some(first_parameter) = anchors.tail_parameters.first() {
            assert_eq!(anchors.body_value, *first_parameter);
        } else {
            assert_eq!(anchors.body_value, anchors.receiver);
        }
    }

    assert_eq!(
        finalized_contract_method_scheme(zero_tail),
        "box 'a -> box 'a",
    );
    assert_eq!(
        finalized_contract_method_scheme(multiple_tail),
        "box 'a -> ('b & box 'a) -> box 'a -> 'b",
    );
}

#[test]
fn role_impl_method_lifecycle_slice4b_builds_inactive_receiver_descriptor_and_falls_back() {
    let zero_tail = concat!(
        "type box 'a\n",
        "role Read 'subject:\n",
        "  our x.read: 'subject\n",
        "impl (box 'a): Read:\n",
        "  our x.read = x\n",
    );
    let multiple_tail = concat!(
        "type box 'a\n",
        "role Choose 'subject:\n",
        "  our x.choose: 'subject -> 'subject -> 'subject\n",
        "impl (box 'a): Choose:\n",
        "  our x.choose a b = a\n",
    );

    for (source, method, parameter_count) in [
        (zero_tail, "read", 0usize),
        (multiple_tail, "choose", 2usize),
    ] {
        let lowered = receiver_method_anchor_witness(source, method, true);
        let descriptor = lowered
            .descriptor
            .expect("plain receiver method must complete an inactive descriptor");
        assert_eq!(
            descriptor.anchor,
            DeferredRequirementAnchor::Receiver {
                receiver: lowered.anchors.receiver,
            }
        );
        assert_eq!(descriptor.anchors.receiver, lowered.anchors.receiver);
        assert_eq!(
            descriptor.anchors.tail_parameters,
            lowered.anchors.tail_parameters
        );
        assert_eq!(descriptor.anchors.body_value, lowered.anchors.body_value);
        assert_eq!(descriptor.anchors.body_effect, lowered.anchors.body_effect);
        assert_eq!(
            descriptor.anchors.method_value,
            lowered.anchors.method_value
        );
        assert_eq!(descriptor.parameter_upper_count, parameter_count);
        assert!(descriptor.all_parameter_uppers_present);
        assert_eq!(
            descriptor.body_cursor,
            RequirementSpineCursor::FunctionResult {
                consumed_function_layers: parameter_count + 1,
            }
        );
        assert_eq!(
            descriptor.parameter_context,
            RequirementParameterContextStatus::Clean(
                NonMutatingRequirementClass::PlainValueParameters {
                    count: parameter_count,
                }
            )
        );
        assert_eq!(
            lowered.parameter_context,
            Some(descriptor.parameter_context.clone())
        );
        assert_eq!(
            descriptor.continuation_level,
            Some(descriptor.metadata_level)
        );
        assert!(!descriptor.final_connect_value_upper);
        assert_eq!(lowered.anchors.parameter_requirement_edges, parameter_count);
        assert_eq!(lowered.anchors.body_value_requirement_edges, 1);
        assert_eq!(lowered.anchors.body_effect_requirement_edges, 1);
        assert_eq!(lowered.anchors.method_value_requirement_edges, 0);

        let output = lower_receiverless_conformance_shadow(source, true);
        let transitions = output.session.scc.conformance_transition_counts();
        assert_eq!(
            (transitions.pending, transitions.released),
            (1, 1),
            "all structurally clean plain-tail receiver descriptors enter the pending path",
        );
        let immediate = lower_receiverless_conformance_shadow(source, false);
        let role = if method == "read" { "Read" } else { "Choose" };
        assert_eq!(
            receiverless_production_surface(&output, role),
            receiverless_production_surface(&immediate, role)
        );
    }

    assert_eq!(
        finalized_contract_method_scheme(zero_tail),
        "box 'a -> box 'a",
    );
    assert_eq!(
        finalized_contract_method_scheme(multiple_tail),
        "box 'a -> ('b & box 'a) -> box 'a -> 'b",
    );

    let effect_row_parameter = concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "role Consume 'subject 'effect:\n",
        "  our x.consume: '[tick; 'effect] -> unit\n",
        "impl Consume int 'e:\n",
        "  our x.consume action = ()\n",
    );
    let immediate = receiver_method_anchor_witness(effect_row_parameter, "consume", false);
    let fallback = receiver_method_anchor_witness(effect_row_parameter, "consume", true);
    assert_eq!(fallback.anchors, immediate.anchors);
    assert!(fallback.descriptor.is_none());
    assert!(matches!(
        fallback.parameter_context,
        Some(RequirementParameterContextStatus::Unsupported(
            RequirementParameterContextUnavailable {
                parameter_index: 0,
                reason: RequirementParameterUnsupportedReason::EffectRow,
            }
        ))
    ));
    let fallback_output = lower_receiverless_conformance_shadow(effect_row_parameter, true);
    let immediate_output = lower_receiverless_conformance_shadow(effect_row_parameter, false);
    assert_eq!(
        fallback_output.session.scc.conformance_transition_counts(),
        crate::scc::ConformanceTransitionCounts::default(),
        "effect-bearing parameters must remain on the immediate fallback path",
    );
    assert_eq!(
        receiverless_production_surface(&fallback_output, "Consume"),
        receiverless_production_surface(&immediate_output, "Consume")
    );

    let split_with_same_mutation = slice4a_requirement_plan_witness(
        multiple_tail,
        "choose",
        2,
        Slice4aRequirementPlanMode::SplitWithInjectedBridgeMutation,
    );
    let mutated_fallback = slice4a_requirement_plan_witness(
        multiple_tail,
        "choose",
        2,
        Slice4aRequirementPlanMode::ForcedMutatedFallback,
    );
    assert_eq!(mutated_fallback, split_with_same_mutation);
}

#[test]
fn role_impl_method_lifecycle_slice4c_t1_immediate_publication_matches_frozen_oracle() {
    let source = concat!(
        "my identity = \\value -> value\n",
        "my computed = identity 1\n",
    );
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let identity = binding_def_and_order(&lower.modules, module, "identity").0;
    let computed = binding_def_and_order(&lower.modules, module, "computed").0;
    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert!(
        crate::check::summarize_lowering(&output)
            .diagnostics
            .is_empty()
    );
    assert_eq!(
        slice4c_t1_binding_publication_witness(&output, identity),
        Slice4cT1BindingPublicationWitness {
            body_published: true,
            root_has_body_var_lower: true,
            fetch: BindingFetch::FetchValue,
            computed_runtime_root: false,
            quantified: true,
            scheme: "'a -> 'a".into(),
        }
    );
    assert_eq!(
        slice4c_t1_binding_publication_witness(&output, computed),
        Slice4cT1BindingPublicationWitness {
            body_published: true,
            root_has_body_var_lower: true,
            fetch: BindingFetch::FetchComputation,
            computed_runtime_root: true,
            quantified: true,
            scheme: "int".into(),
        }
    );
}

#[test]
fn role_impl_method_lifecycle_slice4c_t2_inactive_provisional_commit_publishes_once() {
    for suppress_runtime_root in [false, true] {
        let (output, method, def_finished_emissions, publication_commits) =
            lower_inactive_receiver_provisional_for_slice4c_t2(
                Evaluation::Computation,
                suppress_runtime_root,
                true,
            );

        assert_eq!(def_finished_emissions, 1);
        assert_eq!(publication_commits, 1);
        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert!(
            crate::check::summarize_lowering(&output)
                .diagnostics
                .is_empty()
        );
        assert_eq!(
            slice4c_t1_binding_publication_witness(&output, method),
            Slice4cT1BindingPublicationWitness {
                body_published: true,
                root_has_body_var_lower: true,
                fetch: BindingFetch::FetchComputation,
                computed_runtime_root: !suppress_runtime_root,
                quantified: true,
                scheme: "box 'a -> box 'a".into(),
            }
        );
    }
}

#[test]
fn role_impl_method_lifecycle_slice4c_t2_inactive_rejection_poison_is_natural_bottom() {
    let (output, method, def_finished_emissions, publication_commits) =
        lower_inactive_receiver_provisional_for_slice4c_t2(Evaluation::Computation, false, false);

    assert_eq!(def_finished_emissions, 1);
    assert_eq!(publication_commits, 0);
    assert!(matches!(
        output.errors.as_slice(),
        [BodyLoweringError::Expr {
            def,
            error: LoweringError::SignatureTypeMismatch { .. },
            ..
        }] if *def == method
    ));
    assert_eq!(
        slice4c_t1_binding_publication_witness(&output, method),
        Slice4cT1BindingPublicationWitness {
            body_published: false,
            root_has_body_var_lower: false,
            // No fetch was published; the SCC machine's absent-entry default is FetchValue.
            fetch: BindingFetch::FetchValue,
            computed_runtime_root: false,
            quantified: true,
            scheme: "never".into(),
        }
    );
}

#[test]
fn role_impl_method_lifecycle_slice4c_t3_build_failure_matches_immediate_baseline() {
    let source = concat!(
        "role Build 'subject:\n",
        "  our x.build: int\n",
        "impl int: Build:\n",
        "  our x.build = \\value -> value\n",
    );
    let (delayed, method) = lower_receiver_conformance_shadow(source, true, false, false);
    let (immediate, immediate_method) =
        lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!(method, immediate_method);
    assert_eq!(
        receiver_shadow_production_surface(&delayed, "Build"),
        receiver_shadow_production_surface(&immediate, "Build"),
        "a rejected delayed receiver must remain bodyless and compact naturally to Bottom",
    );

    let [witness] = delayed.receiver_conformance_shadow() else {
        panic!("expected one delayed receiver witness")
    };
    assert!(!witness.binding_committed);
    assert_eq!((witness.edge_applications, witness.releases), (1, 1));
    assert_eq!(
        persisted_receiver_actual_view(&delayed, witness.member),
        &witness.actual_view,
    );
    assert_eq!(
        (
            witness.def_finished_emissions,
            witness.binding_publication_commits
        ),
        (1, 0),
    );
    assert!(matches!(
        delayed.session.poly.defs.get(method),
        Some(Def::Let {
            body: None,
            scheme: Some(scheme),
            ..
        }) if poly::dump::format_scheme(&delayed.session.poly.typ, scheme) == "never"
    ));
    assert_eq!(computed_runtime_root_count(&delayed.session, method), 0);
    assert_eq!(
        delayed.session.scc.conformance_transition_counts(),
        crate::scc::ConformanceTransitionCounts {
            pending: 1,
            released: 1,
            ..Default::default()
        }
    );
}

#[test]
fn role_impl_method_lifecycle_slice4c_t3_valid_result_annotation_and_capture_failure_match_baseline()
 {
    use crate::role_impl_conformance::ActualMethodConformanceView;
    use crate::role_impl_conformance::view::ConformanceTypeView;

    let source = concat!(
        "role Read 'subject:\n",
        "  our x.read: int\n",
        "impl int: Read:\n",
        "  our x.read: int = 1\n",
        "my observed = 1.read\n",
    );
    let (delayed, method) = lower_receiver_conformance_shadow(source, true, false, false);
    let (immediate, _) = lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!(
        receiver_shadow_production_surface(&delayed, "Read"),
        receiver_shadow_production_surface(&immediate, "Read"),
    );
    assert!(delayed.errors.is_empty(), "{:?}", delayed.errors);

    let [witness] = delayed.receiver_conformance_shadow() else {
        panic!("expected one delayed receiver witness")
    };
    assert!(witness.binding_committed);
    assert_eq!(
        (
            witness.def_finished_emissions,
            witness.binding_publication_commits
        ),
        (1, 1),
    );
    assert_eq!(
        witness.actual_view.value,
        ActualMethodConformanceView::Available(ConformanceTypeView::Builtin(BuiltinType::Int)),
    );
    assert!(matches!(
        witness.actual_view.effect,
        ActualMethodConformanceView::Available(ConformanceTypeView::Bottom)
    ));
    assert_eq!(
        persisted_receiver_actual_view(&delayed, witness.member),
        &witness.actual_view,
    );
    assert!(matches!(
        delayed.session.poly.defs.get(method),
        Some(Def::Let {
            body: Some(_),
            scheme: Some(scheme),
            ..
        }) if poly::dump::format_scheme(&delayed.session.poly.typ, scheme) == "int -> int"
    ));
}

#[test]
fn role_impl_method_lifecycle_slice4c_t3_capture_failure_still_connects_and_commits() {
    use crate::role_impl_conformance::{
        ActualMethodConformanceView, ActualMethodConformanceViewUnavailable,
    };

    let source = concat!(
        "role Read 'subject:\n",
        "  our x.read: int\n",
        "impl int: Read:\n",
        "  our x.read = 1\n",
    );
    let (failed_capture, _) = lower_receiver_conformance_shadow(source, true, false, true);
    let (immediate, _) = lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!(
        receiver_shadow_production_surface(&failed_capture, "Read"),
        receiver_shadow_production_surface(&immediate, "Read"),
    );
    let [witness] = failed_capture.receiver_conformance_shadow() else {
        panic!("expected one delayed receiver witness")
    };
    assert!(witness.binding_committed);
    assert_eq!(
        (
            witness.def_finished_emissions,
            witness.binding_publication_commits
        ),
        (1, 1),
    );
    assert!(matches!(
        witness.actual_view.value,
        ActualMethodConformanceView::Unavailable(
            ActualMethodConformanceViewUnavailable::NonAtomicSurface
        )
    ));
    assert!(matches!(
        witness.actual_view.effect,
        ActualMethodConformanceView::Unavailable(
            ActualMethodConformanceViewUnavailable::NonAtomicSurface
        )
    ));
    assert_eq!(witness.actual_view.tail_parameter_count, Some(0));
    assert_eq!(
        persisted_receiver_actual_view(&failed_capture, witness.member),
        &witness.actual_view,
    );
}

#[test]
fn role_impl_method_lifecycle_slice4c_t3_internal_descriptor_gate_falls_back_immediately() {
    let source = concat!(
        "role Read 'subject:\n",
        "  our x.read: int\n",
        "impl int: Read:\n",
        "  our x.read = 1\n",
    );
    let (fallback, _) = lower_receiver_conformance_shadow(source, true, true, false);
    let (immediate, _) = lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!(
        receiver_shadow_production_surface(&fallback, "Read"),
        receiver_shadow_production_surface(&immediate, "Read"),
    );
    assert!(fallback.receiver_conformance_shadow().is_empty());
    assert!(
        fallback.role_impl_conformance_contracts()[0]
            .actual_method_views()
            .is_empty(),
        "an unsupported immediate fallback has no pending snapshot to hand off",
    );
    assert_eq!(
        fallback.session.scc.conformance_transition_counts(),
        crate::scc::ConformanceTransitionCounts::default(),
    );
}

#[test]
fn role_impl_method_lifecycle_slice4c_t3_mixed_receiverless_receiver_component_captures_atomically()
{
    let source = concat!(
        "role Pair 'subject:\n",
        "  our make: int\n",
        "  our x.read: int\n",
        "impl int: Pair:\n",
        "  our make = read\n",
        "  our x.read = make\n",
    );
    let (delayed, _) = lower_receiver_conformance_shadow(source, true, false, false);
    let (immediate, _) = lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!(
        receiver_shadow_production_surface(&delayed, "Pair"),
        receiver_shadow_production_surface(&immediate, "Pair"),
    );
    assert_eq!(delayed.receiverless_conformance_shadow().len(), 1);
    assert_eq!(delayed.receiver_conformance_shadow().len(), 1);
    let [contract] = delayed.role_impl_conformance_contracts() else {
        panic!("expected one mixed-method source contract")
    };
    assert_eq!(contract.actual_method_views().len(), 2);
    let receiverless = &delayed.receiverless_conformance_shadow()[0];
    assert_eq!(
        persisted_receiverless_actual_view(&delayed, receiverless.member),
        &receiverless.actual_view,
    );
    let receiver = &delayed.receiver_conformance_shadow()[0];
    assert_eq!(
        persisted_receiver_actual_view(&delayed, receiver.member),
        &receiver.actual_view,
    );
    let events = delayed.conformance_batch_events();
    assert_eq!(events.len(), 4, "{events:?}");
    assert!(matches!(
        events[0],
        super::super::body::ConformanceBatchEvent::Captured(_)
    ));
    assert!(matches!(
        events[1],
        super::super::body::ConformanceBatchEvent::Captured(_)
    ));
    assert!(matches!(
        events[2],
        super::super::body::ConformanceBatchEvent::RequirementApplied(_)
    ));
    assert!(matches!(
        events[3],
        super::super::body::ConformanceBatchEvent::RequirementApplied(_)
    ));
    assert_eq!(
        delayed.session.scc.conformance_transition_counts(),
        crate::scc::ConformanceTransitionCounts {
            pending: 2,
            released: 2,
            ..Default::default()
        }
    );
}

#[test]
fn role_impl_method_lifecycle_slice4c_t4_receiver_and_ordinary_binding_recurse_in_one_component() {
    let source = concat!(
        "role Eval 'subject:\n",
        "  our x.eval: int\n",
        "impl int: Eval:\n",
        "  our x.eval = helper\n",
        "  my helper = eval\n",
    );
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let implementation = lower.modules.role_impls(module)[0].clone();
    let method = implementation.methods[0].def;
    let helper = lower
        .modules
        .value_decls(implementation.body_module, &Name("helper".into()))[0]
        .def;

    let (mut delayed, delayed_method) =
        lower_receiver_conformance_shadow(source, true, false, false);
    let (immediate, immediate_method) =
        lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!((delayed_method, immediate_method), (method, method));
    assert_eq!(
        receiver_shadow_production_surface(&delayed, "Eval"),
        receiver_shadow_production_surface(&immediate, "Eval"),
    );

    let [witness] = delayed.receiver_conformance_shadow() else {
        panic!("expected one delayed receiver witness")
    };
    assert!(witness.binding_committed);
    assert_eq!(
        (
            witness.edge_applications,
            witness.releases,
            witness.def_finished_emissions,
            witness.binding_publication_commits,
        ),
        (1, 1, 1, 1),
    );

    let events = delayed.session.take_scc_events();
    assert!(
        events.iter().any(|event| {
            matches!(
                event,
                SccEvent::MergeComponents { merged, .. }
                    if merged.contains(&method) && merged.contains(&helper)
            )
        }),
        "missing method/helper component merge: {events:?}"
    );
    assert!(
        events.iter().any(|event| {
            matches!(
                event,
                SccEvent::QuantifyComponent { component, .. }
                    if component.contains(&method) && component.contains(&helper)
            )
        }),
        "missing joint method/helper quantification: {events:?}"
    );
}

#[test]
fn role_impl_method_lifecycle_slice4c_t4_forward_use_resolution_closes_component_cycle() {
    let source = concat!(
        "role Eval 'subject:\n",
        "  our x.eval: int\n",
        "impl int: Eval:\n",
        "  our x.eval = helper\n",
        "  my helper = eval\n",
    );
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let implementation = lower.modules.role_impls(module)[0].clone();
    let method = implementation.methods[0].def;
    let helper = lower
        .modules
        .value_decls(implementation.body_module, &Name("helper".into()))[0]
        .def;

    let (mut delayed, _) = lower_receiver_conformance_shadow(source, true, false, false);
    let events = delayed.session.take_scc_events();
    let first_edge = events
        .iter()
        .position(|event| {
            matches!(
                event,
                SccEvent::ComponentEdgeAdded { from, to }
                    if (from.contains(&method) && to.contains(&helper))
                        || (from.contains(&helper) && to.contains(&method))
            )
        })
        .unwrap_or_else(|| panic!("missing first method/helper use edge: {events:?}"));
    let merge = events
        .iter()
        .position(|event| {
            matches!(
                event,
                SccEvent::MergeComponents { components, merged }
                    if components.len() == 2
                        && components.iter().all(|component| component.len() == 1)
                        && merged.contains(&method)
                        && merged.contains(&helper)
            )
        })
        .unwrap_or_else(|| panic!("missing late method/helper merge: {events:?}"));
    let quantify = events
        .iter()
        .position(|event| {
            matches!(
                event,
                SccEvent::QuantifyComponent { component, .. }
                    if component.contains(&method) && component.contains(&helper)
            )
        })
        .unwrap_or_else(|| panic!("missing joint quantification: {events:?}"));

    assert!(
        first_edge < merge && merge < quantify,
        "the first resolved use must leave two components open; the reverse use closes the cycle before joint quantification: {events:?}",
    );
    assert_eq!(
        delayed
            .conformance_batch_events()
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    super::super::body::ConformanceBatchEvent::Captured(_)
                )
            })
            .count(),
        1,
    );
    assert_eq!(
        delayed
            .conformance_batch_events()
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    super::super::body::ConformanceBatchEvent::RequirementApplied(_)
                )
            })
            .count(),
        1,
    );
}

#[test]
fn role_impl_method_lifecycle_slice4c_t4_same_component_commits_success_and_poisons_failure() {
    let source = concat!(
        "role Pair 'subject:\n",
        "  our x.good: int\n",
        "  our x.bad: int\n",
        "impl int: Pair:\n",
        "  our x.good = { bad; 1 }\n",
        "  our x.bad = \\value -> { good; value }\n",
    );
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let implementation = lower.modules.role_impls(module)[0].clone();
    let good = implementation.methods[0].def;
    let bad = implementation.methods[1].def;

    let (mut delayed, _) = lower_receiver_conformance_shadow(source, true, false, false);
    let (immediate, _) = lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!(
        receiver_shadow_production_surface(&delayed, "Pair"),
        receiver_shadow_production_surface(&immediate, "Pair"),
    );

    assert_eq!(delayed.receiver_conformance_shadow().len(), 2);
    let good_witness = delayed
        .receiver_conformance_shadow()
        .iter()
        .find(|witness| witness.member == good)
        .expect("good receiver witness");
    let bad_witness = delayed
        .receiver_conformance_shadow()
        .iter()
        .find(|witness| witness.member == bad)
        .expect("bad receiver witness");
    assert!(good_witness.binding_committed);
    assert!(!bad_witness.binding_committed);
    assert_eq!(
        (
            good_witness.edge_applications,
            good_witness.releases,
            good_witness.def_finished_emissions,
            good_witness.binding_publication_commits,
        ),
        (1, 1, 1, 1),
    );
    assert_eq!(
        (
            bad_witness.edge_applications,
            bad_witness.releases,
            bad_witness.def_finished_emissions,
            bad_witness.binding_publication_commits,
        ),
        (1, 1, 1, 0),
    );
    assert!(matches!(
        delayed.session.poly.defs.get(good),
        Some(Def::Let {
            body: Some(_),
            scheme: Some(_),
            ..
        })
    ));
    assert!(matches!(
        delayed.session.poly.defs.get(bad),
        Some(Def::Let {
            body: None,
            scheme: Some(scheme),
            ..
        }) if poly::dump::format_scheme(&delayed.session.poly.typ, scheme) == "never"
    ));

    let events = delayed.conformance_batch_events();
    assert_eq!(events.len(), 4, "{events:?}");
    assert!(events[..2].iter().all(|event| matches!(
        event,
        super::super::body::ConformanceBatchEvent::Captured(_)
    )));
    assert!(events[2..].iter().all(|event| matches!(
        event,
        super::super::body::ConformanceBatchEvent::RequirementApplied(_)
    )));
    let scc_events = delayed.session.take_scc_events();
    assert!(
        scc_events.iter().any(|event| {
            matches!(
                event,
                SccEvent::MergeComponents { merged, .. }
                    if merged.contains(&good) && merged.contains(&bad)
            )
        }),
        "missing good/bad component merge: {scc_events:?}"
    );
    assert!(
        scc_events.iter().any(|event| {
            matches!(
                event,
                SccEvent::QuantifyComponent { component, .. }
                    if component.contains(&good) && component.contains(&bad)
            )
        }),
        "missing joint good/bad quantification: {scc_events:?}"
    );
}

#[test]
fn role_impl_method_lifecycle_slice4c_t4_computed_fetch_cycle_matches_immediate_timing() {
    let source = concat!(
        "my make_helper value = \\ignored -> value\n",
        "role Eval 'subject:\n",
        "  our x.eval: int\n",
        "impl int: Eval:\n",
        "  our x.eval = helper 0\n",
        "  my helper = make_helper eval\n",
    );
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let implementation = lower.modules.role_impls(module)[0].clone();
    let method = implementation.methods[0].def;
    let helper = lower
        .modules
        .value_decls(implementation.body_module, &Name("helper".into()))[0]
        .def;

    let (mut delayed, _) = lower_receiver_conformance_shadow(source, true, false, false);
    let (mut immediate, _) = lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!(
        receiver_shadow_production_surface(&delayed, "Eval"),
        receiver_shadow_production_surface(&immediate, "Eval"),
    );
    assert!(matches!(
        delayed.errors.as_slice(),
        [BodyLoweringError::Analysis(
            crate::analysis::AnalysisDiagnostic::ComputedFetchCycle {
                component,
                parent,
                target,
            }
        )] if component.contains(&method)
            && component.contains(&helper)
            && component.len() == 2
            && [*parent, *target].contains(&method)
            && [*parent, *target].contains(&helper)
    ));

    let delayed_events = delayed.session.take_scc_events();
    let immediate_events = immediate.session.take_scc_events();
    let cycle_event = |events: &[SccEvent]| {
        events
            .iter()
            .enumerate()
            .find_map(|(index, event)| match event {
                SccEvent::ComputedFetchCycle {
                    component,
                    parent,
                    target,
                } => Some((index, component.clone(), *parent, *target)),
                _ => None,
            })
    };
    assert_eq!(cycle_event(&delayed_events), cycle_event(&immediate_events));
    let (cycle_index, _, _, _) = cycle_event(&delayed_events).expect("computed-fetch-cycle event");
    let merge_index = delayed_events
        .iter()
        .position(|event| {
            matches!(
                event,
                SccEvent::MergeComponents { merged, .. }
                    if merged.contains(&method) && merged.contains(&helper)
            )
        })
        .expect("method/helper merge event");
    let quantify_index = delayed_events
        .iter()
        .position(|event| {
            matches!(
                event,
                SccEvent::QuantifyComponent { component, .. }
                    if component.contains(&method) && component.contains(&helper)
            )
        })
        .expect("method/helper quantification event");
    assert!(merge_index < cycle_index && cycle_index < quantify_index);
}

#[test]
fn role_impl_method_lifecycle_slice4d_plain_tail_parameters_match_immediate_baseline() {
    use crate::role_impl_conformance::view::{ConformanceBinder, ConformanceTypeView};
    use crate::role_impl_conformance::{
        ActualMethodConformanceView, ActualMethodConformanceViewUnavailable,
    };

    let single = concat!(
        "role Apply 'subject:\n",
        "  our x.apply: int -> int\n",
        "impl int: Apply:\n",
        "  our x.apply value = value\n",
        "my observed = 1.apply 2\n",
    );
    let multiple_annotated = concat!(
        "role Choose 'subject:\n",
        "  our x.choose: int -> bool -> int\n",
        "impl int: Choose:\n",
        "  our x.choose(value: int, flag: bool): int = value\n",
        "my observed = 1.choose 2 true\n",
    );
    let multiple_effect_result = concat!(
        "role Choose 'subject:\n",
        "  our x.choose: int -> bool -> [] int\n",
        "impl int: Choose:\n",
        "  our x.choose(value: int, flag: bool): [] int = value\n",
        "my observed = 1.choose 2 true\n",
    );

    for (source, role, parameter_count, pure_effect_anchor) in [
        (single, "Apply", 1usize, true),
        (multiple_annotated, "Choose", 2usize, true),
        (multiple_effect_result, "Choose", 2usize, false),
    ] {
        let (delayed, _) = lower_receiver_conformance_shadow(source, true, false, false);
        let (immediate, _) = lower_receiver_conformance_shadow(source, false, false, false);
        assert_eq!(
            receiver_shadow_production_surface(&delayed, role),
            receiver_shadow_production_surface(&immediate, role),
            "parameter_count={parameter_count}",
        );
        assert!(delayed.errors.is_empty(), "{:?}", delayed.errors);
        let [witness] = delayed.receiver_conformance_shadow() else {
            panic!("expected one delayed receiver witness for {parameter_count} parameters")
        };
        assert!(witness.binding_committed);
        assert_eq!(
            persisted_receiver_actual_view(&delayed, witness.member),
            &witness.actual_view,
        );
        assert_eq!(
            witness.actual_view.tail_parameter_count,
            Some(parameter_count),
        );
        assert!(
            matches!(
                (parameter_count, &witness.actual_view.value),
                (
                    1,
                    ActualMethodConformanceView::Available(ConformanceTypeView::Binder(
                        ConformanceBinder::MethodQuantifier(0)
                    ))
                ) | (
                    2,
                    ActualMethodConformanceView::Available(ConformanceTypeView::Builtin(
                        BuiltinType::Int
                    ))
                )
            ),
            "parameter_count={parameter_count}: {:?}",
            witness.actual_view.value
        );
        assert!(
            if pure_effect_anchor {
                matches!(
                    witness.actual_view.effect,
                    ActualMethodConformanceView::Available(ConformanceTypeView::Bottom)
                )
            } else {
                matches!(
                    witness.actual_view.effect,
                    ActualMethodConformanceView::Unavailable(
                        ActualMethodConformanceViewUnavailable::WeightedVariable
                    )
                )
            },
            "parameter_count={parameter_count}: {:?}",
            witness.actual_view.effect,
        );
        assert_eq!(
            (
                witness.edge_applications,
                witness.releases,
                witness.def_finished_emissions,
                witness.binding_publication_commits,
            ),
            (1, 1, 1, 1),
        );
        assert_eq!(
            delayed.session.scc.conformance_transition_counts(),
            crate::scc::ConformanceTransitionCounts {
                pending: 1,
                released: 1,
                ..Default::default()
            },
        );
    }
}

#[test]
fn role_impl_method_lifecycle_slice4d_missing_parameter_layer_falls_back_immediately() {
    let source = concat!(
        "role Choose 'subject:\n",
        "  our x.choose: int -> int\n",
        "impl int: Choose:\n",
        "  our x.choose first second = first\n",
    );
    with_requirement_harness(source, "choose", |lowerer, requirement, bindings, vars| {
        let receiver = lowerer.fresh_type_var();
        let deferred = lowerer
            .deferred_impl_method_requirement(
                DeferredRequirementAnchor::Receiver { receiver },
                Arc::clone(requirement),
                2,
                true,
                bindings,
                vars,
            )
            .expect("unsupported descriptor classification");
        assert!(matches!(
            deferred.parameter_context,
            RequirementParameterContextStatus::Unsupported(
                RequirementParameterContextUnavailable {
                    parameter_index: 1,
                    reason: RequirementParameterUnsupportedReason::MissingFunctionLayer,
                }
            )
        ));
    });

    let (delayed, _) = lower_receiver_conformance_shadow(source, true, false, false);
    let (immediate, _) = lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!(
        receiver_shadow_production_surface(&delayed, "Choose"),
        receiver_shadow_production_surface(&immediate, "Choose"),
    );
    assert!(delayed.receiver_conformance_shadow().is_empty());
    assert!(
        delayed.role_impl_conformance_contracts()[0]
            .actual_method_views()
            .is_empty(),
        "an unsupported parameter spine remains on the immediate path",
    );
    assert_eq!(
        delayed.session.scc.conformance_transition_counts(),
        crate::scc::ConformanceTransitionCounts::default(),
    );
}

#[test]
fn role_impl_method_lifecycle_slice4d_mixed_component_captures_multi_tail_atomically() {
    let source = concat!(
        "role Pair 'subject:\n",
        "  our make: int\n",
        "  our x.choose: int -> int -> int\n",
        "impl int: Pair:\n",
        "  our make = choose 1 2\n",
        "  our x.choose first second = { make; first }\n",
    );
    let (delayed, _) = lower_receiver_conformance_shadow(source, true, false, false);
    let (immediate, _) = lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!(
        receiver_shadow_production_surface(&delayed, "Pair"),
        receiver_shadow_production_surface(&immediate, "Pair"),
    );
    assert_eq!(delayed.receiverless_conformance_shadow().len(), 1);
    assert_eq!(delayed.receiver_conformance_shadow().len(), 1);
    assert!(delayed.receiver_conformance_shadow()[0].binding_committed);
    let events = delayed.conformance_batch_events();
    assert_eq!(events.len(), 4, "{events:?}");
    assert!(events[..2].iter().all(|event| matches!(
        event,
        super::super::body::ConformanceBatchEvent::Captured(_)
    )));
    assert!(events[2..].iter().all(|event| matches!(
        event,
        super::super::body::ConformanceBatchEvent::RequirementApplied(_)
    )));
    assert_eq!(
        delayed.session.scc.conformance_transition_counts(),
        crate::scc::ConformanceTransitionCounts {
            pending: 2,
            released: 2,
            ..Default::default()
        },
    );
}

#[test]
fn generic_role_impl_conformance_stage2_slice6_persists_poisoned_receiver_snapshot() {
    use crate::role_impl_conformance::ActualMethodConformanceView;
    use crate::role_impl_conformance::view::ConformanceTypeView;

    let source = concat!(
        "role Read 'subject:\n",
        "  our x.read: int\n",
        "impl int: Read:\n",
        "  our x.read = true\n",
    );
    let (delayed, _) = lower_receiver_conformance_shadow(source, true, false, false);
    let (immediate, _) = lower_receiver_conformance_shadow(source, false, false, false);
    assert_eq!(
        receiver_shadow_production_surface(&delayed, "Read"),
        receiver_shadow_production_surface(&immediate, "Read"),
    );

    let [witness] = delayed.receiver_conformance_shadow() else {
        panic!("expected one poisoned receiver witness")
    };
    assert!(!witness.binding_committed);
    assert_eq!(
        witness.actual_view.value,
        ActualMethodConformanceView::Available(ConformanceTypeView::Builtin(BuiltinType::Bool)),
    );
    assert!(matches!(
        witness.actual_view.effect,
        ActualMethodConformanceView::Available(ConformanceTypeView::Bottom)
    ));
    assert_eq!(
        persisted_receiver_actual_view(&delayed, witness.member),
        &witness.actual_view,
    );
}

#[test]
fn generic_role_impl_conformance_stage2_slice6_exit_hands_off_declared_and_actual_together() {
    use crate::role_impl_conformance::RoleImplMethodActualSurface;
    use crate::role_impl_conformance::view::DeclaredTypeView;

    let alpha_a = concat!(
        "role Same 'subject:\n",
        "  our x.same: 'subject\n",
        "impl 'a: Same:\n",
        "  our x.same = x\n",
    );
    let alpha_b = concat!(
        "role Same 'subject:\n",
        "  our x.same: 'subject\n",
        "impl 'renamed: Same:\n",
        "  our x.same = x\n",
    );

    let exit_view = |source| {
        let (output, member) = lower_receiver_conformance_shadow(source, true, false, false);
        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let [contract] = output.role_impl_conformance_contracts() else {
            panic!("expected one source conformance contract")
        };
        let declared = contract.declared_view(&output.modules);
        let DeclaredTypeView::Available(declared_input) = &declared.inputs[0] else {
            panic!("expected first-order declared impl input: {declared:?}")
        };
        let actual_method = contract
            .actual_method_view(member)
            .expect("the same contract must own the actual method handoff");
        let RoleImplMethodActualSurface::Receiver(actual) = &actual_method.surface else {
            panic!("expected receiver actual handoff: {actual_method:?}")
        };
        let crate::role_impl_conformance::ActualMethodConformanceView::Available(actual_value) =
            &actual.value
        else {
            panic!("expected first-order receiver value: {actual:?}")
        };
        assert_eq!(
            actual_value, declared_input,
            "the Exit witness observes declared and actual U0 through one contract",
        );
        (
            declared_input.clone(),
            RoleImplMethodActualSurface::Receiver(actual.clone()),
        )
    };

    assert_eq!(exit_view(alpha_a), exit_view(alpha_b));
}

#[test]
fn generic_role_impl_conformance_stage1_slice2_classifies_all_method_provisions() {
    let source = concat!(
        "role Demo 'subject:\n",
        "  our x.required: unit\n",
        "  our x.defaulted = ()\n",
        "  our x.missing: unit\n",
        "impl int: Demo:\n",
        "  our x.required = ()\n",
        "  our x.required = ()\n",
        "  our extra = ()\n",
    );

    assert_eq!(
        characterize_method_contract(source),
        concat!(
            "substitution=inputs=[subject->input0] associated=[] ambiguous=[]\n",
            "methods=[required=explicit(2);refs=[input0] | defaulted=default;refs=[] | missing=missing;refs=[input0]] unmatched=[extra]",
        ),
    );
}

/// The parser/module map currently accepts an input and associated declaration with the same
/// spelling. The contract keeps both slots and records requirement occurrences as ambiguous rather
/// than silently choosing one. Enforcement remains a later-stage language decision.
#[test]
fn generic_role_impl_conformance_stage1_slice2_characterizes_same_name_slots() {
    let source = concat!(
        "role Clash 'a:\n",
        "  type a\n",
        "  our x.read: a\n",
        "impl int: Clash:\n",
        "  type a = int\n",
        "  our x.read = 1\n",
    );

    assert_eq!(
        characterize_method_contract(source),
        concat!(
            "substitution=inputs=[a->input0] associated=[a->] ambiguous=[a]\n",
            "methods=[read=explicit(1);refs=[];ambiguous=[a]] unmatched=[]",
        ),
    );
}

#[test]
fn generic_role_impl_conformance_stage1_slice2_recovers_imported_default_body() {
    let source = concat!(
        "role Demo 'subject:\n",
        "  our x.defaulted = ()\n",
        "impl int: Demo:\n",
    );
    let root = parse(source);
    let lower = lower_module_map(&root);
    let role = lower
        .modules
        .type_decls(lower.modules.root_id(), &Name("Demo".into()))[0]
        .clone();
    let default_method = lower.modules.role_methods(role.id)[0].def;
    let output = lower_binding_bodies(&root, lower);
    let runtime = crate::CompiledRuntimeSurface::from_lowering(&output);
    let mut imported_poly = poly::expr::Arena::new();
    let padding = imported_poly.defs.fresh();
    imported_poly.defs.set(padding, Def::Arg);
    let mut labels = poly::dump::DumpLabels::new();
    let import = runtime.import_into(&mut imported_poly, &mut labels);
    let imported_method = import.map_def(default_method);

    assert_ne!(imported_method, default_method);
    assert!(
        !output
            .modules
            .role_method_has_source_default_body(imported_method)
    );
    assert!(crate::role_impl_conformance::role_method_has_default_body(
        &output.modules,
        &imported_poly,
        imported_method,
    ));
}

struct Fixture {
    name: &'static str,
    role: &'static str,
    source: &'static str,
    current: &'static str,
}

#[derive(Debug)]
enum LifecycleEvent {
    RegisterDef(DefId),
    RequirementDependency(DefId),
    Merge(Vec<DefId>),
    Quantify(Vec<DefId>),
}

struct LifecycleFixture {
    name: &'static str,
    role: &'static str,
    source: &'static str,
    ordinary_binding: Option<&'static str>,
    expect_multi_member_component: bool,
    observe_dependency_edge: bool,
}

fn timeline_position(
    timeline: &[LifecycleEvent],
    predicate: impl Fn(&LifecycleEvent) -> bool,
) -> usize {
    timeline
        .iter()
        .position(predicate)
        .unwrap_or_else(|| panic!("missing lifecycle event in {timeline:?}"))
}

fn with_requirement_harness<R>(
    source: &str,
    method_name: &str,
    test: impl FnOnce(
        &mut ExprLowerer<'_>,
        &Arc<ResolvedRoleMethodRequirement>,
        &[(String, AnnTypeVarId)],
        &mut rustc_hash::FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> R,
) -> R {
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let implementation = lower.modules.role_impls(module)[0].clone();
    let impl_node = root
        .children()
        .find(|child| child.kind() == SyntaxKind::ImplDecl)
        .expect("role impl declaration");
    let mut body_lowerer = super::super::body::BodyLowerer::new(lower);
    let mut context = body_lowerer
        .register_role_impl_candidate(
            &impl_node,
            implementation.def,
            implementation.module,
            implementation.order,
            None,
        )
        .expect("role impl lowering context");
    let role_method = body_lowerer
        .modules
        .role_methods(context.role)
        .iter()
        .find(|method| method.name == Name(method_name.into()))
        .expect("role method requirement");
    let stored = body_lowerer
        .role_requirements
        .get(&role_method.def)
        .expect("stored role method requirement");
    let requirement = Arc::new(ResolvedRoleMethodRequirement {
        role_method: role_method.def,
        role: body_lowerer
            .modules
            .type_decl_path(
                &body_lowerer
                    .modules
                    .type_decl_by_id(context.role)
                    .expect("role declaration"),
            )
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect(),
        inputs: context.input_signatures.clone(),
        associated: context.associated_signatures.clone(),
        signature: substitute_role_requirement_signature(stored, &context),
    });
    let method = implementation
        .methods
        .iter()
        .find(|method| method.name == Name(method_name.into()))
        .expect("role impl method");
    let mut expr_lowerer = ExprLowerer::new(
        &mut body_lowerer.session,
        &body_lowerer.modules,
        implementation.body_module,
        method.order,
        method.def,
    );
    test(
        &mut expr_lowerer,
        &requirement,
        &context.type_var_bindings,
        &mut context.ann_solver_vars,
    )
}

#[derive(Debug, Clone, Copy)]
enum Slice4aRequirementPlanMode {
    Uninterrupted,
    Split,
    SplitWithInjectedBridgeMutation,
    ForcedMutatedFallback,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Slice4aRequirementPlanWitness {
    parameter_uppers: Vec<Option<NegId>>,
    parameter_upper_shapes: Vec<Option<String>>,
    body_uppers: Option<(NegId, NegId)>,
    body_upper_shapes: Option<(String, String)>,
    bridge_vars: Vec<(String, TypeVar)>,
    bridge_after_plan: Vec<(String, BridgeState)>,
    epoch_after_plan: crate::constraints::ConstraintEpoch,
    next_type_var_after_plan: u32,
    parameter_connections: usize,
    body_value_connections: usize,
    body_effect_connections: usize,
    final_method_connections: usize,
    bridge_after_final: Vec<(String, BridgeState)>,
    epoch_after_final: crate::constraints::ConstraintEpoch,
    next_type_var_after_final: u32,
}

fn slice4a_requirement_plan_witness(
    source: &str,
    method_name: &str,
    parameter_count: usize,
    mode: Slice4aRequirementPlanMode,
) -> Slice4aRequirementPlanWitness {
    with_requirement_harness(
        source,
        method_name,
        |lowerer, requirement, bindings, vars| {
            let receiver = lowerer.fresh_type_var();
            let plan = match mode {
                Slice4aRequirementPlanMode::Uninterrupted => lowerer
                    .uninterrupted_impl_method_requirement_plan_for_slice4a(
                        &requirement.signature,
                        parameter_count,
                        true,
                        bindings,
                        vars,
                    ),
                Slice4aRequirementPlanMode::Split => {
                    let parameters = lowerer
                        .prepare_impl_method_requirement_parameters(
                            &requirement.signature,
                            parameter_count,
                            true,
                            bindings,
                            vars,
                        )
                        .expect("split parameter preparation");
                    lowerer.resume_impl_method_requirement_body(&requirement.signature, parameters)
                }
                Slice4aRequirementPlanMode::SplitWithInjectedBridgeMutation => {
                    let parameters = lowerer
                        .prepare_impl_method_requirement_parameters(
                            &requirement.signature,
                            parameter_count,
                            true,
                            bindings,
                            vars,
                        )
                        .expect("split parameter preparation");
                    let _ = inject_receiver_parameter_bridge_mutation(
                        lowerer,
                        parameter_count,
                        bindings,
                        vars,
                    );
                    lowerer.resume_impl_method_requirement_body(&requirement.signature, parameters)
                }
                Slice4aRequirementPlanMode::ForcedMutatedFallback => {
                    let deferred = lowerer
                        .deferred_impl_method_requirement(
                            DeferredRequirementAnchor::Receiver { receiver },
                            Arc::clone(requirement),
                            parameter_count,
                            true,
                            bindings,
                            vars,
                        )
                        .expect("receiver descriptor preparation");
                    assert!(matches!(
                        deferred.parameter_context,
                        RequirementParameterContextStatus::Clean(_)
                    ));
                    let mutation = inject_receiver_parameter_bridge_mutation(
                        lowerer,
                        parameter_count,
                        bindings,
                        vars,
                    );
                    lowerer.force_mutated_receiver_requirement_fallback_for_slice4b(
                        deferred,
                        mutation,
                        parameter_count,
                        bindings,
                        vars,
                    )
                }
            }
            .expect("receiver requirement plan");

            let parameter_uppers = plan.param_uppers.clone();
            let body = plan.body;
            let constraints = lowerer.session.infer.constraints();
            let parameter_upper_shapes = parameter_uppers
                .iter()
                .map(|upper| upper.map(|upper| poly::dump::format_neg(constraints.types(), upper)))
                .collect::<Vec<_>>();
            let body_uppers = body.map(|body| (body.effect_upper, body.value_upper));
            let body_upper_shapes = body.map(|body| {
                (
                    poly::dump::format_neg(constraints.types(), body.effect_upper),
                    poly::dump::format_neg(constraints.types(), body.value_upper),
                )
            });
            let mut bridge_vars = bindings
                .iter()
                .filter_map(|(name, annotation)| {
                    vars.get(annotation).copied().map(|var| (name.clone(), var))
                })
                .collect::<Vec<_>>();
            bridge_vars.sort_by(|left, right| left.0.cmp(&right.0));
            bridge_vars.dedup();
            let bridge_after_plan = bridge_vars
                .iter()
                .map(|(name, var)| (name.clone(), bridge_state(lowerer, *var)))
                .collect::<Vec<_>>();
            let epoch_after_plan = constraints.epoch();
            let next_type_var_after_plan = constraints.next_type_var();

            let mut parameter_connections = 0usize;
            for upper in parameter_uppers.iter().flatten().copied() {
                let actual = lowerer.fresh_type_var();
                let before = upper_bound_count(lowerer, actual);
                let lower = lowerer.alloc_pos(Pos::Var(actual));
                lowerer.session.infer.subtype(lower, upper);
                parameter_connections += upper_bound_count(lowerer, actual) - before;
            }

            let body_value = lowerer.fresh_type_var();
            let body_effect = lowerer.fresh_type_var();
            let value_before = upper_bound_count(lowerer, body_value);
            let effect_before = upper_bound_count(lowerer, body_effect);
            let computation = Computation::value(
                lowerer.session.poly.add_expr(Expr::Tuple(Vec::new())),
                body_value,
                body_effect,
            );
            lowerer
                .connect_impl_method_body_requirement(computation, body.expect("body requirement"));
            let body_value_connections = upper_bound_count(lowerer, body_value) - value_before;
            let body_effect_connections = upper_bound_count(lowerer, body_effect) - effect_before;

            let method_value = lowerer.fresh_type_var();
            let method_before = upper_bound_count(lowerer, method_value);
            lowerer
                .connect_impl_method_requirement(method_value, requirement, bindings, vars, false)
                .expect("receiver final metadata");
            let final_method_connections = upper_bound_count(lowerer, method_value) - method_before;
            let constraints = lowerer.session.infer.constraints();
            let bridge_after_final = bridge_vars
                .iter()
                .map(|(name, var)| (name.clone(), bridge_state(lowerer, *var)))
                .collect::<Vec<_>>();

            Slice4aRequirementPlanWitness {
                parameter_uppers,
                parameter_upper_shapes,
                body_uppers,
                body_upper_shapes,
                bridge_vars,
                bridge_after_plan,
                epoch_after_plan,
                next_type_var_after_plan,
                parameter_connections,
                body_value_connections,
                body_effect_connections,
                final_method_connections,
                bridge_after_final,
                epoch_after_final: constraints.epoch(),
                next_type_var_after_final: constraints.next_type_var(),
            }
        },
    )
}

fn inject_receiver_parameter_bridge_mutation(
    lowerer: &mut ExprLowerer<'_>,
    parameter_count: usize,
    bindings: &[(String, AnnTypeVarId)],
    vars: &rustc_hash::FxHashMap<AnnTypeVarId, TypeVar>,
) -> BridgeMutationAudit {
    let before = lowerer.requirement_bridge_audit_snapshot(bindings, vars);
    let bridge = bindings
        .iter()
        .find_map(|(_, annotation)| vars.get(annotation).copied())
        .expect("receiver fixture bridge");
    lowerer.constrain_lower(
        bridge,
        Pos::Con(
            vec![BuiltinType::Int.surface_name().to_string()],
            Vec::new(),
        ),
    );
    let status = lowerer.requirement_parameter_context_since(
        NonMutatingRequirementClass::PlainValueParameters {
            count: parameter_count,
        },
        before,
        bindings,
        vars,
    );
    let RequirementParameterContextStatus::MutatedBridge(audit) = status else {
        panic!("injected bridge lower bound must be detected")
    };
    assert!(audit.epoch_after > audit.epoch_before);
    assert!(audit.affected.iter().any(|affected| {
        affected.solver_var == bridge && affected.bounds_changed && !affected.subtract_facts_changed
    }));
    audit
}

#[derive(Debug)]
struct ReceiverExactEquivalenceWitness {
    accessor_instantiations: Vec<TypeVar>,
    exact_class: Vec<TypeVar>,
    unrelated_anchors: Vec<TypeVar>,
    bridge_identities: Vec<crate::role_impl_conformance::view::ConformanceBinder>,
}

fn receiver_exact_equivalence_witness(
    source: &str,
    method_name: &str,
) -> ReceiverExactEquivalenceWitness {
    use crate::role_impl_conformance::RoleImplMethodProvision;
    use crate::role_impl_conformance::view::{
        ActualMethodConformanceView, ActualMethodConformanceViewUnavailable,
        ExactEquivalenceClasses,
    };

    let output = lower_conformance_fixture(source);
    let [contract] = output.role_impl_conformance_contracts() else {
        panic!("fixture must retain one source conformance contract")
    };
    let method = contract
        .methods
        .iter()
        .find(|method| method.name == method_name)
        .unwrap_or_else(|| panic!("missing role method {method_name}"));
    let RoleImplMethodProvision::Explicit { implementations } = &method.provision else {
        panic!("fixture method must be explicit: {:?}", method.provision)
    };
    let [implementation] = implementations.as_slice() else {
        panic!("fixture method must have one implementation: {implementations:?}")
    };
    let actual = contract
        .actual_method_view(implementation.def)
        .expect("captured receiver actual surface");
    let crate::role_impl_conformance::RoleImplMethodActualSurface::Receiver(actual) =
        &actual.surface
    else {
        panic!("fixture method must be a receiver method")
    };
    assert_eq!(
        actual.value,
        ActualMethodConformanceView::Unavailable(
            ActualMethodConformanceViewUnavailable::NonAtomicSurface,
        ),
        "EQ1 fixture must retain today's non-atomic capture baseline",
    );

    let bridge = contract
        .binder_bridge
        .as_ref()
        .expect("complete conformance binder bridge");
    let [(_, u0_bridge)] = bridge.universals.as_slice() else {
        panic!("fixture must expose exactly one universal bridge: {bridge:?}")
    };
    let mut exact_classes = ExactEquivalenceClasses::new(output.session.infer.constraints());
    let exact_class = exact_classes.class(*u0_bridge);
    let mut unrelated_anchors = [contract.impl_def, implementation.def]
        .into_iter()
        .filter_map(|def| output.typing.def(def))
        .collect::<Vec<_>>();
    unrelated_anchors.sort_unstable_by_key(|var| var.0);
    unrelated_anchors.dedup();
    let bridged_vars = bridge
        .universals
        .iter()
        .map(|(_, var)| *var)
        .chain(bridge.inferred_associated.iter().map(|(_, var)| *var))
        .collect::<rustc_hash::FxHashSet<_>>();
    let accessor_instantiations = exact_class
        .iter()
        .copied()
        .filter(|var| !bridged_vars.contains(var))
        .collect::<Vec<_>>();
    let bridge_identities = bridge_identities_in_class(bridge, &exact_class);

    ReceiverExactEquivalenceWitness {
        accessor_instantiations,
        exact_class,
        unrelated_anchors,
        bridge_identities,
    }
}

fn add_var_constraint(
    machine: &mut crate::constraints::ConstraintMachine,
    lower: TypeVar,
    weights: crate::constraints::ConstraintWeights,
    upper: TypeVar,
) {
    let lower = machine.alloc_pos(Pos::Var(lower));
    let upper = machine.alloc_neg(Neg::Var(upper));
    machine.weighted_subtype(lower, weights, upper);
}

fn bridge_identities_in_class(
    bridge: &crate::role_impl_conformance::RoleImplConformanceBinderBridge,
    class: &[TypeVar],
) -> Vec<crate::role_impl_conformance::view::ConformanceBinder> {
    use crate::role_impl_conformance::view::ConformanceBinder;

    let mut identities = bridge
        .universals
        .iter()
        .filter_map(|(binder, var)| {
            class
                .contains(var)
                .then_some(ConformanceBinder::Universal(*binder))
        })
        .chain(
            bridge
                .inferred_associated
                .iter()
                .filter_map(|(binder, var)| {
                    class
                        .contains(var)
                        .then_some(ConformanceBinder::InferredAssociated(*binder))
                }),
        )
        .collect::<Vec<_>>();
    identities.sort();
    identities.dedup();
    identities
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReceiverMethodAnchorWitness {
    receiver: TypeVar,
    tail_parameters: Vec<TypeVar>,
    body_value: TypeVar,
    body_effect: TypeVar,
    method_value: TypeVar,
    parameter_requirement_edges: usize,
    body_value_requirement_edges: usize,
    body_effect_requirement_edges: usize,
    method_value_requirement_edges: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReceiverDescriptorWitness {
    anchor: DeferredRequirementAnchor,
    anchors: crate::lowering::expr::method_body::ReceiverMethodLoweringAnchors,
    parameter_upper_count: usize,
    all_parameter_uppers_present: bool,
    body_cursor: RequirementSpineCursor,
    parameter_context: RequirementParameterContextStatus,
    continuation_level: Option<crate::constraints::TypeLevel>,
    metadata_level: crate::constraints::TypeLevel,
    final_connect_value_upper: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReceiverMethodLoweringWitness {
    anchors: ReceiverMethodAnchorWitness,
    descriptor: Option<ReceiverDescriptorWitness>,
    parameter_context: Option<RequirementParameterContextStatus>,
}

fn receiver_method_anchor_witness(
    source: &str,
    method_name: &str,
    prepare_inactive_receiver_requirement: bool,
) -> ReceiverMethodLoweringWitness {
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let implementation = lower.modules.role_impls(module)[0].clone();
    let impl_node = root
        .children()
        .find(|child| child.kind() == SyntaxKind::ImplDecl)
        .expect("role impl declaration");
    let binding = crate::role_impl_body(&impl_node)
        .expect("role impl body")
        .children()
        .find(|child| {
            crate::role_impl_method_binding(child)
                .is_some_and(|method| method.name == Name(method_name.into()))
        })
        .expect("role impl method binding");
    let method_syntax = crate::role_impl_method_binding(&binding).expect("method syntax");
    let method = implementation
        .methods
        .iter()
        .find(|method| method.name == Name(method_name.into()))
        .expect("role impl method");
    let mut body_lowerer = super::super::body::BodyLowerer::new(lower);
    let mut context = body_lowerer
        .register_role_impl_candidate(
            &impl_node,
            implementation.def,
            implementation.module,
            implementation.order,
            None,
        )
        .expect("role impl lowering context");
    let role_method = body_lowerer
        .modules
        .role_methods(context.role)
        .iter()
        .find(|method| method.name == Name(method_name.into()))
        .expect("role method requirement");
    let stored = body_lowerer
        .role_requirements
        .get(&role_method.def)
        .expect("stored role method requirement");
    let requirement = Arc::new(ResolvedRoleMethodRequirement {
        role_method: role_method.def,
        role: body_lowerer
            .modules
            .type_decl_path(
                &body_lowerer
                    .modules
                    .type_decl_by_id(context.role)
                    .expect("role declaration"),
            )
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect(),
        inputs: context.input_signatures.clone(),
        associated: context.associated_signatures.clone(),
        signature: substitute_role_requirement_signature(stored, &context),
    });
    let expr = binding_body_expr(&binding).expect("method body expression");
    let mut lowerer = ExprLowerer::new(
        &mut body_lowerer.session,
        &body_lowerer.modules,
        implementation.body_module,
        method.order,
        method.def,
    );
    let lowered = lowerer
        .lower_impl_method_body_expr(
            &expr,
            &binding_arg_patterns(&binding),
            method_syntax.receiver,
            &context.target_ann,
            binding_type_expr(&binding),
            &context.type_var_bindings,
            &mut context.ann_solver_vars,
            Some(&requirement),
            false,
            prepare_inactive_receiver_requirement,
            false,
        )
        .expect("receiver method lowering");
    let parameter_context = lowered.receiver_parameter_context.clone();
    let descriptor = lowered
        .inactive_receiver_requirement
        .as_ref()
        .map(|deferred| ReceiverDescriptorWitness {
            anchor: deferred.anchor,
            anchors: deferred
                .receiver_anchors
                .clone()
                .expect("completed receiver anchors"),
            parameter_upper_count: deferred.parameter_uppers.len(),
            all_parameter_uppers_present: deferred.parameter_uppers.iter().all(Option::is_some),
            body_cursor: deferred.body_cursor,
            parameter_context: deferred.parameter_context.clone(),
            continuation_level: deferred.continuation.new_var_level,
            metadata_level: deferred.final_metadata.new_var_level,
            final_connect_value_upper: deferred.final_metadata.connect_value_upper,
        });
    let anchors = lowered.receiver_anchors.expect("receiver lowering anchors");
    assert_eq!(lowered.computation.value, anchors.method_value);
    let parameter_requirement_edges = anchors
        .tail_parameters
        .iter()
        .map(|parameter| upper_bound_count(&lowerer, *parameter))
        .sum();
    ReceiverMethodLoweringWitness {
        anchors: ReceiverMethodAnchorWitness {
            receiver: anchors.receiver,
            tail_parameters: anchors.tail_parameters,
            body_value: anchors.body_value,
            body_effect: anchors.body_effect,
            method_value: anchors.method_value,
            parameter_requirement_edges,
            body_value_requirement_edges: upper_bound_count(&lowerer, anchors.body_value),
            body_effect_requirement_edges: upper_bound_count(&lowerer, anchors.body_effect),
            method_value_requirement_edges: upper_bound_count(&lowerer, anchors.method_value),
        },
        descriptor,
        parameter_context,
    }
}

fn assert_receiver_requirement_connections(
    lowerer: &mut ExprLowerer<'_>,
    requirement: &ResolvedRoleMethodRequirement,
    bindings: &[(String, AnnTypeVarId)],
    vars: &mut rustc_hash::FxHashMap<AnnTypeVarId, TypeVar>,
    param_count: usize,
) {
    let plan = lowerer
        .impl_method_requirement_plan(&requirement.signature, param_count, true, bindings, vars)
        .expect("receiver requirement plan");
    assert_eq!(plan.param_uppers.len(), param_count);
    assert!(plan.param_uppers.iter().all(Option::is_some));
    assert!(plan.body.is_some());

    let mut param_connections = 0usize;
    for upper in plan.param_uppers.into_iter().flatten() {
        let actual = lowerer.fresh_type_var();
        let before = upper_bound_count(lowerer, actual);
        let lower = lowerer.alloc_pos(Pos::Var(actual));
        lowerer.session.infer.subtype(lower, upper);
        param_connections += upper_bound_count(lowerer, actual) - before;
    }
    assert_eq!(param_connections, param_count);

    let body_value = lowerer.fresh_type_var();
    let body_effect = lowerer.fresh_type_var();
    let value_before = upper_bound_count(lowerer, body_value);
    let effect_before = upper_bound_count(lowerer, body_effect);
    let body = Computation::value(
        lowerer.session.poly.add_expr(Expr::Tuple(Vec::new())),
        body_value,
        body_effect,
    );
    lowerer.connect_impl_method_body_requirement(body, plan.body.expect("body requirement"));
    assert_eq!(upper_bound_count(lowerer, body_value) - value_before, 1);
    assert_eq!(upper_bound_count(lowerer, body_effect) - effect_before, 1);

    let method_value = lowerer.fresh_type_var();
    let before = upper_bound_count(lowerer, method_value);
    lowerer
        .connect_impl_method_requirement(method_value, requirement, bindings, vars, false)
        .expect("receiver final requirement metadata");
    assert_eq!(upper_bound_count(lowerer, method_value) - before, 0);
}

fn upper_bound_count(lowerer: &ExprLowerer<'_>, var: TypeVar) -> usize {
    lowerer
        .session
        .infer
        .constraints()
        .bounds()
        .of(var)
        .map(|bounds| bounds.uppers().len())
        .unwrap_or(0)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BridgeState {
    bounds: Option<crate::constraints::VarBounds>,
    subtract_facts: Vec<crate::constraints::SubtractFact>,
}

fn bridge_state(lowerer: &ExprLowerer<'_>, var: TypeVar) -> BridgeState {
    let constraints = lowerer.session.infer.constraints();
    BridgeState {
        bounds: constraints.bounds().of(var).cloned(),
        subtract_facts: constraints.subtracts().facts(var).to_vec(),
    }
}

fn solver_var_named(
    bindings: &[(String, AnnTypeVarId)],
    vars: &rustc_hash::FxHashMap<AnnTypeVarId, TypeVar>,
    name: &str,
) -> TypeVar {
    let id = bindings
        .iter()
        .find_map(|(binding, id)| (binding == name).then_some(*id))
        .unwrap_or_else(|| panic!("missing annotation binding {name}"));
    vars.get(&id)
        .copied()
        .unwrap_or_else(|| panic!("missing solver bridge for {name}"))
}

fn neg_var(types: &poly::types::TypeArena, neg: NegId) -> TypeVar {
    match types.neg(neg) {
        Neg::Var(var) => *var,
        other => panic!("expected variable upper, got {other:?}"),
    }
}

fn stacked_neg_var(types: &poly::types::TypeArena, neg: NegId) -> TypeVar {
    match types.neg(neg) {
        Neg::Var(var) => *var,
        Neg::Stack { inner, .. } => stacked_neg_var(types, *inner),
        other => panic!("expected stacked variable upper, got {other:?}"),
    }
}

fn stacked_pos_var(types: &poly::types::TypeArena, pos: PosId) -> Option<TypeVar> {
    match types.pos(pos) {
        Pos::Var(var) => Some(*var),
        Pos::Stack { inner, .. } => stacked_pos_var(types, *inner),
        Pos::Row(items) => items.iter().find_map(|item| stacked_pos_var(types, *item)),
        _ => None,
    }
}

struct PauseResumeRequirementWitness {
    parameter_upper: NegId,
    body: ImplRequirementBodyConnection,
    resumed_fresh_upper: NegId,
    captured_level: crate::constraints::TypeLevel,
}

struct WitnessSignatureFunctionLayer<'a> {
    param: &'a SignatureType,
    ret_eff: Option<&'a SignatureEffectRow>,
    ret: &'a SignatureType,
}

fn pause_resume_requirement_parameter_and_body(
    expr_lowerer: &mut ExprLowerer<'_>,
    requirement: &ResolvedRoleMethodRequirement,
    bindings: &[(String, AnnTypeVarId)],
    vars: &rustc_hash::FxHashMap<AnnTypeVarId, TypeVar>,
) -> PauseResumeRequirementWitness {
    let receiver_layer = witness_signature_function_layer(&requirement.signature)
        .expect("receiver requirement layer");
    let parameter_layer =
        witness_signature_function_layer(receiver_layer.ret).expect("tail parameter layer");
    let seed = signature_vars_from_ann_vars(bindings, vars);
    let captured_level = expr_lowerer.session.infer.current_level();
    let mut lowerer = SignatureLowerer::with_vars_at_level(
        &mut expr_lowerer.session.infer,
        expr_lowerer.modules,
        seed,
        captured_level,
    );
    let parameter_upper = lowerer
        .lower_neg(parameter_layer.param)
        .expect("parameter layer before pause");
    let continuation = lowerer.into_continuation();
    assert_eq!(continuation.new_var_level, Some(captured_level));

    // Resume while the arena itself is at a different level. Fresh variables produced after the
    // pause must still use the level captured by the continuation.
    let previous_level = expr_lowerer.session.infer.enter_child_level();
    assert_eq!(previous_level, captured_level);
    assert_ne!(expr_lowerer.session.infer.current_level(), captured_level);
    let mut lowerer = SignatureLowerer::from_continuation(
        &mut expr_lowerer.session.infer,
        expr_lowerer.modules,
        continuation,
    );
    let (ret_eff, ret) =
        witness_signature_result_effect(parameter_layer.ret_eff, parameter_layer.ret);
    let body = ImplRequirementBodyConnection {
        effect_upper: lowerer
            .lower_ret_effect_neg(ret_eff)
            .expect("body effect layer after resume"),
        value_upper: lowerer
            .lower_neg(ret)
            .expect("body value layer after resume"),
    };
    let resumed_fresh_upper = lowerer
        .lower_neg(&SignatureType::Var(SignatureVar::new(
            "#slice1b-resumed-fresh",
        )))
        .expect("fresh method-local variable after resume");
    let _continuation = lowerer.into_continuation();
    expr_lowerer.session.infer.restore_level(previous_level);

    PauseResumeRequirementWitness {
        parameter_upper,
        body,
        resumed_fresh_upper,
        captured_level,
    }
}

fn witness_signature_function_layer(
    signature: &SignatureType,
) -> Option<WitnessSignatureFunctionLayer<'_>> {
    match signature {
        SignatureType::Effectful { ret, .. } => witness_signature_function_layer(ret),
        SignatureType::Function {
            param,
            ret_eff,
            ret,
            ..
        } => Some(WitnessSignatureFunctionLayer {
            param,
            ret_eff: ret_eff.as_ref(),
            ret,
        }),
        _ => None,
    }
}

fn witness_signature_result_effect<'a>(
    ret_eff: Option<&'a SignatureEffectRow>,
    ret: &'a SignatureType,
) -> (Option<&'a SignatureEffectRow>, &'a SignatureType) {
    match (ret_eff, ret) {
        (None, SignatureType::Effectful { eff, ret }) => (Some(eff), ret),
        _ => (ret_eff, ret),
    }
}

fn assert_signature_lowerer_reuses_private_data_effect_tail() {
    let root = parse(concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "my site = ()\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let tick = lower.modules.type_decls(module, &Name("tick".into()))[0].id;
    let mut infer = crate::Arena::new();
    let public_tail = infer.fresh_type_var();
    let row = SignatureEffectRow::new(
        vec![SignatureEffectAtom::Type(SignatureType::Named(tick))],
        Some(SignatureVar::new("e")),
    );
    let signature = SignatureType::EffectRow(row);
    let mut lowerer = SignatureLowerer::with_vars(
        &mut infer,
        &lower.modules,
        rustc_hash::FxHashMap::from_iter([("e".into(), public_tail)]),
    );
    let invariant = lowerer
        .lower_invariant_arg(&signature)
        .expect("data-position effect row");
    let types = lowerer.infer.constraints().types();
    let (lower, upper) = match types.neu(invariant) {
        Neu::Bounds(lower, upper) => (*lower, *upper),
        other => panic!("expected invariant effect bounds, got {other:?}"),
    };
    let private_from_lower = stacked_pos_var(types, lower).expect("private positive tail");
    let private_from_upper = match types.neg(upper) {
        Neg::Row(_, tail) => stacked_neg_var(types, *tail),
        other => panic!("expected negative effect row, got {other:?}"),
    };
    assert_eq!(private_from_lower, private_from_upper);
    assert_ne!(private_from_lower, public_tail);
    let public_bounds = lowerer
        .infer
        .constraints()
        .bounds()
        .of(public_tail)
        .expect("private tail flows to public tail");
    assert_eq!(public_bounds.lowers().len(), 1);
}

fn assert_signature_lowerer_pause_resume_reuses_private_data_effect_tail() {
    let root = parse(concat!(
        "act tick:\n",
        "  pub ping: () -> ()\n",
        "my site = ()\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let tick = lower.modules.type_decls(module, &Name("tick".into()))[0].id;
    let mut infer = crate::Arena::new();
    let public_tail = infer.fresh_type_var();
    let row = SignatureEffectRow::new(
        vec![SignatureEffectAtom::Type(SignatureType::Named(tick))],
        Some(SignatureVar::new("e")),
    );
    let signature = SignatureType::EffectRow(row);
    let SignatureType::EffectRow(signature_row) = &signature else {
        unreachable!("constructed effect-row signature")
    };
    let mut lowerer = SignatureLowerer::with_vars(
        &mut infer,
        &lower.modules,
        rustc_hash::FxHashMap::from_iter([("e".into(), public_tail)]),
    );
    let lower_pos = lowerer
        .lower_data_effect_row_pos(signature_row)
        .expect("data-position positive effect row before pause");
    let continuation = lowerer.into_continuation();
    let mut lowerer = SignatureLowerer::from_continuation(&mut infer, &lower.modules, continuation);
    let upper = lowerer
        .lower_data_effect_row_neg(signature_row)
        .expect("data-position negative effect row after resume");
    let _continuation = lowerer.into_continuation();

    let types = infer.constraints().types();
    let private_from_lower = stacked_pos_var(types, lower_pos).expect("private positive tail");
    let private_from_upper = match types.neg(upper) {
        Neg::Row(_, tail) => stacked_neg_var(types, *tail),
        other => panic!("expected negative effect row, got {other:?}"),
    };
    assert_eq!(private_from_lower, private_from_upper);
    assert_ne!(private_from_lower, public_tail);
    let public_bounds = infer
        .constraints()
        .bounds()
        .of(public_tail)
        .expect("private tail flows to public tail");
    assert_eq!(public_bounds.lowers().len(), 1);
}

fn lifecycle_fixtures() -> Vec<LifecycleFixture> {
    vec![
        LifecycleFixture {
            name: "receiverless",
            role: "Make",
            source: concat!(
                "impl Make int:\n",
                "  our make = 1\n",
                "role Make 'subject:\n",
                "  our make: int\n",
            ),
            ordinary_binding: None,
            expect_multi_member_component: false,
            observe_dependency_edge: true,
        },
        LifecycleFixture {
            name: "receiver-zero-tail",
            role: "Read",
            source: concat!(
                "impl int: Read:\n",
                "  our x.read = 1\n",
                "role Read 'subject:\n",
                "  our x.read: int\n",
            ),
            ordinary_binding: None,
            expect_multi_member_component: false,
            observe_dependency_edge: true,
        },
        LifecycleFixture {
            name: "receiver-multiple-tail",
            role: "Choose",
            source: concat!(
                "impl int: Choose:\n",
                "  our x.choose a b = a\n",
                "role Choose 'subject:\n",
                "  our x.choose: int -> int -> int\n",
            ),
            ordinary_binding: None,
            expect_multi_member_component: false,
            observe_dependency_edge: true,
        },
        LifecycleFixture {
            name: "mutual-with-ordinary-binding",
            role: "Eval",
            source: concat!(
                "role Eval 'subject:\n",
                "  our x.eval: int\n",
                "impl int: Eval:\n",
                "  our x.eval = helper\n",
                "  my helper = eval\n",
            ),
            ordinary_binding: Some("helper"),
            expect_multi_member_component: false,
            observe_dependency_edge: false,
        },
        LifecycleFixture {
            name: "two-role-impl-methods-one-component",
            role: "Pair",
            source: concat!(
                "role Pair 'subject:\n",
                "  our x.left: int\n",
                "  our x.right: int\n",
                "impl int: Pair:\n",
                "  our x.left = right\n",
                "  our x.right = left\n",
            ),
            ordinary_binding: None,
            expect_multi_member_component: true,
            observe_dependency_edge: false,
        },
    ]
}

const EXPLICIT_BOOL_CONCRETE_INT: &str = concat!(
    "lowering=accepted; check-diagnostics=0\n",
    "methods=box 'a -> int -> int\n",
    "infer-candidates=Index(box 'a <: box 'a, int <: int; value=bool <: bool) where [] methods=1 links=assoc/head:[value:0],prereq/head:0\n",
    "poly-candidates=Index(box 'a <: box 'a, int <: int; value=bool <: bool) where [] methods=1 links=assoc/head:[value:0],prereq/head:0",
);
const EXPLICIT_BOOL_UNIVERSAL_A: &str = concat!(
    "lowering=accepted; check-diagnostics=0\n",
    "methods=box('a & 'b) -> int -> 'a\n",
    "infer-candidates=Index(box 'a <: box 'a, int <: int; value=bool <: bool) where [] methods=1 links=assoc/head:[value:0],prereq/head:0\n",
    "poly-candidates=Index(box 'a <: box 'a, int <: int; value=bool <: bool) where [] methods=1 links=assoc/head:[value:0],prereq/head:0",
);
const EXPLICIT_OR_INFERRED_A: &str = concat!(
    "lowering=accepted; check-diagnostics=0\n",
    "methods=box('a & 'b) -> int -> 'a\n",
    "infer-candidates=Index(box 'a <: box 'a, int <: int; value='a <: 'a) where [] methods=1 links=assoc/head:[value:1],prereq/head:0\n",
    "poly-candidates=Index(box 'a <: box 'a, int <: int; value='a <: 'a) where [] methods=1 links=assoc/head:[value:1],prereq/head:0",
);
const OMITTED_ASSOCIATED_ONE_METHOD: &str = concat!(
    "lowering=accepted; check-diagnostics=0\n",
    "methods=box('a & 'b) -> int -> 'a\n",
    "infer-candidates=Index(box 'a <: box 'a, int <: int; value='a <: 'a) where [] methods=1 links=assoc/head:[value:0],prereq/head:0\n",
    "poly-candidates=Index(box 'a <: box 'a, int <: int; value='a <: 'a) where [] methods=1 links=assoc/head:[value:0],prereq/head:0",
);
const EXPLICIT_LIST_A: &str = concat!(
    "lowering=accepted; check-diagnostics=0\n",
    "methods=box 'a -> int -> list 'a\n",
    "infer-candidates=Index(box 'a <: box 'a, int <: int; value=list 'a <: list 'a) where [] methods=1 links=assoc/head:[value:1],prereq/head:0\n",
    "poly-candidates=Index(box 'a <: box 'a, int <: int; value=list 'a <: list 'a) where [] methods=1 links=assoc/head:[value:1],prereq/head:0",
);
const OMITTED_SHARED_TWO_METHODS: &str = concat!(
    "lowering=accepted; check-diagnostics=0\n",
    "methods=box('a & 'b) -> 'a | box('a & 'b) -> 'a\n",
    "infer-candidates=Access(box 'a <: box 'a; value='a <: 'a) where [] methods=2 links=assoc/head:[value:0],prereq/head:0\n",
    "poly-candidates=Access(box 'a <: box 'a; value='a <: 'a) where [] methods=2 links=assoc/head:[value:0],prereq/head:0",
);
const PARTIAL_EXPLICIT_MULTIPLE: &str = concat!(
    "lowering=accepted; check-diagnostics=0\n",
    "methods=pair 'a -> 'a | pair('a & 'b) -> 'a\n",
    "infer-candidates=PairView(pair 'a <: pair 'a; first='a <: 'a, second='a <: 'a) where [] methods=2 links=assoc/head:[first:1,second:0],prereq/head:0\n",
    "poly-candidates=PairView(pair 'a <: pair 'a; first='a <: 'a, second='a <: 'a) where [] methods=2 links=assoc/head:[first:1,second:0],prereq/head:0",
);
const RESIDUAL_PREREQUISITE_ABSENT_PRESENT: &str = concat!(
    "lowering=accepted; check-diagnostics=0\n",
    "methods=int -> () | 'a -> () where 'a: Eq\n",
    "infer-candidates=Box(int <: int; ) where [] methods=1 links=assoc/head:[],prereq/head:0 || Box('a <: 'a; ) where [Eq('a <: any)] methods=1 links=assoc/head:[],prereq/head:1\n",
    "poly-candidates=Box(int <: int; ) where [] methods=1 links=assoc/head:[],prereq/head:0 || Box('a <: 'a; ) where [Eq('a <: any)] methods=1 links=assoc/head:[],prereq/head:1",
);
const EFFECTFUL_SHARED_ROW: &str = concat!(
    "lowering=accepted; check-diagnostics=0\n",
    "methods=box 'a -> (() -> ['b] 'c & 'd) -> ['b] 'd\n",
    "infer-candidates=Flow(box 'a <: box 'a; value='a <: 'a) where [] methods=1 links=assoc/head:[value:1],prereq/head:0\n",
    "poly-candidates=Flow(box 'a <: box 'a; value='a <: 'a) where [] methods=1 links=assoc/head:[value:1],prereq/head:0",
);

#[derive(Debug, PartialEq, Eq)]
struct Slice4cT1BindingPublicationWitness {
    body_published: bool,
    root_has_body_var_lower: bool,
    fetch: BindingFetch,
    computed_runtime_root: bool,
    quantified: bool,
    scheme: String,
}

fn lower_inactive_receiver_provisional_for_slice4c_t2(
    evaluation: Evaluation,
    suppress_runtime_root: bool,
    commit: bool,
) -> (BodyLowering, DefId, usize, usize) {
    let source = concat!(
        "type box 'a\n",
        "role Read 'subject:\n",
        "  our x.read: 'subject\n",
        "impl (box 'a): Read:\n",
        "  our x.read = x\n",
    );
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let method = lower.modules.role_impls(module)[0].methods[0].def;
    let mut lowerer = super::super::body::BodyLowerer::new(lower);
    lowerer.set_inactive_receiver_provisional_test_mode(evaluation, suppress_runtime_root);
    lowerer.lower_block(&root, module);

    assert!(
        lowerer.inactive_receiver_provisional_descriptor_is_complete(method),
        "inactive receiver descriptor missing: finished={}, committed={}",
        lowerer.binding_def_finished_emission_count(method),
        lowerer.binding_publication_commit_count(method),
    );
    assert_eq!(lowerer.binding_def_finished_emission_count(method), 1);
    assert_eq!(lowerer.binding_publication_commit_count(method), 0);
    let method_root = lowerer
        .typing
        .def(method)
        .expect("provisional method must retain its registered root");
    assert!(!root_has_direct_var_lower(&lowerer.session, method_root));
    assert!(matches!(
        lowerer.session.poly.defs.get(method),
        Some(Def::Let {
            body: None,
            scheme: None,
            ..
        })
    ));
    assert_eq!(computed_runtime_root_count(&lowerer.session, method), 0);

    assert_eq!(
        lowerer.resolve_inactive_receiver_provisional_for_test(method, commit),
        commit
    );
    assert_eq!(lowerer.binding_def_finished_emission_count(method), 1);
    assert_eq!(
        lowerer.binding_publication_commit_count(method),
        usize::from(commit)
    );
    assert_eq!(
        root_has_direct_var_lower(&lowerer.session, method_root),
        commit
    );
    assert_eq!(
        computed_runtime_root_count(&lowerer.session, method),
        usize::from(commit && !suppress_runtime_root)
    );
    assert!(matches!(
        lowerer.session.poly.defs.get(method),
        Some(Def::Let { body, scheme: None, .. }) if body.is_some() == commit
    ));

    lowerer.drain_analysis_with_conformance();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    let def_finished_emissions = lowerer.binding_def_finished_emission_count(method);
    let publication_commits = lowerer.binding_publication_commit_count(method);
    let output = lowerer.finish();
    assert_eq!(
        output.session.scc.conformance_transition_counts(),
        crate::scc::ConformanceTransitionCounts::default(),
        "inactive T2 must not emit an SCC conformance blocker",
    );
    (output, method, def_finished_emissions, publication_commits)
}

fn root_has_direct_var_lower(session: &AnalysisSession, root: TypeVar) -> bool {
    session
        .infer
        .constraints()
        .bounds()
        .of(root)
        .is_some_and(|bounds| {
            bounds.lowers().iter().any(|bound| {
                matches!(
                    session.infer.constraints().types().pos(bound.pos),
                    Pos::Var(_)
                )
            })
        })
}

fn computed_runtime_root_count(session: &AnalysisSession, def: DefId) -> usize {
    session
        .poly
        .runtime_roots
        .iter()
        .filter(|root| matches!(root, poly::expr::RuntimeRoot::ComputedDef(root) if *root == def))
        .count()
}

fn slice4c_t1_binding_publication_witness(
    output: &BodyLowering,
    def: DefId,
) -> Slice4cT1BindingPublicationWitness {
    let Some(Def::Let { body, scheme, .. }) = output.session.poly.defs.get(def) else {
        panic!("expected let definition")
    };
    let root = output
        .typing
        .def(def)
        .expect("finished binding must retain its registered root");
    let root_has_body_var_lower = root_has_direct_var_lower(&output.session, root);
    let scheme = scheme
        .as_ref()
        .map(|scheme| poly::dump::format_scheme(&output.session.poly.typ, scheme))
        .unwrap_or_else(|| "<missing>".into());

    Slice4cT1BindingPublicationWitness {
        body_published: body.is_some(),
        root_has_body_var_lower,
        fetch: output.session.scc.fetch_of(def),
        computed_runtime_root: computed_runtime_root_count(&output.session, def) != 0,
        quantified: output.session.scc.is_quantified(def),
        scheme,
    }
}

fn characterize(source: &str, role: &str) -> String {
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let method_defs = lower
        .modules
        .role_impls(module)
        .iter()
        .flat_map(|implementation| implementation.methods.iter().map(|method| method.def))
        .collect::<Vec<_>>();
    let output = lower_binding_bodies(&root, lower);
    let role = vec![role.to_string()];

    let diagnostic = if output.errors.is_empty() {
        "accepted".to_string()
    } else {
        format!("rejected({})", output.errors.len())
    };
    let check_diagnostics = crate::check::summarize_lowering(&output).diagnostics.len();
    let method_schemes = method_defs
        .iter()
        .map(|def| {
            let scheme = match output.session.poly.defs.get(*def) {
                Some(Def::Let {
                    scheme: Some(scheme),
                    ..
                }) => scheme,
                _ => return "<missing>".to_string(),
            };
            poly::dump::format_scheme(&output.session.poly.typ, scheme)
        })
        .collect::<Vec<_>>()
        .join(" | ");
    let infer_candidates = output
        .session
        .role_impls
        .candidates(&role)
        .iter()
        .map(|candidate| format_candidate(&output.session.infer.constraints().types(), candidate))
        .collect::<Vec<_>>()
        .join(" || ");
    let poly_candidates = output
        .session
        .poly
        .role_impls
        .candidates(&role)
        .iter()
        .map(|candidate| format_candidate(&output.session.poly.typ, candidate))
        .collect::<Vec<_>>()
        .join(" || ");

    format!(
        "lowering={diagnostic}; check-diagnostics={check_diagnostics}\nmethods={method_schemes}\ninfer-candidates={infer_candidates}\npoly-candidates={poly_candidates}"
    )
}

fn lower_receiverless_conformance_shadow(source: &str, enabled: bool) -> BodyLowering {
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let mut lowerer = super::super::body::BodyLowerer::new(lower);
    lowerer.set_receiverless_conformance_shadow_enabled(enabled);
    lowerer.lower_block(&root, module);
    lowerer.drain_analysis_with_conformance();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    lowerer.finish()
}

fn lower_receiver_conformance_shadow(
    source: &str,
    enabled: bool,
    force_descriptor_gate_failure: bool,
    force_capture_failure: bool,
) -> (BodyLowering, DefId) {
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let method = lower.modules.role_impls(module)[0].methods[0].def;
    let mut lowerer = super::super::body::BodyLowerer::new(lower);
    lowerer.set_receiverless_conformance_shadow_enabled(enabled);
    if force_descriptor_gate_failure {
        lowerer.force_receiver_descriptor_gate_failure(method);
    }
    if force_capture_failure {
        lowerer.force_receiver_capture_failure(method);
    }
    lowerer.lower_block(&root, module);
    lowerer.drain_analysis_with_conformance();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    (lowerer.finish(), method)
}

fn receiver_shadow_production_surface(output: &BodyLowering, role: &str) -> String {
    let bodyless = output
        .session
        .poly
        .defs
        .iter()
        .filter(|(_, def)| matches!(def, Def::Let { body: None, .. }))
        .count();
    format!(
        "{}\nbodyless={bodyless}",
        receiverless_production_surface(output, role),
    )
}

fn receiverless_production_surface(output: &BodyLowering, role: &str) -> String {
    let role = vec![role.to_string()];
    let infer_candidates = output
        .session
        .role_impls
        .candidates(&role)
        .iter()
        .map(|candidate| format_candidate(&output.session.infer.constraints().types(), candidate))
        .collect::<Vec<_>>();
    let poly_candidates = output
        .session
        .poly
        .role_impls
        .candidates(&role)
        .iter()
        .map(|candidate| format_candidate(&output.session.poly.typ, candidate))
        .collect::<Vec<_>>();
    let diagnostics = crate::check::summarize_lowering(output);
    format!(
        "errors={:?}\ncheck={diagnostics:?}\ninfer={infer_candidates:?}\npoly={poly_candidates:?}\nruntime={} ",
        output.errors,
        poly::dump::dump_arena_with_labels(&output.session.poly, &output.labels),
    )
}

fn persisted_actual_surface(
    output: &BodyLowering,
    member: DefId,
) -> &crate::role_impl_conformance::RoleImplMethodActualSurface {
    &output
        .role_impl_conformance_contracts()
        .iter()
        .find_map(|contract| contract.actual_method_view(member))
        .unwrap_or_else(|| panic!("missing persisted actual view for {member:?}"))
        .surface
}

fn persisted_receiverless_actual_view(
    output: &BodyLowering,
    member: DefId,
) -> &crate::role_impl_conformance::ActualMethodConformanceView {
    let crate::role_impl_conformance::RoleImplMethodActualSurface::Receiverless(view) =
        persisted_actual_surface(output, member)
    else {
        panic!("expected receiverless persisted actual view for {member:?}")
    };
    view
}

fn persisted_receiver_actual_view(
    output: &BodyLowering,
    member: DefId,
) -> &crate::role_impl_conformance::ActualReceiverMethodConformanceView {
    let crate::role_impl_conformance::RoleImplMethodActualSurface::Receiver(view) =
        persisted_actual_surface(output, member)
    else {
        panic!("expected receiver persisted actual view for {member:?}")
    };
    view
}

fn characterize_contract(source: &str) -> String {
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let implementation = lower.modules.role_impls(module)[0].clone();
    let node = root
        .children()
        .find(|child| child.kind() == SyntaxKind::ImplDecl)
        .expect("root role impl declaration");
    let mut lowerer = super::super::body::BodyLowerer::new(lower);
    let context = lowerer
        .register_role_impl_candidate(
            &node,
            implementation.def,
            implementation.module,
            implementation.order,
            None,
        )
        .expect("role impl contract capture");
    context
        .conformance_contract
        .expect("source role impl contract")
        .binder_dump()
}

fn characterize_method_contract(source: &str) -> String {
    let root = parse(source);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let implementation = lower.modules.role_impls(module)[0].clone();
    let node = root
        .children()
        .find(|child| child.kind() == SyntaxKind::ImplDecl)
        .expect("root role impl declaration");
    let mut lowerer = super::super::body::BodyLowerer::new(lower);
    let context = lowerer
        .register_role_impl_candidate(
            &node,
            implementation.def,
            implementation.module,
            implementation.order,
            None,
        )
        .expect("role impl contract capture");
    context
        .conformance_contract
        .expect("source role impl contract")
        .method_correspondence_dump()
}

fn lowered_contract_dump(source: &str) -> String {
    let root = parse(source);
    let lower = lower_module_map(&root);
    let output = lower_binding_bodies(&root, lower);
    assert_eq!(
        output.errors,
        Vec::new(),
        "exit fixture should lower cleanly"
    );
    let contracts = output.role_impl_conformance_contracts();
    assert_eq!(contracts.len(), 1, "one source impl contract");
    format!(
        "{}\n{}",
        contracts[0].binder_dump(),
        contracts[0].method_correspondence_dump(),
    )
}

fn fixture_source(name: &str) -> &'static str {
    conformance_fixtures()
        .into_iter()
        .find(|fixture| fixture.name == name)
        .unwrap_or_else(|| panic!("missing fixture {name}"))
        .source
}

fn lower_conformance_fixture(source: &str) -> BodyLowering {
    let root = parse(source);
    let lower = lower_module_map(&root);
    let output = lower_binding_bodies(&root, lower);
    assert_eq!(output.errors, Vec::new(), "fixture should lower cleanly");
    output
}

fn shadow_conformance_pair_dump(source: &str) -> String {
    let output = lower_conformance_fixture(source);
    shadow_conformance_pair_dump_from_output(&output)
}

fn shadow_conformance_pair_dump_from_output(output: &BodyLowering) -> String {
    use crate::role_impl_conformance::RoleImplMethodActualSurface;
    use crate::role_impl_conformance::view::{ActualMethodConformanceView, DeclaredTypeView};

    output
        .role_impl_conformance_contracts()
        .iter()
        .enumerate()
        .flat_map(|(contract_index, contract)| {
            contract
                .shadow_conformance_pairs(&output.modules)
                .into_iter()
                .map(move |pair| {
                    assert!(contract.methods.iter().any(|method| {
                        method.requirement == pair.requirement && method.name == pair.method_name
                    }));
                    let implementation = if pair.implementation.is_some() {
                        "explicit"
                    } else {
                        "none"
                    };
                    let declared = match pair.declared {
                        Some(DeclaredTypeView::Available(_)) => "available",
                        Some(DeclaredTypeView::Unavailable(_)) => "unavailable",
                        Some(DeclaredTypeView::Ambiguous(_)) => "ambiguous",
                        None => "missing",
                    };
                    let actual = match pair.actual {
                        Some(RoleImplMethodActualSurface::Receiverless(
                            ActualMethodConformanceView::Available(_),
                        )) => "available",
                        Some(RoleImplMethodActualSurface::Receiverless(
                            ActualMethodConformanceView::Unavailable(_),
                        )) => "unavailable",
                        Some(RoleImplMethodActualSurface::Receiver(view))
                            if matches!(
                                (&view.value, &view.effect),
                                (
                                    ActualMethodConformanceView::Available(_),
                                    ActualMethodConformanceView::Available(_),
                                )
                            ) =>
                        {
                            "available"
                        }
                        Some(RoleImplMethodActualSurface::Receiver(_)) => "unavailable",
                        None => "missing",
                    };
                    format!(
                        "contract={contract_index} role={} method={} impl={implementation} declared={declared} actual={actual} outcome={:?}",
                        contract.role.join("::"),
                        pair.method_name,
                        pair.outcome,
                    )
                })
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn declared_contract_view(
    source: &str,
) -> crate::role_impl_conformance::view::DeclaredRoleImplView {
    let output = lower_conformance_fixture(source);
    output.role_impl_conformance_contracts()[0].declared_view(&output.modules)
}

fn first_contract_method_scheme<'a>(
    output: &'a BodyLowering,
    contract: &crate::role_impl_conformance::RoleImplConformanceContract,
) -> &'a Scheme {
    let implementation = match &contract.methods[0].provision {
        crate::role_impl_conformance::RoleImplMethodProvision::Explicit { implementations } => {
            &implementations[0]
        }
        provision => panic!("expected explicit method provision, got {provision:?}"),
    };
    let Some(Def::Let {
        scheme: Some(scheme),
        ..
    }) = output.session.poly.defs.get(implementation.def)
    else {
        panic!("impl method should have a finalized scheme");
    };
    scheme
}

fn finalized_contract_method_scheme(source: &str) -> String {
    let output = lower_conformance_fixture(source);
    let contract = &output.role_impl_conformance_contracts()[0];
    poly::dump::format_scheme(
        &output.session.poly.typ,
        first_contract_method_scheme(&output, contract),
    )
}

fn scheme_var_location(
    types: &poly::types::TypeArena,
    scheme: &Scheme,
    var: poly::types::TypeVar,
) -> &'static str {
    if scheme.quantifiers.contains(&var) {
        return "quantified";
    }
    if scheme.recursive_bounds.iter().any(|bound| bound.var == var) {
        return "recursive";
    }
    let violations = crate::interface_oracle::scan_scheme_closure(
        types,
        scheme,
        crate::interface_oracle::BoundaryInterface::EMPTY,
    )
    .err()
    .unwrap_or_default();
    if violations.iter().any(|violation| {
        matches!(
            violation,
            crate::interface_oracle::InterfaceViolation::UnboundSchemeVariable {
                var: unbound
            } if *unbound == var
        )
    }) {
        "free"
    } else {
        "absent"
    }
}

fn characterize_attached_contract(source: &str, owner: &str) -> String {
    let root = parse(source);
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let owner = lower.modules.type_decls(root_module, &Name(owner.into()))[0].clone();
    let companion = lower
        .modules
        .type_companion(owner.id)
        .expect("type companion module");
    let implementation = lower.modules.role_impls(companion)[0].clone();
    let node = root
        .descendants()
        .find(|child| child.kind() == SyntaxKind::ImplDecl)
        .expect("attached role impl declaration");
    let mut lowerer = super::super::body::BodyLowerer::new(lower);
    let context = lowerer
        .register_role_impl_candidate(
            &node,
            implementation.def,
            implementation.module,
            implementation.order,
            Some(AnnSelfAlias {
                owner: owner.id,
                type_vars: vec!["a".into()],
            }),
        )
        .expect("attached role impl contract capture");
    context
        .conformance_contract
        .expect("attached source role impl contract")
        .binder_dump()
}

fn format_candidate(
    types: &poly::types::TypeArena,
    candidate: &poly::roles::RoleImplCandidate,
) -> String {
    let head_vars = poly::roles::RoleConstraint {
        role: candidate.role.clone(),
        inputs: candidate.inputs.clone(),
        associated: Vec::new(),
    }
    .raw_vars(types);
    let prerequisite_vars = candidate
        .prerequisites
        .iter()
        .flat_map(|prerequisite| prerequisite.raw_vars(types))
        .collect::<rustc_hash::FxHashSet<_>>();
    let associated_head_links = candidate
        .associated
        .iter()
        .map(|associated| {
            let vars = poly::roles::RoleConstraint {
                role: candidate.role.clone(),
                inputs: Vec::new(),
                associated: vec![associated.clone()],
            }
            .raw_vars(types);
            format!(
                "{}:{}",
                associated.name,
                vars.intersection(&head_vars).count()
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let prerequisite_head_links = prerequisite_vars.intersection(&head_vars).count();
    let inputs = candidate
        .inputs
        .iter()
        .map(|arg| format_role_arg(types, arg))
        .collect::<Vec<_>>()
        .join(", ");
    let associated = candidate
        .associated
        .iter()
        .map(|associated| {
            format!(
                "{}={}",
                associated.name,
                format_role_arg(types, &associated.value)
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    let prerequisites = candidate
        .prerequisites
        .iter()
        .map(|prerequisite| {
            let inputs = prerequisite
                .inputs
                .iter()
                .map(|arg| format_role_arg(types, arg))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}({inputs})", prerequisite.role.join("::"))
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "{}({inputs}; {associated}) where [{prerequisites}] methods={} links=assoc/head:[{associated_head_links}],prereq/head:{prerequisite_head_links}",
        candidate.role.join("::"),
        candidate.methods.len(),
    )
}

fn format_role_arg(types: &poly::types::TypeArena, arg: &poly::roles::RoleConstraintArg) -> String {
    format!(
        "{} <: {}",
        poly::dump::format_pos(types, arg.lower),
        poly::dump::format_neg(types, arg.upper),
    )
}

fn conformance_fixtures() -> Vec<Fixture> {
    vec![
        Fixture {
            name: "explicit-bool-concrete-int",
            role: "Index",
            source: concat!(
                "type box 'a with:\n",
                "  struct self:\n",
                "    item: 'a\n",
                "role Index 'container 'key:\n",
                "  type value\n",
                "  our c.index: 'key -> value\n",
                "impl Index (box 'a) int:\n",
                "  type value = bool\n",
                "  our c.index i = 42\n",
            ),
            current: EXPLICIT_BOOL_CONCRETE_INT,
        },
        Fixture {
            name: "explicit-bool-universal-a",
            role: "Index",
            source: concat!(
                "type box 'a with:\n",
                "  struct self:\n",
                "    item: 'a\n",
                "role Index 'container 'key:\n",
                "  type value\n",
                "  our c.index: 'key -> value\n",
                "impl Index (box 'a) int:\n",
                "  type value = bool\n",
                "  our c.index i = c.item\n",
            ),
            current: EXPLICIT_BOOL_UNIVERSAL_A,
        },
        Fixture {
            name: "explicit-a-same-a",
            role: "Index",
            source: concat!(
                "type box 'a with:\n",
                "  struct self:\n",
                "    item: 'a\n",
                "role Index 'container 'key:\n",
                "  type value\n",
                "  our c.index: 'key -> value\n",
                "impl Index (box 'a) int:\n",
                "  type value = 'a\n",
                "  our c.index i = c.item\n",
            ),
            current: EXPLICIT_OR_INFERRED_A,
        },
        Fixture {
            name: "explicit-list-a-nested-binder",
            role: "Index",
            source: concat!(
                "type list 'a\n",
                "type box 'a with:\n",
                "  struct self:\n",
                "    item: list 'a\n",
                "role Index 'container 'key:\n",
                "  type value\n",
                "  our c.index: 'key -> value\n",
                "impl Index (box 'a) int:\n",
                "  type value = list 'a\n",
                "  our c.index i = c.item\n",
            ),
            current: EXPLICIT_LIST_A,
        },
        Fixture {
            name: "omitted-associated-one-method",
            role: "Index",
            source: concat!(
                "type box 'a with:\n",
                "  struct self:\n",
                "    item: 'a\n",
                "role Index 'container 'key:\n",
                "  type value\n",
                "  our c.index: 'key -> value\n",
                "impl Index (box 'a) int:\n",
                "  our c.index i = c.item\n",
            ),
            current: OMITTED_ASSOCIATED_ONE_METHOD,
        },
        Fixture {
            name: "omitted-associated-shared-two-methods",
            role: "Access",
            source: concat!(
                "type box 'a with:\n",
                "  struct self:\n",
                "    item: 'a\n",
                "role Access 'container:\n",
                "  type value\n",
                "  our c.get: value\n",
                "  our c.peek: value\n",
                "impl (box 'a): Access:\n",
                "  our c.get = c.item\n",
                "  our c.peek = c.item\n",
            ),
            current: OMITTED_SHARED_TWO_METHODS,
        },
        Fixture {
            name: "partial-explicit-multiple-associated",
            role: "PairView",
            source: concat!(
                "type pair 'a with:\n",
                "  struct self:\n",
                "    left: 'a\n",
                "    right: 'a\n",
                "role PairView 'container:\n",
                "  type first\n",
                "  type second\n",
                "  our c.first: first\n",
                "  our c.second: second\n",
                "impl (pair 'a): PairView:\n",
                "  type first = 'a\n",
                "  our c.first = c.left\n",
                "  our c.second = c.right\n",
            ),
            current: PARTIAL_EXPLICIT_MULTIPLE,
        },
        Fixture {
            name: "residual-prerequisite-absent-present",
            role: "Box",
            source: concat!(
                "role Eq 'a:\n",
                "  our x.eq: unit\n",
                "role Box 'a:\n",
                "  our x.get: unit\n",
                "impl int: Box:\n",
                "  our x.get = ()\n",
                "impl 'a: Box:\n",
                "  our x.get = x.eq\n",
            ),
            current: RESIDUAL_PREREQUISITE_ABSENT_PRESENT,
        },
        Fixture {
            name: "effectful-shared-row-binder",
            role: "Flow",
            source: concat!(
                "act tick:\n",
                "  pub ping: () -> ()\n",
                "type box 'a with:\n",
                "  struct self:\n",
                "    item: 'a\n",
                "role Flow 'container:\n",
                "  type value\n",
                "  our c.run: (unit -> ['e] value) -> ['e] value\n",
                "impl (box 'a): Flow:\n",
                "  type value = 'a\n",
                "  our c.run f = f()\n",
            ),
            current: EFFECTFUL_SHARED_ROW,
        },
        Fixture {
            name: "alpha-renamed-a",
            role: "Index",
            source: concat!(
                "type box 'a with:\n",
                "  struct self:\n",
                "    item: 'a\n",
                "role Index 'container 'key:\n",
                "  type value\n",
                "  our c.index: 'key -> value\n",
                "impl Index (box 'a) int:\n",
                "  type value = 'a\n",
                "  our c.index i = c.item\n",
            ),
            current: EXPLICIT_OR_INFERRED_A,
        },
        Fixture {
            name: "alpha-renamed-b",
            role: "Index",
            source: concat!(
                "type box 'b with:\n",
                "  struct self:\n",
                "    item: 'b\n",
                "role Index 'container 'key:\n",
                "  type value\n",
                "  our c.index: 'key -> value\n",
                "impl Index (box 'b) int:\n",
                "  type value = 'b\n",
                "  our c.index i = c.item\n",
            ),
            current: EXPLICIT_OR_INFERRED_A,
        },
        Fixture {
            name: "malformed-unused-impl",
            role: "Index",
            source: concat!(
                "type box 'a with:\n",
                "  struct self:\n",
                "    item: 'a\n",
                "role Index 'container 'key:\n",
                "  type value\n",
                "  our c.index: 'key -> value\n",
                "impl Index (box 'a) int:\n",
                "  type value = bool\n",
                "  our c.index i = c.item\n",
                "my unrelated = 1\n",
            ),
            current: EXPLICIT_BOOL_UNIVERSAL_A,
        },
    ]
}
