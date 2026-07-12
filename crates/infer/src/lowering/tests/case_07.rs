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
