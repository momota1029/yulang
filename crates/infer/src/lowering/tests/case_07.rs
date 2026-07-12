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
