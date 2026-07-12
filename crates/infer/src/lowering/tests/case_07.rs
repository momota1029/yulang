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
