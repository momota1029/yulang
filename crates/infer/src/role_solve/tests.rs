use super::*;

use crate::arena::Arena;
use crate::roles::RoleConstraintArg;
use poly::types::{Neg, NegId, Pos, PosId};

#[test]
fn role_input_rejects_variable_only_aliases_and_top() {
    let mut infer = Arena::new();
    let positive_var = infer.fresh_type_var();
    let negative_var = infer.fresh_type_var();
    let positive_alias = infer.alloc_pos(Pos::Var(positive_var));
    let negative_alias = infer.alloc_neg(Neg::Var(negative_var));
    let bottom = infer.alloc_pos(Pos::Bot);
    let top = infer.alloc_neg(Neg::Top);

    let inputs = [
        compact_role_input(&infer, positive_alias, top),
        compact_role_input(&infer, bottom, negative_alias),
        compact_role_input(&infer, bottom, top),
    ];

    assert!(
        inputs
            .iter()
            .all(|input| !role_input_has_concrete_component(input))
    );
}

#[test]
fn role_input_accepts_each_concrete_component_shape() {
    let mut infer = Arena::new();
    let bottom = infer.alloc_pos(Pos::Bot);
    let top = infer.alloc_neg(Neg::Top);
    let never = infer.alloc_neg(Neg::Bot);
    let builtin = infer.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let positive_con = infer.alloc_pos(Pos::Con(vec!["PositiveNominal".into()], Vec::new()));
    let negative_con = infer.alloc_neg(Neg::Con(vec!["NegativeNominal".into()], Vec::new()));
    let function = infer.alloc_pos(Pos::Fun {
        arg: top,
        arg_eff: top,
        ret_eff: bottom,
        ret: bottom,
    });
    let record = infer.alloc_pos(Pos::Record(Vec::new()));
    let record_spread = infer.alloc_pos(Pos::RecordTailSpread {
        fields: Vec::new(),
        tail: bottom,
    });
    let poly_variant = infer.alloc_pos(Pos::PolyVariant(Vec::new()));
    let tuple = infer.alloc_pos(Pos::Tuple(Vec::new()));
    let row_item = infer.alloc_pos(Pos::Con(vec!["effect".into()], Vec::new()));
    let row = infer.alloc_pos(Pos::Row(vec![row_item]));

    let inputs = [
        ("Never/bottom", compact_role_input(&infer, bottom, never)),
        ("builtin", compact_role_input(&infer, builtin, top)),
        ("Pos::Con", compact_role_input(&infer, positive_con, top)),
        ("Neg::Con", compact_role_input(&infer, bottom, negative_con)),
        ("function", compact_role_input(&infer, function, top)),
        ("record", compact_role_input(&infer, record, top)),
        (
            "record spread",
            compact_role_input(&infer, record_spread, top),
        ),
        (
            "polymorphic variant",
            compact_role_input(&infer, poly_variant, top),
        ),
        ("tuple", compact_role_input(&infer, tuple, top)),
        ("row", compact_role_input(&infer, row, top)),
    ];

    for (shape, input) in inputs {
        assert!(
            role_input_has_concrete_component(&input),
            "{shape} should be a concrete role input component"
        );
    }
}

#[test]
fn role_constraint_could_resolve_requires_concrete_information_for_every_input() {
    let mut infer = Arena::new();
    let first_var = infer.fresh_type_var();
    let second_var = infer.fresh_type_var();
    let first_alias = infer.alloc_pos(Pos::Var(first_var));
    let second_alias = infer.alloc_neg(Neg::Var(second_var));
    let bottom = infer.alloc_pos(Pos::Bot);
    let top = infer.alloc_neg(Neg::Top);
    let builtin = infer.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let nominal = infer.alloc_neg(Neg::Con(vec!["Concrete".into()], Vec::new()));

    let all_variable = role_constraint(vec![
        compact_role_input(&infer, first_alias, top),
        compact_role_input(&infer, bottom, second_alias),
    ]);
    let concrete = role_constraint(vec![
        compact_role_input(&infer, builtin, top),
        compact_role_input(&infer, bottom, nominal),
    ]);

    assert!(!role_constraint_could_resolve(&all_variable));
    assert!(role_constraint_could_resolve(&concrete));
}

#[test]
fn candidate_precheck_rejects_definite_non_first_head_mismatch_before_deep_match() {
    let mut infer = Arena::new();
    let node_var = infer.fresh_type_var();
    let candidate = vec![
        nominal_role_arg(
            "doc_leaf",
            vec![nominal_bounds(
                "cons_cell",
                vec![
                    identity_bounds(node_var),
                    nominal_bounds("nil_cell", Vec::new()),
                ],
            )],
        ),
        nominal_role_arg("html_format", Vec::new()),
    ];
    let demand = vec![
        nominal_bounds(
            "doc_leaf",
            vec![nominal_bounds(
                "cons_cell",
                vec![
                    nominal_bounds("text_leaf", Vec::new()),
                    nominal_bounds("nil_cell", Vec::new()),
                ],
            )],
        ),
        nominal_bounds("markdown_format", Vec::new()),
    ];

    assert!(role_candidate_has_definite_input_head_mismatch(
        &candidate, &demand
    ));
    let mut subst = TypeSubst::default();
    assert!(!match_role_candidate_inputs(
        &candidate, &demand, &mut subst
    ));
    assert_eq!(subst.get(node_var), None);
}

#[test]
fn candidate_precheck_defers_ambiguous_input_to_full_match() {
    let mut infer = Arena::new();
    let format_var = infer.fresh_type_var();
    let candidate = vec![
        nominal_role_arg("text_leaf", Vec::new()),
        identity_role_arg(format_var),
    ];
    let demand = vec![
        nominal_bounds("text_leaf", Vec::new()),
        nominal_bounds("markdown_format", Vec::new()),
    ];

    assert!(!role_candidate_has_definite_input_head_mismatch(
        &candidate, &demand
    ));
    let mut subst = TypeSubst::default();
    assert!(match_role_candidate_inputs(&candidate, &demand, &mut subst));
    assert_eq!(
        subst.get(format_var),
        compact_type_from_bounds(&demand[1]).as_ref()
    );
}

#[test]
fn candidate_precheck_preserves_positive_nominal_match() {
    let nested_node = nominal_bounds(
        "doc_leaf",
        vec![nominal_bounds(
            "cons_cell",
            vec![
                nominal_bounds("text_leaf", Vec::new()),
                nominal_bounds("nil_cell", Vec::new()),
            ],
        )],
    );
    let markdown = nominal_bounds("markdown_format", Vec::new());
    let candidate = vec![
        CompactRoleArg::invariant(nested_node.clone()),
        CompactRoleArg::invariant(markdown.clone()),
    ];
    let demand = vec![nested_node, markdown];

    assert!(!role_candidate_has_definite_input_head_mismatch(
        &candidate, &demand
    ));
    assert!(match_role_candidate_inputs(
        &candidate,
        &demand,
        &mut TypeSubst::default()
    ));
}

#[test]
fn raw_candidate_precheck_rejects_definite_head_mismatch_before_compaction() {
    let mut machine = ConstraintMachine::new();
    let candidate = raw_role_candidate(vec![raw_nominal_role_arg(&mut machine, "html_format")]);
    let demand = vec![nominal_bounds("markdown_format", Vec::new())];

    assert!(raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &demand,
    ));
    let (matched, stats, cached_candidates) =
        resolve_raw_candidate_for_test(&machine, &candidate, &demand);

    assert!(!matched);
    assert_eq!(stats.candidate_cache_misses, 0);
    assert_eq!(stats.candidate_cache_hits, 0);
    assert_eq!(cached_candidates, 0);
}

#[test]
fn raw_candidate_precheck_compares_canonical_builtin_heads() {
    let mut machine = ConstraintMachine::new();
    let candidate = raw_role_candidate(vec![raw_nominal_role_arg(&mut machine, "int")]);

    assert!(!raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &[nominal_bounds("int", Vec::new())],
    ));
    assert!(raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &[nominal_bounds("float", Vec::new())],
    ));
}

#[test]
fn raw_candidate_precheck_defers_variable_input_to_compaction_and_matching() {
    let mut machine = ConstraintMachine::new();
    let var = TypeVar(0);
    machine.register_type_var(var, TypeLevel::root());
    let candidate = raw_role_candidate(vec![RoleConstraintArg {
        lower: machine.alloc_pos(Pos::Var(var)),
        upper: machine.alloc_neg(Neg::Var(var)),
    }]);
    let demand = vec![nominal_bounds("markdown_format", Vec::new())];

    assert!(!raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &demand,
    ));
    let (matched, stats, cached_candidates) =
        resolve_raw_candidate_for_test(&machine, &candidate, &demand);

    assert!(matched);
    assert_eq!(stats.candidate_cache_misses, 1);
    assert_eq!(cached_candidates, 1);
}

#[test]
fn raw_candidate_precheck_preserves_positive_nominal_match() {
    let mut machine = ConstraintMachine::new();
    let candidate = raw_role_candidate(vec![raw_nominal_role_arg(&mut machine, "markdown_format")]);
    let demand = vec![nominal_bounds("markdown_format", Vec::new())];

    assert!(!raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &demand,
    ));
    let (matched, stats, cached_candidates) =
        resolve_raw_candidate_for_test(&machine, &candidate, &demand);

    assert!(matched);
    assert_eq!(stats.candidate_cache_misses, 1);
    assert_eq!(cached_candidates, 1);
}

#[test]
fn raw_and_compacted_candidate_head_prechecks_compose() {
    let mut machine = ConstraintMachine::new();
    let var = TypeVar(0);
    machine.register_type_var(var, TypeLevel::root());
    let html_lower = machine.alloc_pos(Pos::Con(vec!["html_format".into()], Vec::new()));
    let html_upper = machine.alloc_neg(Neg::Con(vec!["html_format".into()], Vec::new()));
    let raw_lower = machine.alloc_pos(Pos::Var(var));
    let raw_upper = machine.alloc_neg(Neg::Var(var));
    machine.constrain_subtype(html_lower, raw_upper);
    machine.constrain_subtype(raw_lower, html_upper);
    let candidate = raw_role_candidate(vec![RoleConstraintArg {
        lower: raw_lower,
        upper: raw_upper,
    }]);
    let demand = vec![nominal_bounds("markdown_format", Vec::new())];

    assert!(!raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &demand,
    ));
    let mut cache = CompactRoleImplCandidateCache::default();
    let mut compact_stats = RoleResolveStats::default();
    let compact = cache.compact(&machine, &candidate, &mut compact_stats);
    assert!(role_candidate_has_definite_input_head_mismatch(
        &compact.inputs,
        &demand,
    ));

    let (matched, stats, cached_candidates) =
        resolve_raw_candidate_for_test(&machine, &candidate, &demand);
    assert!(!matched);
    assert_eq!(stats.candidate_cache_misses, 1);
    assert_eq!(cached_candidates, 1);
}

fn compact_role_input(infer: &Arena, lower: PosId, upper: NegId) -> CompactRoleArg {
    compact_role_constraint(
        infer.constraints(),
        &RoleConstraint {
            role: vec!["TestRole".into()],
            inputs: vec![RoleConstraintArg { lower, upper }],
            associated: Vec::new(),
        },
    )
    .inputs
    .into_iter()
    .next()
    .expect("test role should contain one input")
}

fn role_constraint(inputs: Vec<CompactRoleArg>) -> CompactRoleConstraint {
    CompactRoleConstraint {
        role: vec!["TestRole".into()],
        inputs,
        associated: Vec::new(),
    }
}

fn raw_role_candidate(inputs: Vec<RoleConstraintArg>) -> RoleImplCandidate {
    RoleImplCandidate {
        impl_def: None,
        role: vec!["TestRole".into()],
        inputs,
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    }
}

fn raw_nominal_role_arg(machine: &mut ConstraintMachine, name: &str) -> RoleConstraintArg {
    let path = vec![name.into()];
    RoleConstraintArg {
        lower: machine.alloc_pos(Pos::Con(path.clone(), Vec::new())),
        upper: machine.alloc_neg(Neg::Con(path, Vec::new())),
    }
}

fn resolve_raw_candidate_for_test(
    machine: &ConstraintMachine,
    candidate: &RoleImplCandidate,
    demand: &[CompactBounds],
) -> (bool, RoleResolveStats, usize) {
    let constraint = role_constraint(
        demand
            .iter()
            .cloned()
            .map(CompactRoleArg::invariant)
            .collect(),
    );
    let mut cache = CompactRoleImplCandidateCache::default();
    let mut stats = RoleResolveStats::default();
    let matched = resolve_role_candidate(
        machine,
        &constraint,
        Some(demand),
        candidate,
        &MainPolarity::default(),
        &FxHashMap::default(),
        &RoleImplTable::new(),
        &mut cache,
        &mut FxHashSet::default(),
        &mut stats,
    )
    .is_some();
    (matched, stats, cache.entries.len())
}

fn identity_role_arg(var: TypeVar) -> CompactRoleArg {
    CompactRoleArg::invariant(identity_bounds(var))
}

fn identity_bounds(var: TypeVar) -> CompactBounds {
    let ty = CompactType::from_var(crate::compact::CompactVar::plain(var));
    CompactBounds::Interval {
        lower: ty.clone(),
        upper: ty,
    }
}

fn nominal_role_arg(name: &str, args: Vec<CompactBounds>) -> CompactRoleArg {
    CompactRoleArg::invariant(nominal_bounds(name, args))
}

fn nominal_bounds(name: &str, args: Vec<CompactBounds>) -> CompactBounds {
    CompactBounds::Con {
        path: vec![name.into()],
        args,
    }
}
