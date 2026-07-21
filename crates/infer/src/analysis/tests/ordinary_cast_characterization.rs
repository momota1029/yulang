use rustc_hash::FxHashSet;

use super::*;
use crate::casts::{
    OrdinaryCastShadowOutcome, OrdinaryCastShadowSeam, begin_ordinary_cast_shadow_capture,
    finish_ordinary_cast_shadow_capture,
};
use crate::compact::CompactCon;
use poly::cast_resolution::{OrdinaryCastResolution, classify_ordinary_cast_candidates};

const SOURCE: &[&str] = &["source"];
const TARGET: &[&str] = &["target"];

#[test]
fn direct_nominal_cast_event_applies_zero_one_or_every_visible_candidate() {
    for candidate_count in 0..=2 {
        let mut session = prefix_seeded_session(candidate_count);
        let lower = session.infer.alloc_pos(Pos::Con(path(SOURCE), Vec::new()));
        let upper = session.infer.alloc_neg(Neg::Con(path(TARGET), Vec::new()));
        let before = session.infer.constraints().timing().weighted_subtype_calls;

        session.infer.subtype(lower, upper);
        assert!(matches!(
            session.infer.constraints().events(),
            [ConstraintEvent::NominalCastNeeded { source, target, .. }]
                if source == &path(SOURCE) && target == &path(TARGET)
        ));
        session.route_constraint_events();

        assert_eq!(
            session.infer.constraints().timing().weighted_subtype_calls - before,
            candidate_count
        );
        assert!(session.take_diagnostics().is_empty());

        // Future oracle by candidate_count: 0 = Missing (diagnose), 1 = Unique (instantiate one),
        // 2 = Ambiguous (diagnose before instantiating). Current direct-event behavior is instead
        // empty-success / instantiate-one / instantiate-all.
    }
}

#[test]
fn compact_cast_discovery_treats_one_and_two_candidates_as_the_same_present_pair() {
    let compact = compact_root_with_pair();
    for candidate_count in 0..=2 {
        let session = prefix_seeded_session(candidate_count);
        let batch = find_next_compact_cast(&compact, &session.casts, &FxHashSet::default());

        if candidate_count == 0 {
            assert!(batch.is_none());
        } else {
            let batch = batch.expect("any non-empty bucket is current compact ingress");
            assert_eq!(batch.key.source, path(SOURCE));
            assert_eq!(batch.key.target, path(TARGET));
            assert_eq!(batch.applications.len(), 1);
        }

        // Future oracle by candidate_count: 0 = Missing (skip discovery), 1 = Unique (return the
        // batch), 2 = Ambiguous (terminal non-success, without marking the pair applied).
    }
}

#[test]
fn direct_and_compact_shadow_observations_match_the_ocast_a_oracle() {
    for candidate_count in 0..=2 {
        let expected = expected_shadow_outcome(candidate_count);

        let mut session = prefix_seeded_session(candidate_count);
        let lower = session.infer.alloc_pos(Pos::Con(path(SOURCE), Vec::new()));
        let upper = session.infer.alloc_neg(Neg::Con(path(TARGET), Vec::new()));
        begin_ordinary_cast_shadow_capture();
        session.infer.subtype(lower, upper);
        session.route_constraint_events();
        let direct = finish_ordinary_cast_shadow_capture()
            .into_iter()
            .filter(|witness| {
                witness.seam == OrdinaryCastShadowSeam::NominalConstraint
                    && witness.source == path(SOURCE)
                    && witness.target == path(TARGET)
            })
            .collect::<Vec<_>>();

        assert_eq!(direct.len(), 1);
        assert_eq!(direct[0].outcome, expected);
        assert_eq!(
            direct[0].candidate_defs,
            (0..candidate_count)
                .map(|index| Some(DefId(index as u32)))
                .collect::<Vec<_>>()
        );

        let session = prefix_seeded_session(candidate_count);
        let compact = compact_root_with_pair();
        begin_ordinary_cast_shadow_capture();
        let _ = find_next_compact_cast(&compact, &session.casts, &FxHashSet::default());
        let compact = finish_ordinary_cast_shadow_capture()
            .into_iter()
            .filter(|witness| {
                witness.seam == OrdinaryCastShadowSeam::CompactDiscovery
                    && witness.source == path(SOURCE)
                    && witness.target == path(TARGET)
            })
            .collect::<Vec<_>>();

        assert_eq!(compact.len(), 1);
        assert_eq!(compact[0].outcome, expected);
        assert_eq!(
            compact[0].candidate_defs,
            (0..candidate_count)
                .map(|index| Some(DefId(index as u32)))
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn cached_prefix_seed_preserves_cast_table_and_poly_rule_cardinality() {
    for candidate_count in 0..=2 {
        let session = prefix_seeded_session(candidate_count);
        let infer_count = session.casts.candidates(&path(SOURCE), &path(TARGET)).len();
        let poly_count = session
            .poly
            .cast_rules
            .iter()
            .filter(|rule| {
                rule.kind == poly::expr::CastRuleKind::Value
                    && rule.source == path(SOURCE)
                    && rule.target == path(TARGET)
            })
            .count();

        assert_eq!(infer_count, candidate_count);
        assert_eq!(poly_count, candidate_count);

        // Future oracle by candidate_count: 0 = Missing, 1 = Unique, 2 = Ambiguous. Prefix seeding
        // currently copies every durable value rule into CastTable without changing cardinality.
    }
}

#[test]
fn prefix_seeded_infer_and_poly_classification_match_the_ocast_a_oracle() {
    for candidate_count in 0..=2 {
        let session = prefix_seeded_session(candidate_count);
        let infer_resolution = session.casts.resolve_value(&path(SOURCE), &path(TARGET));
        let poly_resolution =
            classify_ordinary_cast_candidates(session.poly.cast_rules.iter().filter(|rule| {
                rule.kind == poly::expr::CastRuleKind::Value
                    && rule.source == path(SOURCE)
                    && rule.target == path(TARGET)
            }));
        let expected = expected_shadow_outcome(candidate_count);

        assert_eq!(resolution_outcome(&infer_resolution), expected);
        assert_eq!(resolution_outcome(&poly_resolution), expected);
        assert_eq!(
            infer_resolution_defs(&infer_resolution),
            poly_resolution_defs(&poly_resolution)
        );
    }
}

#[test]
fn cached_prefix_seed_retains_defs_without_changing_schemes() {
    let session = prefix_seeded_session(2);
    let infer_rules = session.casts.candidates(&path(SOURCE), &path(TARGET));
    let poly_rules = session
        .poly
        .cast_rules
        .iter()
        .filter(|rule| {
            rule.kind == poly::expr::CastRuleKind::Value
                && rule.source == path(SOURCE)
                && rule.target == path(TARGET)
        })
        .collect::<Vec<_>>();

    assert_eq!(infer_rules.len(), poly_rules.len());
    for (infer_rule, poly_rule) in infer_rules.iter().zip(poly_rules) {
        assert_eq!(infer_rule.def, Some(poly_rule.def));
        assert_eq!(infer_rule.scheme.quantifiers, poly_rule.scheme.quantifiers);
        assert_eq!(
            infer_rule.scheme.role_predicates,
            poly_rule.scheme.role_predicates
        );
        assert_eq!(
            infer_rule.scheme.recursive_bounds,
            poly_rule.scheme.recursive_bounds
        );
        assert_eq!(
            infer_rule.scheme.stack_quantifiers,
            poly_rule.scheme.stack_quantifiers
        );
        assert_eq!(infer_rule.scheme.predicate, poly_rule.scheme.predicate);
    }
}

#[test]
fn repeated_identical_nominal_subtype_constraint_emits_only_one_current_cast_event() {
    for candidate_count in 0..=2 {
        let mut session = prefix_seeded_session(candidate_count);
        let lower = session.infer.alloc_pos(Pos::Con(path(SOURCE), Vec::new()));
        let upper = session.infer.alloc_neg(Neg::Con(path(TARGET), Vec::new()));
        let before = session.infer.constraints().timing().weighted_subtype_calls;

        session.infer.subtype(lower, upper);
        session.route_constraint_events();
        let after_first = session.infer.constraints().timing().weighted_subtype_calls;
        session.infer.subtype(lower, upper);
        assert!(session.infer.constraints().events().is_empty());
        session.route_constraint_events();
        let after_second = session.infer.constraints().timing().weighted_subtype_calls;

        assert_eq!(after_first - before, candidate_count);
        assert_eq!(after_second - after_first, 0);
        assert!(session.take_diagnostics().is_empty());

        // Future oracle for the first event is Missing/Unique/Ambiguous by candidate_count. The
        // exact repeated subtype never emits a second current event because the constraint machine
        // has already seen the same endpoint pair; diagnostic dedup beyond this case is deferred.
    }
}

#[test]
fn duplicated_imported_registry_entry_is_currently_counted_twice() {
    let mut poly = PolyArena::new();
    let scheme = monomorphic_cast_scheme(&mut poly.typ, path(SOURCE), path(TARGET));
    let rule = poly::expr::CastRule {
        def: DefId(7),
        source: path(SOURCE),
        target: path(TARGET),
        scheme,
        kind: poly::expr::CastRuleKind::Value,
    };
    poly.cast_rules.extend([rule.clone(), rule]);

    let session = AnalysisSession::new_with_imported_boundary(
        poly,
        &crate::CompiledBoundaryInterface::empty(),
    );

    assert_eq!(
        session.casts.candidates(&path(SOURCE), &path(TARGET)).len(),
        2
    );
    assert_eq!(session.poly.cast_rules.len(), 2);
    assert_eq!(
        session.poly.cast_rules[0].def,
        session.poly.cast_rules[1].def
    );

    // Future raw-cardinality oracle: Ambiguous. Because both entries carry the same DefId, the
    // activation slices must either prove this representation impossible or deduplicate it as
    // registry hygiene before treating it as two source declarations.
}

#[test]
fn disjoint_looking_same_pair_schemes_are_both_applied_today() {
    let mut poly = PolyArena::new();
    for argument in ["int", "bool"] {
        let scheme = concrete_unary_cast_scheme(
            &mut poly.typ,
            path(SOURCE),
            path(TARGET),
            vec![argument.to_string()],
        );
        poly.cast_rules.push(poly::expr::CastRule {
            def: DefId(poly.cast_rules.len() as u32),
            source: path(SOURCE),
            target: path(TARGET),
            scheme,
            kind: poly::expr::CastRuleKind::Value,
        });
    }
    let mut session = AnalysisSession::new(poly);
    let argument = infer_con_neu(&mut session.infer, &["int"]);
    let lower = session
        .infer
        .alloc_pos(Pos::Con(path(SOURCE), vec![argument]));
    let argument = infer_con_neu(&mut session.infer, &["int"]);
    let upper = session
        .infer
        .alloc_neg(Neg::Con(path(TARGET), vec![argument]));
    let before = session.infer.constraints().timing().weighted_subtype_calls;

    session.infer.subtype(lower, upper);
    while !session.infer.constraints().events().is_empty() {
        session.route_constraint_events();
    }

    assert_eq!(
        session.infer.constraints().timing().weighted_subtype_calls - before,
        2
    );
    assert!(session.take_diagnostics().is_empty());

    // Future oracle: Ambiguous before applicability. The int-argument and bool-argument schemes
    // look disjoint, but Section 5 deliberately classifies their shared constructor pair only.
}

#[test]
fn infer_adapter_preserves_raw_cardinality_for_ocast_a_ambiguous_edge_fixtures() {
    let mut duplicate_poly = PolyArena::new();
    let scheme = monomorphic_cast_scheme(&mut duplicate_poly.typ, path(SOURCE), path(TARGET));
    let rule = poly::expr::CastRule {
        def: DefId(7),
        source: path(SOURCE),
        target: path(TARGET),
        scheme,
        kind: poly::expr::CastRuleKind::Value,
    };
    duplicate_poly.cast_rules.extend([rule.clone(), rule]);
    let duplicate_session = AnalysisSession::new(duplicate_poly);
    let duplicate_resolution = duplicate_session
        .casts
        .resolve_value(&path(SOURCE), &path(TARGET));

    assert_eq!(
        resolution_outcome(&duplicate_resolution),
        OrdinaryCastShadowOutcome::Ambiguous
    );
    assert_eq!(
        infer_resolution_defs(&duplicate_resolution),
        vec![DefId(7), DefId(7)]
    );

    let mut disjoint_poly = PolyArena::new();
    for argument in ["int", "bool"] {
        let scheme = concrete_unary_cast_scheme(
            &mut disjoint_poly.typ,
            path(SOURCE),
            path(TARGET),
            vec![argument.to_string()],
        );
        disjoint_poly.cast_rules.push(poly::expr::CastRule {
            def: DefId(disjoint_poly.cast_rules.len() as u32),
            source: path(SOURCE),
            target: path(TARGET),
            scheme,
            kind: poly::expr::CastRuleKind::Value,
        });
    }
    let disjoint_session = AnalysisSession::new(disjoint_poly);
    let disjoint_resolution = disjoint_session
        .casts
        .resolve_value(&path(SOURCE), &path(TARGET));

    assert_eq!(
        resolution_outcome(&disjoint_resolution),
        OrdinaryCastShadowOutcome::Ambiguous
    );
    assert_eq!(
        infer_resolution_defs(&disjoint_resolution),
        vec![DefId(0), DefId(1)]
    );
}

fn prefix_seeded_session(candidate_count: usize) -> AnalysisSession {
    let mut poly = PolyArena::new();
    for index in 0..candidate_count {
        let scheme = monomorphic_cast_scheme(&mut poly.typ, path(SOURCE), path(TARGET));
        poly.cast_rules.push(poly::expr::CastRule {
            def: DefId(index as u32),
            source: path(SOURCE),
            target: path(TARGET),
            scheme,
            kind: poly::expr::CastRuleKind::Value,
        });
    }
    AnalysisSession::new_with_imported_boundary(poly, &crate::CompiledBoundaryInterface::empty())
}

fn expected_shadow_outcome(candidate_count: usize) -> OrdinaryCastShadowOutcome {
    match candidate_count {
        0 => OrdinaryCastShadowOutcome::Missing,
        1 => OrdinaryCastShadowOutcome::Unique,
        _ => OrdinaryCastShadowOutcome::Ambiguous,
    }
}

fn resolution_outcome<R>(resolution: &OrdinaryCastResolution<R>) -> OrdinaryCastShadowOutcome {
    match resolution {
        OrdinaryCastResolution::Missing => OrdinaryCastShadowOutcome::Missing,
        OrdinaryCastResolution::Unique(_) => OrdinaryCastShadowOutcome::Unique,
        OrdinaryCastResolution::Ambiguous(_) => OrdinaryCastShadowOutcome::Ambiguous,
    }
}

fn infer_resolution_defs(
    resolution: &OrdinaryCastResolution<crate::casts::CastRule>,
) -> Vec<DefId> {
    match resolution {
        OrdinaryCastResolution::Missing => Vec::new(),
        OrdinaryCastResolution::Unique(rule) => rule.def.iter().copied().collect(),
        OrdinaryCastResolution::Ambiguous(rules) => {
            rules.iter().filter_map(|rule| rule.def).collect()
        }
    }
}

fn poly_resolution_defs(resolution: &OrdinaryCastResolution<&poly::expr::CastRule>) -> Vec<DefId> {
    match resolution {
        OrdinaryCastResolution::Missing => Vec::new(),
        OrdinaryCastResolution::Unique(rule) => vec![rule.def],
        OrdinaryCastResolution::Ambiguous(rules) => rules.iter().map(|rule| rule.def).collect(),
    }
}

fn compact_root_with_pair() -> CompactRoot {
    let mut root = CompactType::from_con(CompactCon {
        path: path(SOURCE),
        args: Vec::new(),
    });
    root.cons.insert(path(TARGET), Vec::new());
    CompactRoot {
        root,
        rec_vars: Vec::new(),
    }
}

fn concrete_unary_cast_scheme(
    types: &mut poly::types::TypeArena,
    source: Vec<String>,
    target: Vec<String>,
    argument: Vec<String>,
) -> Scheme {
    let source_arg = poly_con_neu(types, &argument);
    let target_arg = poly_con_neu(types, &argument);
    let arg = types.alloc_neg(Neg::Con(source, vec![source_arg]));
    let arg_eff = types.alloc_neg(Neg::Bot);
    let ret_eff = types.alloc_pos(Pos::Bot);
    let ret = types.alloc_pos(Pos::Con(target, vec![target_arg]));
    let predicate = types.alloc_pos(Pos::Fun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    });
    Scheme {
        quantifiers: Vec::new(),
        role_predicates: Vec::new(),
        recursive_bounds: Vec::new(),
        stack_quantifiers: Vec::new(),
        predicate,
    }
}

fn poly_con_neu(types: &mut poly::types::TypeArena, path: &[String]) -> NeuId {
    let lower = types.alloc_pos(Pos::Con(path.to_vec(), Vec::new()));
    let upper = types.alloc_neg(Neg::Con(path.to_vec(), Vec::new()));
    types.alloc_neu(Neu::Bounds(lower, upper))
}

fn infer_con_neu(infer: &mut crate::arena::Arena, segments: &[&str]) -> NeuId {
    let path = path(segments);
    let lower = infer.alloc_pos(Pos::Con(path.clone(), Vec::new()));
    let upper = infer.alloc_neg(Neg::Con(path, Vec::new()));
    infer.alloc_neu(Neu::Bounds(lower, upper))
}

fn path(segments: &[&str]) -> Vec<String> {
    segments
        .iter()
        .map(|segment| (*segment).to_string())
        .collect()
}
