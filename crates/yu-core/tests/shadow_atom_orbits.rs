#![cfg(feature = "shadow")]

use yu_core::shadow_atom_orbits::Formula;
use yu_core::shadow_atom_orbits::{AtomRef::*, Error, Formula::*, MAX_PUBLIC, Resource, evaluate};

fn exists(binder: u64, body: Formula) -> Formula {
    Exists {
        binder,
        body: Box::new(body),
    }
}
fn forall(binder: u64, body: Formula) -> Formula {
    ForAll {
        binder,
        body: Box::new(body),
    }
}
fn and(a: Formula, b: Formula) -> Formula {
    And(Box::new(a), Box::new(b))
}
fn or(a: Formula, b: Formula) -> Formula {
    Or(Box::new(a), Box::new(b))
}

#[test]
fn original_alternation_is_preserved() {
    let equality = Eq(Variable(7), Variable(9));
    assert_eq!(
        evaluate(&exists(7, forall(9, equality.clone())), &[], 100),
        Ok(false)
    );
    assert_eq!(
        evaluate(&forall(9, exists(7, equality)), &[], 100),
        Ok(true)
    );
}

#[test]
fn one_shared_witness_retains_correlation_and_repeated_occurrences() {
    let shared = exists(
        7,
        and(Eq(Public(0), Variable(7)), Eq(Public(1), Variable(7))),
    );
    assert_eq!(evaluate(&shared, &[41, 41], 100), Ok(true));
    assert_eq!(evaluate(&shared, &[41, 42], 100), Ok(false));
    assert_eq!(
        evaluate(&exists(7, Ne(Variable(7), Variable(7))), &[], 100),
        Ok(false)
    );
}

#[test]
fn fresh_atom_exists_outside_every_supplied_constant() {
    let mut body = Bool(true);
    for index in 0..MAX_PUBLIC {
        body = and(body, Ne(Variable(1), Public(index)));
    }
    let labels: Vec<_> = (0..MAX_PUBLIC as u64).collect();
    assert_eq!(evaluate(&exists(1, body), &labels, 10_000), Ok(true));
}

#[test]
fn nested_variables_keep_their_lexical_values() {
    let body = exists(
        1,
        forall(
            2,
            or(Eq(Variable(1), Variable(2)), Ne(Variable(1), Variable(2))),
        ),
    );
    assert_eq!(evaluate(&body, &[], 100), Ok(true));
}

#[test]
fn invalid_scope_and_duplicate_binders_are_rejected_everywhere() {
    assert_eq!(
        evaluate(&Eq(Variable(1), Variable(1)), &[], 100),
        Err(Error::OutOfScopeVariable(1))
    );
    let escaped = and(exists(1, Bool(true)), Eq(Variable(1), Variable(1)));
    assert_eq!(
        evaluate(&escaped, &[], 100),
        Err(Error::OutOfScopeVariable(1))
    );
    let nested_duplicate = exists(1, forall(1, Bool(true)));
    assert_eq!(
        evaluate(&nested_duplicate, &[], 100),
        Err(Error::RepeatedBinder(1))
    );
    let siblings = or(exists(1, Bool(true)), exists(1, Bool(false)));
    assert_eq!(evaluate(&siblings, &[], 100), Err(Error::RepeatedBinder(1)));
    let hidden_invalid = or(Bool(true), Eq(Public(0), Public(0)));
    assert_eq!(
        evaluate(&hidden_invalid, &[], 100),
        Err(Error::InvalidPublicReference(0))
    );
    let sibling_reference = and(
        exists(1, Bool(true)),
        exists(2, Eq(Variable(1), Variable(2))),
    );
    assert_eq!(
        evaluate(&sibling_reference, &[], 100),
        Err(Error::OutOfScopeVariable(1))
    );
}

#[test]
fn public_and_binder_alpha_renaming_preserves_truth() {
    for (labels, renamed) in [([4, 4], [u64::MAX, u64::MAX]), ([4, 5], [u64::MAX, 0])] {
        let original = exists(
            1,
            and(Eq(Public(0), Variable(1)), Eq(Public(1), Variable(1))),
        );
        let changed = exists(
            901,
            and(Eq(Public(0), Variable(901)), Eq(Public(1), Variable(901))),
        );
        assert_eq!(
            evaluate(&original, &labels, 100),
            evaluate(&changed, &renamed, 100)
        );
    }
}

#[test]
fn exhaustion_never_becomes_false_and_shortcircuit_is_justified() {
    assert_eq!(
        evaluate(&Bool(false), &[], 0),
        Err(Error::Exhausted(Resource::EvaluationSteps))
    );
    assert_eq!(evaluate(&Bool(false), &[], 1), Ok(false));
    assert_eq!(
        evaluate(&forall(1, Eq(Variable(1), Variable(1))), &[9], 2),
        Err(Error::Exhausted(Resource::EvaluationSteps))
    );
    assert_eq!(evaluate(&or(Bool(true), Bool(false)), &[], 2), Ok(true));
    assert_eq!(
        evaluate(&Bool(true), &[0; MAX_PUBLIC + 1], 100),
        Err(Error::Exhausted(Resource::PublicPorts))
    );
    let mut deep = Bool(true);
    for _ in 0..32 {
        deep = Not(Box::new(deep));
    }
    assert_eq!(
        evaluate(&deep, &[], 100),
        Err(Error::Exhausted(Resource::Depth))
    );
    let mut binders = Bool(true);
    for id in 0..17 {
        binders = exists(id, binders);
    }
    assert_eq!(
        evaluate(&binders, &[], 100),
        Err(Error::Exhausted(Resource::Binders))
    );
    // A balanced tree exceeds the node limit without exceeding depth.
    fn tree(depth: usize) -> Formula {
        if depth == 0 {
            Bool(true)
        } else {
            and(tree(depth - 1), tree(depth - 1))
        }
    }
    assert_eq!(
        evaluate(&tree(7), &[], 1000),
        Err(Error::Exhausted(Resource::Nodes))
    );
}

#[test]
fn orbit_results_match_direct_finite_domain_for_three_binder_formulas() {
    // A direct evaluator enumerates six actual values with no equality classes.
    // With two public ports and three binders, six values realize every equality
    // pattern this finite equality-only formula can observe. This is a bounded
    // differential for the implementation, not a finite-universe source rule.
    fn direct(f: &Formula, public: &[u64], bound: &mut Vec<(u64, u64)>) -> bool {
        let value = |a: &yu_core::shadow_atom_orbits::AtomRef| match a {
            Public(i) => public[*i],
            Variable(id) => bound.iter().find(|(b, _)| b == id).unwrap().1,
        };
        match f {
            Bool(v) => *v,
            Eq(a, b) => value(a) == value(b),
            Ne(a, b) => value(a) != value(b),
            Not(a) => !direct(a, public, bound),
            And(a, b) => direct(a, public, bound) && direct(b, public, bound),
            Or(a, b) => direct(a, public, bound) || direct(b, public, bound),
            Exists { binder, body } | ForAll { binder, body } => {
                let existential = matches!(f, Exists { .. });
                for actual in 0..6 {
                    bound.push((*binder, actual));
                    let answer = direct(body, public, bound);
                    bound.pop();
                    if answer == existential {
                        return existential;
                    }
                }
                !existential
            }
        }
    }
    let refs = [
        Public(0),
        Public(1),
        Variable(10),
        Variable(11),
        Variable(12),
    ];
    let mut atoms = Vec::new();
    for left in 0..refs.len() {
        for right in left..refs.len() {
            atoms.push(Eq(refs[left], refs[right]));
            atoms.push(Ne(refs[left], refs[right]));
        }
    }
    let mut compared = 0;
    for a in &atoms {
        for b in &atoms {
            for matrix in [
                and(a.clone(), b.clone()),
                or(a.clone(), Not(Box::new(b.clone()))),
            ] {
                for prefix in 0..8 {
                    let mut formula = matrix.clone();
                    for index in (0..3).rev() {
                        formula = if prefix & (1 << index) == 0 {
                            exists(10 + index, formula)
                        } else {
                            forall(10 + index, formula)
                        };
                    }
                    for public in [[0, 0], [0, 1]] {
                        assert_eq!(
                            evaluate(&formula, &public, 100_000),
                            Ok(direct(&formula, &public, &mut Vec::new()))
                        );
                        compared += 1;
                    }
                }
            }
        }
    }
    assert_eq!(compared, 28_800);
}
