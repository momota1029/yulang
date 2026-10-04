//! Test-only reconstruction candidate grounded in the admitted Lambda HIR and
//! Function constraint for the current `id` / `zero` source grammar.
//!
//! This does not define production Function-bound denotation. It connects the
//! source-derived body recipe and four-port artifact to a small typed-observation
//! model, then checks the Theorem C old-tuple-preserving lift over finite input
//! and request histories. The missing production denotation crosswalk remains.

use super::*;
use yu_types::{NegativeEffectView, PositiveEffectView};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BodyProgram {
    Identity,
    Constant(i32),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Request {
    operation: &'static str,
    origin: u8,
    continuation: u8,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Challenge {
    input: i32,
    requests: Vec<Request>,
    completes: bool,
    fiber: (u8, u8, u8),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Completion {
    Returned,
    Suspended { deferred_body: HirOccurrenceId },
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TypedObservation {
    requests: Vec<Request>,
    completion: Completion,
    result_type: &'static str,
    lambda_occurrence: HirOccurrenceId,
    body_occurrence: HirOccurrenceId,
    binder: HirParameterId,
    fiber: (u8, u8, u8),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct CheckedChallenge {
    old: Challenge,
    fresh_coordinate: u8,
}

struct SourceArtifact {
    body: BodyProgram,
    lambda_occurrence: HirOccurrenceId,
    body_occurrence: HirOccurrenceId,
    binder: HirParameterId,
}

fn source_body(expr: &ResolvedExpr, parameter: &HirParameterId) -> (BodyProgram, HirOccurrenceId) {
    let ResolvedExpr::Lambda {
        body,
        parameter: actual_parameter,
        ..
    } = expr
    else {
        panic!("source artifact is a Lambda");
    };
    assert_eq!(actual_parameter, parameter);
    match body.as_ref() {
        ResolvedExpr::Name {
            occurrence,
            resolution: NameResolution::Parameter(body_parameter),
            ..
        } if body_parameter == parameter => (BodyProgram::Identity, occurrence.clone()),
        ResolvedExpr::Integer {
            occurrence,
            spelling,
            ..
        } => (
            BodyProgram::Constant(spelling.parse().expect("integer HIR spelling")),
            occurrence.clone(),
        ),
        _ => panic!("the bounded source body is own-parameter Name or Integer"),
    }
}

fn inspect_artifact(source: &str, path: &str) -> SourceArtifact {
    let hir = module(source, path);
    assert!(hir.errors().is_empty(), "{source}");
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("one binding");
    };
    let ResolvedExpr::Lambda {
        occurrence: lambda_occurrence,
        parameter,
        ..
    } = binding.value()
    else {
        panic!("binding value is Lambda");
    };
    let (body, body_occurrence) = source_body(binding.value(), parameter);

    let batch = collect(hir.clone());
    let root_component = batch
        .root_value_component(binding.definition_root())
        .expect("collected source root");
    let root_term = batch.term_for_component(&root_component);
    let solved = SolvedModule::solve(batch).expect("bounded source Function solves");
    assert!(solved.errors().is_empty(), "{source}");

    let function_fact = solved
        .store()
        .facts()
        .iter()
        .find(|fact| {
            fact.upper() == root_term
                && matches!(
                    solved.store().term_view(fact.lower()),
                    Ok(TermView::PositiveFunction { .. })
                )
        })
        .expect("source Lambda contributes one positive Function fact");
    let lambda_fact_id = ConstraintOccurrenceId::new(lambda_occurrence.clone(), 2);
    assert!(solved.store().provenance().iter().any(|edge| {
        edge.fact() == function_fact.id() && edge.cause().occurrence() == &lambda_fact_id
    }));
    let TermView::PositiveFunction {
        argument,
        argument_effect,
        result_effect,
        result,
    } = solved.store().term_view(function_fact.lower()).unwrap()
    else {
        unreachable!()
    };
    let TermView::LiveVariable(argument_variable) = solved.store().term_view(argument).unwrap()
    else {
        panic!("Function argument is a live source parameter");
    };
    let TermView::LiveVariable(result_variable) = solved.store().term_view(result).unwrap() else {
        panic!("Function result is a live source value endpoint");
    };
    assert_eq!(argument_variable.polarity(), Polarity::Negative);
    assert_eq!(result_variable.polarity(), Polarity::Positive);
    assert!(matches!(
        solved.store().term_view(argument_effect),
        Ok(TermView::Leaf(Leaf::EmptyEffectNegative))
    ));
    assert!(matches!(
        solved.store().term_view(result_effect),
        Ok(TermView::LiveVariable(_))
    ));
    match body {
        BodyProgram::Identity => assert_eq!(argument_variable.ordinal(), result_variable.ordinal()),
        BodyProgram::Constant(_) => {
            assert_ne!(argument_variable.ordinal(), result_variable.ordinal())
        }
    }

    let scheme = solved.schemes[0].as_ref().expect("generalized source root");
    let scheme_view = solved.closed_types.scheme_view(scheme).unwrap();
    let quantifiers = scheme_view.quantifier_count();
    match body {
        BodyProgram::Identity => {
            assert_eq!(quantifiers, 1);
            let PositiveValueView::Function {
                argument,
                argument_effect,
                result_effect,
                result,
            } = scheme_view.positive_value(scheme_view.predicate()).unwrap()
            else {
                panic!("id public Function");
            };
            let NegativeValueView::Quantified(argument) =
                scheme_view.negative_value(argument).unwrap()
            else {
                panic!("id public argument variable");
            };
            let PositiveValueView::Quantified(result) = scheme_view.positive_value(result).unwrap()
            else {
                panic!("id public result variable");
            };
            assert_eq!(argument.ordinal(), result.ordinal());
            assert!(matches!(
                scheme_view.negative_effect(argument_effect),
                Ok(NegativeEffectView::Empty)
            ));
            assert!(matches!(
                scheme_view.positive_effect(result_effect),
                Ok(PositiveEffectView::Bottom)
            ));
        }
        BodyProgram::Constant(0) => {
            assert_eq!(quantifiers, 0);
            let PositiveValueView::Function {
                argument,
                argument_effect,
                result_effect,
                result,
            } = scheme_view.positive_value(scheme_view.predicate()).unwrap()
            else {
                panic!("zero public Function");
            };
            assert!(matches!(
                scheme_view.negative_value(argument),
                Ok(NegativeValueView::Top)
            ));
            assert!(matches!(
                scheme_view.positive_value(result),
                Ok(PositiveValueView::Int)
            ));
            assert!(matches!(
                scheme_view.negative_effect(argument_effect),
                Ok(NegativeEffectView::Empty)
            ));
            assert!(matches!(
                scheme_view.positive_effect(result_effect),
                Ok(PositiveEffectView::Bottom)
            ));
        }
        BodyProgram::Constant(_) => panic!("only the accepted zero body is in this model"),
    }

    SourceArtifact {
        body,
        lambda_occurrence: lambda_occurrence.clone(),
        body_occurrence,
        binder: parameter.clone(),
    }
}

fn histories() -> Vec<(Vec<Request>, bool)> {
    let alphabet = ["Read", "Write"];
    let mut out = vec![(Vec::new(), true)];
    for operation in alphabet {
        let request = Request {
            operation,
            origin: 0,
            continuation: 0,
        };
        out.push((vec![request.clone()], true));
        out.push((vec![request], false));
    }
    for first in alphabet {
        for second in alphabet {
            let requests = vec![
                Request {
                    operation: first,
                    origin: 0,
                    continuation: 0,
                },
                Request {
                    operation: second,
                    origin: 1,
                    continuation: 1,
                },
            ];
            out.push((requests.clone(), true));
            out.push((requests, false));
        }
    }
    out
}

fn generated_domain() -> Vec<Challenge> {
    // The domain is generated from the instantiated Int input skeleton and
    // finite argument-computation history grammar, never from comparison.
    (0..=1)
        .flat_map(|input| {
            histories()
                .into_iter()
                .map(move |(requests, completes)| Challenge {
                    input,
                    requests,
                    completes,
                    // One fixed assignment; source identity stays in its own
                    // fields and is never reused as a nu/K/D coordinate.
                    fiber: (0, 0, 0),
                })
        })
        .collect()
}

fn source_output(body: BodyProgram, input: i32) -> i32 {
    match body {
        BodyProgram::Identity => input,
        BodyProgram::Constant(value) => value,
    }
}

fn projected_observation(artifact: &SourceArtifact, challenge: &Challenge) -> TypedObservation {
    let completion = if challenge.completes {
        let _erased_data_output = source_output(artifact.body, challenge.input);
        Completion::Returned
    } else {
        Completion::Suspended {
            // The body is deferred behind the pending argument request. This
            // projection records its source identity; it does not execute a
            // response/resumption transition or the pending suffix.
            deferred_body: artifact.body_occurrence.clone(),
        }
    };
    TypedObservation {
        requests: challenge.requests.clone(),
        completion,
        result_type: "int",
        lambda_occurrence: artifact.lambda_occurrence.clone(),
        body_occurrence: artifact.body_occurrence.clone(),
        binder: artifact.binder.clone(),
        fiber: challenge.fiber,
    }
}

fn checked_lift(challenge: Challenge) -> CheckedChallenge {
    // One total fresh coordinate defined from the complete retained tuple.
    let fresh_coordinate =
        ((challenge.input as usize + challenge.requests.len() + usize::from(challenge.completes))
            % 2) as u8;
    CheckedChallenge {
        old: challenge,
        fresh_coordinate,
    }
}

#[test]
fn source_hir_function_realization_and_checked_lift_match_on_bounded_histories() {
    for (source, path, expected_body) in [
        ("my id x = x", "research-id.yu", BodyProgram::Identity),
        (
            "my zero x = 0",
            "research-zero.yu",
            BodyProgram::Constant(0),
        ),
    ] {
        let artifact = inspect_artifact(source, path);
        assert_eq!(artifact.body, expected_body);

        let domain = generated_domain();
        assert_eq!(domain.len(), 26);
        let actual = domain
            .iter()
            .map(|challenge| projected_observation(&artifact, challenge))
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(actual.len(), 13);

        // Query-independent checked admission uses the same old challenges;
        // total extension adds no condition and projection forgets only W.
        let checked = domain.iter().cloned().map(checked_lift).collect::<Vec<_>>();
        assert_eq!(checked.len(), domain.len());
        let checked_old_tuples = checked
            .iter()
            .map(|item| item.old.clone())
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(checked_old_tuples, domain.iter().cloned().collect());
        assert!(checked.iter().all(|item| item.old.fiber == (0, 0, 0)));
        let checked_projection = checked
            .iter()
            .map(|item| projected_observation(&artifact, &item.old))
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(actual, checked_projection);
    }
}
