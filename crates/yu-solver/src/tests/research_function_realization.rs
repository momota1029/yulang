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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReceiverRole {
    Pure,
    HandlerView,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum InvocationStep {
    Receipt,
    ForceArgument,
    Request {
        request: Request,
        state: u8,
    },
    Resume {
        origin: u8,
        continuation: u8,
        value_type: &'static str,
        state_before: u8,
        state_after: u8,
    },
    EnterBody {
        occurrence: HirOccurrenceId,
        binder: HirParameterId,
    },
    Return {
        value_type: &'static str,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ResultConsumerStep {
    Request {
        request: Request,
        state: u8,
    },
    Resume {
        origin: u8,
        continuation: u8,
        state_before: u8,
        state_after: u8,
    },
    // This marks delivery by the consumer, after the callback body's return.
    Return,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SuspendedResultConsumer {
    callback_trace: Vec<InvocationStep>,
    consumer_trace: Vec<ResultConsumerStep>,
    callback_result: i32,
    pending: Request,
    state: u8,
    actual_role: ReceiverRole,
    callback_view: ReceiverRole,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ResultConsumerOutcome {
    Returned {
        callback_trace: Vec<InvocationStep>,
        consumer_trace: Vec<ResultConsumerStep>,
        callback_result: i32,
        final_state: u8,
        actual_role: ReceiverRole,
        callback_view: ReceiverRole,
    },
    Suspended(SuspendedResultConsumer),
}

fn run_designated_result_consumer(
    invocation: InvocationResult,
    request: Request,
    decision: RequestDecision,
) -> ResultConsumerOutcome {
    let InvocationResult::Returned {
        trace,
        final_state,
        actual_role,
        callback_view,
        result_value,
    } = invocation
    else {
        panic!("the designated result consumer follows callback return");
    };
    let mut consumer_trace = vec![ResultConsumerStep::Request {
        request: request.clone(),
        state: final_state,
    }];
    match decision {
        RequestDecision::Forward => ResultConsumerOutcome::Suspended(SuspendedResultConsumer {
            callback_trace: trace,
            consumer_trace,
            callback_result: result_value,
            pending: request,
            state: final_state,
            actual_role,
            callback_view,
        }),
        RequestDecision::Handle { state_after, .. } => {
            consumer_trace.push(ResultConsumerStep::Resume {
                origin: request.origin,
                continuation: request.continuation,
                state_before: final_state,
                state_after,
            });
            consumer_trace.push(ResultConsumerStep::Return);
            ResultConsumerOutcome::Returned {
                callback_trace: trace,
                consumer_trace,
                callback_result: result_value,
                final_state: state_after,
                actual_role,
                callback_view,
            }
        }
    }
}

fn resume_designated_result_consumer(
    mut suspended: SuspendedResultConsumer,
    decision: RequestDecision,
) -> ResultConsumerOutcome {
    let RequestDecision::Handle { state_after, .. } = decision else {
        panic!("the forwarded result-consumer request receives a response");
    };
    suspended.consumer_trace.push(ResultConsumerStep::Resume {
        origin: suspended.pending.origin,
        continuation: suspended.pending.continuation,
        state_before: suspended.state,
        state_after,
    });
    suspended.consumer_trace.push(ResultConsumerStep::Return);
    ResultConsumerOutcome::Returned {
        callback_trace: suspended.callback_trace,
        consumer_trace: suspended.consumer_trace,
        callback_result: suspended.callback_result,
        final_state: state_after,
        actual_role: suspended.actual_role,
        callback_view: suspended.callback_view,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RequestDecision {
    Handle { value: i32, state_after: u8 },
    Forward,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SuspendedInvocation {
    trace: Vec<InvocationStep>,
    actual_role: ReceiverRole,
    callback_view: ReceiverRole,
    pending: Request,
    current_state: u8,
    argument_value: i32,
    suffix: Vec<Request>,
    suffix_decisions: Vec<RequestDecision>,
    body: BodyProgram,
    body_occurrence: HirOccurrenceId,
    binder: HirParameterId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum InvocationResult {
    Returned {
        trace: Vec<InvocationStep>,
        actual_role: ReceiverRole,
        callback_view: ReceiverRole,
        result_value: i32,
        final_state: u8,
    },
    Suspended(SuspendedInvocation),
}

fn advance_requests(
    mut trace: Vec<InvocationStep>,
    mut current_state: u8,
    mut argument_value: i32,
    requests: Vec<Request>,
    decisions: Vec<RequestDecision>,
    body: BodyProgram,
    actual_role: ReceiverRole,
    callback_view: ReceiverRole,
    body_occurrence: HirOccurrenceId,
    binder: HirParameterId,
) -> InvocationResult {
    assert_eq!(requests.len(), decisions.len());
    for (index, (request, decision)) in requests
        .iter()
        .cloned()
        .zip(decisions.iter().cloned())
        .enumerate()
    {
        trace.push(InvocationStep::Request {
            request: request.clone(),
            state: current_state,
        });
        match decision {
            RequestDecision::Handle { value, state_after } => {
                trace.push(InvocationStep::Resume {
                    origin: request.origin,
                    continuation: request.continuation,
                    value_type: "int",
                    state_before: current_state,
                    state_after,
                });
                current_state = state_after;
                argument_value = value;
            }
            RequestDecision::Forward => {
                return InvocationResult::Suspended(SuspendedInvocation {
                    trace,
                    actual_role,
                    callback_view,
                    pending: request,
                    current_state,
                    argument_value,
                    suffix: requests[index + 1..].to_vec(),
                    suffix_decisions: decisions[index + 1..].to_vec(),
                    body,
                    body_occurrence,
                    binder,
                });
            }
        }
    }
    trace.push(InvocationStep::EnterBody {
        occurrence: body_occurrence,
        binder,
    });
    trace.push(InvocationStep::Return { value_type: "int" });
    InvocationResult::Returned {
        trace,
        actual_role,
        callback_view,
        result_value: match body {
            BodyProgram::Identity => argument_value,
            BodyProgram::Constant(value) => value,
        },
        final_state: current_state,
    }
}

fn invoke_pure_value_through_handler_view(
    artifact: &SourceArtifact,
    requests: Vec<Request>,
    decisions: Vec<RequestDecision>,
) -> InvocationResult {
    invoke_pure_value_through_handler_view_from_state(artifact, 0, requests, decisions)
}

fn invoke_pure_value_through_handler_view_from_state(
    artifact: &SourceArtifact,
    initial_state: u8,
    requests: Vec<Request>,
    decisions: Vec<RequestDecision>,
) -> InvocationResult {
    advance_requests(
        vec![InvocationStep::Receipt, InvocationStep::ForceArgument],
        initial_state,
        0,
        requests,
        decisions,
        artifact.body,
        ReceiverRole::Pure,
        ReceiverRole::HandlerView,
        artifact.body_occurrence.clone(),
        artifact.binder.clone(),
    )
}

fn resume_invocation(
    mut suspended: SuspendedInvocation,
    response: RequestDecision,
) -> InvocationResult {
    let RequestDecision::Handle { value, state_after } = response else {
        panic!("a resumed request receives a response");
    };
    suspended.trace.push(InvocationStep::Resume {
        origin: suspended.pending.origin,
        continuation: suspended.pending.continuation,
        value_type: "int",
        state_before: suspended.current_state,
        state_after,
    });
    advance_requests(
        suspended.trace,
        state_after,
        value,
        suspended.suffix,
        suspended.suffix_decisions,
        suspended.body,
        suspended.actual_role,
        suspended.callback_view,
        suspended.body_occurrence,
        suspended.binder,
    )
}

// Evidence handles belong to this solved store; closed projection does not
// identify its polarized Bottom with the body's empty-effect projection.
#[derive(Clone, Debug)]
struct FunctionReconstruction {
    recipe: LambdaRecipe,
    body_occurrence: HirOccurrenceId,
    body_slots: (u8, u8),
    body_row: u32,
    construction_row: u32,
    body_component: Term,
    construction_component: Term,
    ports: [Term; 4],
}

fn reconstruction_inputs(session: &InferenceSession) -> Vec<FunctionReconstruction> {
    session
        .batch
        .lambda_recipes
        .iter()
        .map(|recipe| {
            let binding = session
                .batch
                .hir
                .items()
                .iter()
                .find_map(|item| match item {
                    HirItem::Binding(binding)
                        if binding.value().occurrence() == &recipe.occurrence =>
                    {
                        Some(binding)
                    }
                    _ => None,
                })
                .expect("recipe source Lambda");
            let ResolvedExpr::Lambda { body, .. } = binding.value() else {
                unreachable!()
            };
            let slots = match body.as_ref() {
                ResolvedExpr::Integer { .. } => (2, 3),
                ResolvedExpr::Name {
                    resolution: NameResolution::Parameter(_),
                    ..
                } => (0, 1),
                ResolvedExpr::Name {
                    resolution: NameResolution::Resolved(_),
                    ..
                } => (1, 2),
                _ => panic!("admitted recipe body"),
            };
            // Ports are filled from the admitted Function, never synthesized here.
            let placeholder = session.batch.component_term_at(recipe.root_component);
            FunctionReconstruction {
                recipe: recipe.clone(),
                body_occurrence: body.occurrence().clone(),
                body_slots: slots,
                body_component: session
                    .batch
                    .component_term_at(recipe.body_effect_component),
                construction_component: session
                    .batch
                    .component_term_at(recipe.lambda_effect_component),
                body_row: session.live_components[recipe.body_effect_component].ordinal,
                construction_row: session.live_components[recipe.lambda_effect_component].ordinal,
                ports: [placeholder; 4],
            }
        })
        .collect()
}

fn retained_function_ports(solved: &SolvedModule, occurrence: &HirOccurrenceId) -> [Term; 4] {
    let cause = ConstraintOccurrenceId::new(occurrence.clone(), 2);
    let fact = solved
        .store()
        .facts()
        .iter()
        .find(|fact| {
            solved
                .store()
                .provenance()
                .iter()
                .any(|edge| edge.fact() == fact.id() && edge.cause().occurrence() == &cause)
                && matches!(
                    solved.store().term_view(fact.lower()),
                    Ok(TermView::PositiveFunction { .. })
                )
        })
        .expect("retained source Function fact");
    let TermView::PositiveFunction {
        argument,
        argument_effect,
        result_effect,
        result,
    } = solved.store().term_view(fact.lower()).unwrap()
    else {
        unreachable!()
    };
    [argument, argument_effect, result_effect, result]
}

fn row_matches(solved: &SolvedModule, term: Term, row: u32, polarity: Polarity) -> bool {
    matches!(solved.store().term_view(term), Ok(TermView::LiveVariable(variable))
        if variable.kind() == ComponentKind::Effect && variable.ordinal() == row && variable.polarity() == polarity)
}

fn reconstruction_matches(solved: &SolvedModule, record: &FunctionReconstruction) -> bool {
    record.body_row != record.construction_row
        && record.ports == retained_function_ports(solved, &record.recipe.occurrence)
        && row_matches(solved, record.ports[2], record.body_row, Polarity::Positive)
}

fn reconstructions_other_row(solved: &SolvedModule, record: &FunctionReconstruction) -> u32 {
    solved
        .store()
        .facts()
        .iter()
        .find_map(|fact| {
            let Ok(TermView::PositiveFunction { result_effect, .. }) =
                solved.store().term_view(fact.lower())
            else {
                return None;
            };
            let Ok(TermView::LiveVariable(row)) = solved.store().term_view(result_effect) else {
                return None;
            };
            (row.kind() == ComponentKind::Effect
                && row.ordinal() != record.body_row
                && row.ordinal() != record.construction_row)
                .then_some(row.ordinal())
        })
        .expect("another source Lambda owns a different body row")
}

fn check_reconstruction(solved: &SolvedModule, record: &FunctionReconstruction) {
    assert!(reconstruction_matches(solved, record));
    assert!(solved.occurrences().contains(&record.recipe.occurrence));
    assert!(!solved.occurrences().contains(&record.body_occurrence));
    for (occurrence, component, slots) in [
        (
            &record.body_occurrence,
            record.body_component,
            record.body_slots,
        ),
        (
            &record.recipe.occurrence,
            record.construction_component,
            (0, 1),
        ),
    ] {
        for (slot, lower_bound) in [(slots.0, true), (slots.1, false)] {
            let cause = ConstraintOccurrenceId::new(occurrence.clone(), slot);
            assert!(
                solved.store().facts().iter().any(|fact| {
                    let endpoints_match = if lower_bound {
                        matches!(
                            solved.store().term_view(fact.lower()),
                            Ok(TermView::Leaf(Leaf::EffectBottomPositive))
                        ) && fact.upper() == component
                    } else {
                        fact.lower() == component
                            && matches!(
                                solved.store().term_view(fact.upper()),
                                Ok(TermView::Leaf(Leaf::EmptyEffectNegative))
                            )
                    };
                    endpoints_match
                        && solved.store().provenance().iter().any(|edge| {
                            edge.fact() == fact.id() && edge.cause().occurrence() == &cause
                        })
                }),
                "retained effect occurrence/slot/polarity"
            );
        }
    }
    // The source Lambda is published as an F4 projection; its internal body is not.
    assert_eq!(
        solved
            .projection_for(&record.recipe.occurrence)
            .unwrap()
            .effect(),
        SolvedEffect::Empty
    );
}

struct SourceArtifact {
    body: BodyProgram,
    lambda_occurrence: HirOccurrenceId,
    body_occurrence: HirOccurrenceId,
    binder: HirParameterId,
    reconstruction: FunctionReconstruction,
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
    let session = InferenceSession::try_new(batch).unwrap();
    let mut records = reconstruction_inputs(&session);
    let solved = session.run().expect("bounded source Function solves");
    let mut reconstruction = records.remove(0);
    reconstruction.ports = retained_function_ports(&solved, &reconstruction.recipe.occurrence);
    check_reconstruction(&solved, &reconstruction);
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
        reconstruction,
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
    assert_eq!(
        artifact.reconstruction.body_occurrence,
        artifact.body_occurrence
    );
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

#[test]
fn resumed_force_bind_keeps_suffix_and_underlying_pure_entry() {
    let artifact = inspect_artifact("my id x = x", "research-id-resume.yu");
    let requests = vec![
        Request {
            operation: "Read",
            origin: 4,
            continuation: 10,
        },
        Request {
            operation: "Write",
            origin: 5,
            continuation: 11,
        },
    ];

    // The first request is handled, the second is forwarded, then the same
    // pending continuation is resumed. The source body runs only afterward.
    let InvocationResult::Suspended(suspended) = invoke_pure_value_through_handler_view(
        &artifact,
        requests.clone(),
        vec![
            RequestDecision::Handle {
                value: 17,
                state_after: 20,
            },
            RequestDecision::Forward,
        ],
    ) else {
        panic!("second argument request is forwarded");
    };
    assert_eq!(suspended.pending, requests[1]);
    let InvocationResult::Returned {
        trace,
        actual_role,
        callback_view,
        result_value,
        final_state,
    } = resume_invocation(
        suspended,
        RequestDecision::Handle {
            value: 23,
            state_after: 21,
        },
    )
    else {
        panic!("resuming the final request reaches the body");
    };
    assert_eq!(actual_role, ReceiverRole::Pure);
    assert_eq!(callback_view, ReceiverRole::HandlerView);
    assert_eq!(result_value, 23);
    assert_eq!(final_state, 21);
    assert_eq!(
        trace,
        vec![
            InvocationStep::Receipt,
            InvocationStep::ForceArgument,
            InvocationStep::Request {
                request: requests[0].clone(),
                state: 0,
            },
            InvocationStep::Resume {
                origin: requests[0].origin,
                continuation: requests[0].continuation,
                value_type: "int",
                state_before: 0,
                state_after: 20,
            },
            InvocationStep::Request {
                request: requests[1].clone(),
                state: 20,
            },
            InvocationStep::Resume {
                origin: requests[1].origin,
                continuation: requests[1].continuation,
                value_type: "int",
                state_before: 20,
                state_after: 21,
            },
            InvocationStep::EnterBody {
                occurrence: artifact.body_occurrence.clone(),
                binder: artifact.binder.clone(),
            },
            InvocationStep::Return { value_type: "int" },
        ]
    );

    // The opposite split forwards the first request, resumes it once, then
    // forwards and resumes the suffix request. Neither outer receipt nor
    // Force is replayed when these nested continuations are resumed.
    let InvocationResult::Suspended(first) = invoke_pure_value_through_handler_view(
        &artifact,
        requests.clone(),
        vec![RequestDecision::Forward, RequestDecision::Forward],
    ) else {
        panic!("first request is forwarded");
    };
    let InvocationResult::Suspended(second) = resume_invocation(
        first,
        RequestDecision::Handle {
            value: 29,
            state_after: 22,
        },
    ) else {
        panic!("suffix request is forwarded after resuming the first");
    };
    assert_eq!(second.pending, requests[1]);
    assert_eq!(second.current_state, 22);
    let InvocationResult::Returned {
        trace,
        actual_role,
        callback_view,
        result_value,
        final_state,
    } = resume_invocation(
        second,
        RequestDecision::Handle {
            value: 31,
            state_after: 23,
        },
    )
    else {
        panic!("resuming both requests reaches the body");
    };
    assert_eq!(actual_role, ReceiverRole::Pure);
    assert_eq!(callback_view, ReceiverRole::HandlerView);
    assert_eq!(result_value, 31);
    assert_eq!(final_state, 23);
    assert_eq!(
        trace,
        vec![
            InvocationStep::Receipt,
            InvocationStep::ForceArgument,
            InvocationStep::Request {
                request: requests[0].clone(),
                state: 0,
            },
            InvocationStep::Resume {
                origin: requests[0].origin,
                continuation: requests[0].continuation,
                value_type: "int",
                state_before: 0,
                state_after: 22,
            },
            InvocationStep::Request {
                request: requests[1].clone(),
                state: 22,
            },
            InvocationStep::Resume {
                origin: requests[1].origin,
                continuation: requests[1].continuation,
                value_type: "int",
                state_before: 22,
                state_after: 23,
            },
            InvocationStep::EnterBody {
                occurrence: artifact.body_occurrence.clone(),
                binder: artifact.binder.clone(),
            },
            InvocationStep::Return { value_type: "int" },
        ]
    );
    assert_eq!(
        trace
            .iter()
            .filter(|step| matches!(step, InvocationStep::Receipt))
            .count(),
        1
    );
    assert_eq!(
        trace
            .iter()
            .filter(|step| matches!(step, InvocationStep::ForceArgument))
            .count(),
        1
    );
    assert_eq!(
        trace
            .iter()
            .filter(|step| matches!(step, InvocationStep::Request { .. }))
            .count(),
        2
    );
    assert_eq!(
        trace
            .iter()
            .filter(|step| matches!(step, InvocationStep::EnterBody { .. }))
            .count(),
        1
    );
    assert_eq!(
        trace.last(),
        Some(&InvocationStep::Return { value_type: "int" })
    );
}

#[test]
fn designated_consumer_resumes_after_the_hir_derived_callback_returns() {
    let response_alphabet = [(0, 0), (0, 1), (1, 0), (1, 1)];
    let mut histories = vec![Vec::new()];
    for length in 1..=2 {
        let previous = histories.clone();
        for prefix in previous
            .into_iter()
            .filter(|history| history.len() == length - 1)
        {
            for response in response_alphabet {
                let mut history = prefix.clone();
                history.push(response);
                histories.push(history);
            }
        }
    }
    assert_eq!(histories.len(), 21);

    let mut callback_cases = 0;
    let mut consumer_resumptions = 0;
    for (source, body, path) in [
        (
            "my id x = x",
            BodyProgram::Identity,
            "research-id-consumer.yu",
        ),
        (
            "my zero x = 0",
            BodyProgram::Constant(0),
            "research-zero-consumer.yu",
        ),
    ] {
        let artifact = inspect_artifact(source, path);
        assert_eq!(artifact.body, body);
        for (history_index, history) in histories.iter().enumerate() {
            let requests = history
                .iter()
                .enumerate()
                .map(|(index, _)| Request {
                    operation: if index % 2 == 0 { "Read" } else { "Write" },
                    origin: index as u8 + 13,
                    continuation: index as u8 + 17,
                })
                .collect::<Vec<_>>();
            let decisions = history
                .iter()
                .map(|(value, state_after)| RequestDecision::Handle {
                    value: *value,
                    state_after: *state_after,
                })
                .collect::<Vec<_>>();
            let InvocationResult::Returned {
                trace: callback_trace,
                result_value,
                final_state,
                actual_role,
                callback_view,
            } = invoke_pure_value_through_handler_view(&artifact, requests.clone(), decisions)
            else {
                panic!("all Force requests are handled in this finite family");
            };
            let expected_value = match body {
                BodyProgram::Identity => history.last().map_or(0, |(value, _)| *value),
                BodyProgram::Constant(value) => value,
            };
            let expected_state = history.last().map_or(0, |(_, state)| *state);
            assert_eq!(result_value, expected_value);
            assert_eq!(final_state, expected_state);

            let request = Request {
                operation: "Publish",
                origin: history_index as u8 + 31,
                continuation: history_index as u8 + 63,
            };
            let ResultConsumerOutcome::Suspended(suspended) = run_designated_result_consumer(
                InvocationResult::Returned {
                    trace: callback_trace.clone(),
                    actual_role,
                    callback_view,
                    result_value,
                    final_state,
                },
                request.clone(),
                RequestDecision::Forward,
            ) else {
                panic!("the designated consumer forwards its request");
            };
            assert_eq!(suspended.pending, request);
            assert_eq!(suspended.callback_trace, callback_trace);
            assert_eq!(suspended.callback_result, result_value);
            assert_eq!(suspended.state, final_state);
            callback_cases += 1;

            for consumer_state in 0..=1 {
                let ResultConsumerOutcome::Returned {
                    callback_trace: resumed_callback,
                    consumer_trace,
                    callback_result,
                    final_state: consumer_final_state,
                    actual_role,
                    callback_view,
                } = resume_designated_result_consumer(
                    suspended.clone(),
                    RequestDecision::Handle {
                        value: 1,
                        state_after: consumer_state,
                    },
                )
                else {
                    panic!("resuming the consumer returns from this bounded trace");
                };
                assert_eq!(resumed_callback, callback_trace);
                assert_eq!(callback_result, result_value);
                assert_eq!(consumer_final_state, consumer_state);
                assert_eq!(actual_role, ReceiverRole::Pure);
                assert_eq!(callback_view, ReceiverRole::HandlerView);
                assert_eq!(
                    consumer_trace,
                    vec![
                        ResultConsumerStep::Request {
                            request: request.clone(),
                            state: final_state,
                        },
                        ResultConsumerStep::Resume {
                            origin: request.origin,
                            continuation: request.continuation,
                            state_before: final_state,
                            state_after: consumer_state,
                        },
                        ResultConsumerStep::Return,
                    ]
                );
                assert_eq!(
                    resumed_callback
                        .iter()
                        .filter(|step| matches!(step, InvocationStep::Receipt))
                        .count(),
                    1
                );
                assert_eq!(
                    resumed_callback
                        .iter()
                        .filter(|step| matches!(step, InvocationStep::ForceArgument))
                        .count(),
                    1
                );
                assert_eq!(
                    resumed_callback
                        .iter()
                        .filter(|step| matches!(step, InvocationStep::EnterBody { .. }))
                        .count(),
                    1
                );
                assert_eq!(
                    resumed_callback
                        .iter()
                        .filter(|step| matches!(step, InvocationStep::Request { .. }))
                        .count(),
                    history.len()
                );
                consumer_resumptions += 1;
            }
        }
    }
    assert_eq!(callback_cases, 42);
    assert_eq!(consumer_resumptions, 84);
}

fn binding_named<'a>(hir: &'a HirModule, name: &str) -> (usize, &'a yu_hir::HirBinding) {
    hir.items()
        .iter()
        .enumerate()
        .find_map(|(index, item)| match item {
            HirItem::Binding(binding) if binding.id().spelling() == name => Some((index, binding)),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing binding {name}"))
}

fn assert_diagonal_function_scheme(
    solved: &SolvedModule,
    binding_index: usize,
    nested_result: bool,
) {
    let scheme = solved.schemes[binding_index]
        .as_ref()
        .expect("every source root gets a closed scheme");
    let view = solved.closed_types.scheme_view(scheme).unwrap();
    assert_eq!(view.quantifier_count(), 1);
    let PositiveValueView::Function {
        argument,
        argument_effect,
        result_effect,
        result,
    } = view.positive_value(view.predicate()).unwrap()
    else {
        panic!("expected Function scheme");
    };
    assert!(matches!(
        view.negative_effect(argument_effect),
        Ok(NegativeEffectView::Empty)
    ));
    assert!(matches!(
        view.positive_effect(result_effect),
        Ok(PositiveEffectView::Bottom)
    ));

    let (diagonal_argument, diagonal_result) = if nested_result {
        assert!(matches!(
            view.negative_value(argument),
            Ok(NegativeValueView::Top)
        ));
        let PositiveValueView::Function {
            argument,
            argument_effect,
            result_effect,
            result,
        } = view.positive_value(result).unwrap()
        else {
            panic!("wrapper returns the source Function value");
        };
        assert!(matches!(
            view.negative_effect(argument_effect),
            Ok(NegativeEffectView::Empty)
        ));
        assert!(matches!(
            view.positive_effect(result_effect),
            Ok(PositiveEffectView::Bottom)
        ));
        (argument, result)
    } else {
        (argument, result)
    };
    let NegativeValueView::Quantified(argument) = view.negative_value(diagonal_argument).unwrap()
    else {
        panic!("diagonal Function argument is quantified");
    };
    let PositiveValueView::Quantified(result) = view.positive_value(diagonal_result).unwrap()
    else {
        panic!("diagonal Function result is quantified");
    };
    assert_eq!(argument.ordinal(), result.ordinal());
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum WrapperReturnStep {
    Receipt,
    ForceArgument,
    Request {
        request: Request,
        state: u8,
    },
    Resume {
        origin: u8,
        continuation: u8,
        state_before: u8,
        state_after: u8,
    },
    EnterBody {
        occurrence: HirOccurrenceId,
        binder: HirParameterId,
    },
    ReturnCallable {
        source_root: yu_hir::DefId,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ReturnedCallable {
    trace: Vec<WrapperReturnStep>,
    source_root: yu_hir::DefId,
    final_state: u8,
}

fn run_source_wrapper_to_returned_callable(
    wrapper: &yu_hir::HirBinding,
    id_root: &yu_hir::HirBinding,
    requests: &[Request],
    decisions: &[RequestDecision],
) -> ReturnedCallable {
    assert_eq!(requests.len(), decisions.len());
    let ResolvedExpr::Lambda {
        parameter, body, ..
    } = wrapper.value()
    else {
        panic!("the wrapper is a source Lambda");
    };
    let ResolvedExpr::Name {
        resolution: NameResolution::Resolved(returned_root),
        ..
    } = body.as_ref()
    else {
        panic!("the wrapper returns a resolved source root");
    };
    assert_eq!(returned_root, id_root.id());
    let ResolvedExpr::Name {
        occurrence: returned_occurrence,
        ..
    } = body.as_ref()
    else {
        unreachable!()
    };

    let mut trace = vec![WrapperReturnStep::Receipt, WrapperReturnStep::ForceArgument];
    let mut state = 0;
    for (request, decision) in requests.iter().zip(decisions) {
        trace.push(WrapperReturnStep::Request {
            request: request.clone(),
            state,
        });
        let RequestDecision::Handle { state_after, .. } = decision else {
            panic!("the bounded returned-callable trace completes the wrapper Force");
        };
        trace.push(WrapperReturnStep::Resume {
            origin: request.origin,
            continuation: request.continuation,
            state_before: state,
            state_after: *state_after,
        });
        state = *state_after;
    }
    trace.push(WrapperReturnStep::EnterBody {
        occurrence: returned_occurrence.clone(),
        binder: parameter.clone(),
    });
    trace.push(WrapperReturnStep::ReturnCallable {
        source_root: returned_root.clone(),
    });
    ReturnedCallable {
        trace,
        source_root: returned_root.clone(),
        final_state: state,
    }
}

fn generated_handled_histories(
    max_len: usize,
    origin_base: u8,
) -> Vec<(Vec<Request>, Vec<RequestDecision>)> {
    let mut histories = vec![(Vec::new(), Vec::new())];
    let alphabet = ["Read", "Write"];
    for length in 1..=max_len {
        for operation_codes in 0..alphabet.len().pow(length as u32) {
            for responses in 0..4usize.pow(length as u32) {
                let mut code = operation_codes;
                let mut response_code = responses;
                let mut requests = Vec::with_capacity(length);
                let mut decisions = Vec::with_capacity(length);
                for index in 0..length {
                    let operation = alphabet[code % alphabet.len()];
                    code /= alphabet.len();
                    requests.push(Request {
                        operation,
                        origin: origin_base + index as u8,
                        continuation: origin_base + 32 + index as u8,
                    });
                    let state_after = (response_code % 2) as u8;
                    response_code /= 2;
                    let value = (response_code % 2) as i32;
                    response_code /= 2;
                    decisions.push(RequestDecision::Handle { value, state_after });
                }
                histories.push((requests, decisions));
            }
        }
    }
    histories
}

#[test]
fn returned_function_aliases_keep_source_identity_and_principal_diagonal() {
    fn permutations(items: &mut [&'static str], at: usize, out: &mut Vec<Vec<&'static str>>) {
        if at == items.len() {
            out.push(items.to_vec());
            return;
        }
        for index in at..items.len() {
            items.swap(at, index);
            permutations(items, at + 1, out);
            items.swap(at, index);
        }
    }

    let mut orders = Vec::new();
    permutations(&mut ["id", "wrap", "left", "right"], 0, &mut orders);
    assert_eq!(orders.len(), 24);
    let mut case_count = 0;
    for order in orders {
        for (id_parameter, wrap_parameter) in [
            ("x", "ignored"),
            ("value", "skipped"),
            ("input", "unused"),
            ("arg", "discard"),
        ] {
            let declarations = std::collections::HashMap::from([
                ("id", format!("my id {id_parameter} = {id_parameter}")),
                ("wrap", format!("my wrap {wrap_parameter} = id")),
                ("left", "my left = wrap".to_owned()),
                ("right", "my right = wrap".to_owned()),
            ]);
            let source = order
                .iter()
                .map(|name| declarations[name].as_str())
                .collect::<Vec<_>>()
                .join("\n");
            let path = format!("research-returned-function-alias-{case_count}.yu");
            let hir = module(&source, &path);
            assert!(hir.errors().is_empty(), "{source}");
            assert_eq!(
                hir.items()
                    .iter()
                    .filter_map(|item| match item {
                        HirItem::Binding(binding) => Some(binding.id().spelling()),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
                order
            );
            let (id_index, id_binding) = binding_named(&hir, "id");
            let (wrap_index, wrap_binding) = binding_named(&hir, "wrap");
            let (_, left_binding) = binding_named(&hir, "left");
            let (_, right_binding) = binding_named(&hir, "right");

            let ResolvedExpr::Lambda { body, .. } = wrap_binding.value() else {
                panic!("wrap is a source Lambda");
            };
            let ResolvedExpr::Name {
                resolution: NameResolution::Resolved(returned_root),
                ..
            } = body.as_ref()
            else {
                panic!("wrap returns one resolved source root");
            };
            assert_eq!(returned_root, id_binding.id());
            for alias in [left_binding, right_binding] {
                let ResolvedExpr::Name {
                    resolution: NameResolution::Resolved(alias_root),
                    ..
                } = alias.value()
                else {
                    panic!("aliases retain a resolved source root");
                };
                assert_eq!(alias_root, wrap_binding.id());
            }

            let batch = collect(hir.clone());
            assert_eq!(batch.definition_uses().len(), 3);
            let names_by_ordinal = hir
                .items()
                .iter()
                .filter_map(|item| match item {
                    HirItem::Binding(binding) => Some(binding.id().spelling()),
                    _ => None,
                })
                .enumerate()
                .map(|(ordinal, name)| (ordinal as u32, name))
                .collect::<std::collections::HashMap<_, _>>();
            let mut use_edges = batch
                .definition_uses()
                .iter()
                .map(|usage| {
                    (
                        names_by_ordinal[&usage.parent().ordinal()],
                        names_by_ordinal[&usage.target().ordinal()],
                    )
                })
                .collect::<Vec<_>>();
            use_edges.sort_unstable();
            assert_eq!(
                use_edges,
                vec![("left", "wrap"), ("right", "wrap"), ("wrap", "id")]
            );
            let collected_uses = batch
                .definition_uses()
                .iter()
                .map(|usage| usage.occurrence().clone())
                .collect::<std::collections::HashSet<_>>();

            let session = InferenceSession::try_new(batch).unwrap();
            let mut reconstructions = reconstruction_inputs(&session);
            let solved = session.run().expect("higher-order name uses solve");
            for record in &mut reconstructions {
                record.ports = retained_function_ports(&solved, &record.recipe.occurrence);
                check_reconstruction(&solved, record);
                let mut wrong_construction = record.clone();
                wrong_construction.body_row = record.construction_row;
                assert!(!reconstruction_matches(&solved, &wrong_construction));
                let other = reconstructions_other_row(&solved, record);
                let mut wrong_attachment = record.clone();
                wrong_attachment.body_row = other;
                assert!(!reconstruction_matches(&solved, &wrong_attachment));
                let mut split_coordinate = record.clone();
                split_coordinate.ports[3] = solved.store().facts().iter().find_map(|fact| {
                    let Ok(TermView::PositiveFunction { result, .. }) = solved.store().term_view(fact.lower()) else { return None };
                    (result != record.ports[3] && matches!(solved.store().term_view(result), Ok(TermView::LiveVariable(variable)) if variable.kind() == ComponentKind::Value && variable.polarity() == Polarity::Positive)).then_some(result)
                }).expect("other source Lambda supplies a distinct positive value coordinate");
                assert!(!reconstruction_matches(&solved, &split_coordinate));
            }
            // Named uses instantiate closed polarized projections. Their
            // effect leaves remain projections, not source-row identities.
            let mut fresh_coordinates = std::collections::HashSet::new();
            for route in &solved.routed_uses {
                let fact_id = route.fact.expect("structured named use has a routed fact");
                let fact = solved
                    .store()
                    .facts()
                    .iter()
                    .find(|fact| fact.id() == fact_id)
                    .unwrap();
                let TermView::PositiveFunction {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } = solved.store().term_view(fact.lower()).unwrap()
                else {
                    panic!("named route retains instantiated Function");
                };
                assert!(matches!(
                    solved.store().term_view(argument_effect),
                    Ok(TermView::Leaf(Leaf::EmptyEffectNegative))
                ));
                assert!(matches!(
                    solved.store().term_view(result_effect),
                    Ok(TermView::Leaf(Leaf::EffectBottomPositive))
                ));
                let (argument, result) = match solved.store().term_view(result).unwrap() {
                    TermView::PositiveFunction {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => {
                        assert!(matches!(
                            solved.store().term_view(argument_effect),
                            Ok(TermView::Leaf(Leaf::EmptyEffectNegative))
                        ));
                        assert!(matches!(
                            solved.store().term_view(result_effect),
                            Ok(TermView::Leaf(Leaf::EffectBottomPositive))
                        ));
                        (argument, result)
                    }
                    _ => (argument, result),
                };
                let TermView::LiveVariable(argument) = solved.store().term_view(argument).unwrap()
                else {
                    panic!("fresh argument")
                };
                let TermView::LiveVariable(result) = solved.store().term_view(result).unwrap()
                else {
                    panic!("fresh result")
                };
                assert_eq!(argument.polarity(), Polarity::Negative);
                assert_eq!(result.polarity(), Polarity::Positive);
                assert_eq!(argument.ordinal(), result.ordinal());
                assert!(
                    fresh_coordinates.insert(argument.ordinal()),
                    "separate closed uses get fresh coordinates"
                );
            }
            assert_eq!(fresh_coordinates.len(), 3);
            assert!(solved.errors().is_empty(), "{source}");
            assert_diagonal_function_scheme(&solved, id_index, false);
            assert_diagonal_function_scheme(&solved, wrap_index, true);
            for alias in ["left", "right"] {
                let (alias_index, _) = binding_named(&hir, alias);
                assert_diagonal_function_scheme(&solved, alias_index, true);
            }

            let routed = solved
                .routed_uses
                .iter()
                .map(|usage| usage.use_id.occurrence().clone())
                .collect::<std::collections::HashSet<_>>();
            assert_eq!(solved.routed_uses.len(), 3, "no source use is routed twice");
            assert_eq!(routed, collected_uses);
            assert_eq!(routed.len(), 3, "every returned-root use routes once");
            assert_eq!(
                solved.counters().instantiation_fresh_value_variables(),
                3,
                "each quantified returned Function use gets a separate fresh substitution"
            );
            case_count += 1;
        }
    }
    assert_eq!(case_count, 96);
}

#[test]
fn returned_function_invocation_keeps_outer_and_future_source_events_separate() {
    let source = "my id x = x\nmy wrap ignored = id\nmy left = wrap\nmy right = wrap";
    let hir = module(source, "research-returned-function-future-call.yu");
    assert!(hir.errors().is_empty());
    let (_, id_binding) = binding_named(&hir, "id");
    let (_, wrapper) = binding_named(&hir, "wrap");
    let (_, left) = binding_named(&hir, "left");
    let (_, right) = binding_named(&hir, "right");
    for alias in [left, right] {
        let ResolvedExpr::Name {
            resolution: NameResolution::Resolved(target),
            ..
        } = alias.value()
        else {
            panic!("the alias resolves to the wrapper");
        };
        assert_eq!(target, wrapper.id());
    }
    let ResolvedExpr::Lambda {
        parameter: wrapper_parameter,
        body: wrapper_body,
        ..
    } = wrapper.value()
    else {
        panic!("wrap is a source Lambda");
    };
    let ResolvedExpr::Name {
        occurrence: wrapper_body_occurrence,
        ..
    } = wrapper_body.as_ref()
    else {
        panic!("wrap's body is the returned source name");
    };
    let ResolvedExpr::Lambda { parameter, .. } = id_binding.value() else {
        panic!("id is a source Lambda");
    };
    let (body, body_occurrence) = source_body(id_binding.value(), parameter);
    assert_eq!(body, BodyProgram::Identity);
    let ResolvedExpr::Lambda {
        occurrence: lambda_occurrence,
        ..
    } = id_binding.value()
    else {
        unreachable!()
    };
    let session = InferenceSession::try_new(collect(hir.clone())).unwrap();
    let mut records = reconstruction_inputs(&session);
    let solved = session.run().unwrap();
    let mut reconstruction = records.remove(0);
    reconstruction.ports = retained_function_ports(&solved, &reconstruction.recipe.occurrence);
    check_reconstruction(&solved, &reconstruction);
    let id_artifact = SourceArtifact {
        body,
        lambda_occurrence: lambda_occurrence.clone(),
        body_occurrence,
        binder: parameter.clone(),
        reconstruction,
    };

    let outer_histories = generated_handled_histories(2, 10);
    let future_histories = generated_handled_histories(1, 100);
    assert_eq!(outer_histories.len(), 73);
    assert_eq!(future_histories.len(), 9);
    let mut composed_histories = 0;
    for (alias_name, alias) in [("left", left), ("right", right)] {
        assert_eq!(alias.id().spelling(), alias_name);
        for (outer_requests, outer_decisions) in &outer_histories {
            let returned = run_source_wrapper_to_returned_callable(
                wrapper,
                id_binding,
                outer_requests,
                outer_decisions,
            );
            assert_eq!(returned.source_root, *id_binding.id());
            let mut expected_outer_state = 0;
            let mut expected_outer_trace =
                vec![WrapperReturnStep::Receipt, WrapperReturnStep::ForceArgument];
            for (request, decision) in outer_requests.iter().zip(outer_decisions) {
                let RequestDecision::Handle { state_after, .. } = decision else {
                    unreachable!("generator emits handled outer histories")
                };
                expected_outer_trace.push(WrapperReturnStep::Request {
                    request: request.clone(),
                    state: expected_outer_state,
                });
                expected_outer_trace.push(WrapperReturnStep::Resume {
                    origin: request.origin,
                    continuation: request.continuation,
                    state_before: expected_outer_state,
                    state_after: *state_after,
                });
                expected_outer_state = *state_after;
            }
            expected_outer_trace.push(WrapperReturnStep::EnterBody {
                occurrence: wrapper_body_occurrence.clone(),
                binder: wrapper_parameter.clone(),
            });
            expected_outer_trace.push(WrapperReturnStep::ReturnCallable {
                source_root: id_binding.id().clone(),
            });
            assert_eq!(returned.trace, expected_outer_trace);
            assert_eq!(returned.final_state, expected_outer_state);
            let outer_trace = returned.trace.clone();

            for (future_requests, future_decisions) in &future_histories {
                let outer_origins = outer_requests
                    .iter()
                    .map(|request| request.origin)
                    .collect::<std::collections::HashSet<_>>();
                let outer_continuations = outer_requests
                    .iter()
                    .map(|request| request.continuation)
                    .collect::<std::collections::HashSet<_>>();
                assert!(
                    future_requests
                        .iter()
                        .all(|request| !outer_origins.contains(&request.origin)
                            && !outer_continuations.contains(&request.continuation))
                );
                let InvocationResult::Returned {
                    trace: future_trace,
                    actual_role,
                    callback_view,
                    result_value,
                    final_state,
                } = invoke_pure_value_through_handler_view_from_state(
                    &id_artifact,
                    returned.final_state,
                    future_requests.clone(),
                    future_decisions.clone(),
                )
                else {
                    panic!("all generated future histories are handled");
                };
                assert_eq!(actual_role, ReceiverRole::Pure);
                assert_eq!(callback_view, ReceiverRole::HandlerView);
                let mut expected_future_state = expected_outer_state;
                let mut expected_argument_value = 0;
                let mut expected_future_trace =
                    vec![InvocationStep::Receipt, InvocationStep::ForceArgument];
                for (request, decision) in future_requests.iter().zip(future_decisions) {
                    let RequestDecision::Handle { value, state_after } = decision else {
                        unreachable!("generator emits handled future histories")
                    };
                    expected_future_trace.push(InvocationStep::Request {
                        request: request.clone(),
                        state: expected_future_state,
                    });
                    expected_future_trace.push(InvocationStep::Resume {
                        origin: request.origin,
                        continuation: request.continuation,
                        value_type: "int",
                        state_before: expected_future_state,
                        state_after: *state_after,
                    });
                    expected_future_state = *state_after;
                    expected_argument_value = *value;
                }
                expected_future_trace.push(InvocationStep::EnterBody {
                    occurrence: id_artifact.body_occurrence.clone(),
                    binder: id_artifact.binder.clone(),
                });
                expected_future_trace.push(InvocationStep::Return { value_type: "int" });
                assert_eq!(future_trace, expected_future_trace);
                assert_eq!(result_value, expected_argument_value);
                assert_eq!(final_state, expected_future_state);
                assert_eq!(
                    returned.trace, outer_trace,
                    "future use cannot replay outer entry"
                );
                composed_histories += 1;
            }
        }
    }
    assert_eq!(composed_histories, 1_314);
}
