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
    advance_requests(
        vec![InvocationStep::Receipt, InvocationStep::ForceArgument],
        0,
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
    let artifact = inspect_artifact("my id x = x", "research-id-consumer.yu");
    let InvocationResult::Returned {
        trace: callback_trace,
        result_value,
        final_state,
        actual_role,
        callback_view,
    } = invoke_pure_value_through_handler_view(
        &artifact,
        vec![Request {
            operation: "Read",
            origin: 13,
            continuation: 17,
        }],
        vec![RequestDecision::Handle {
            value: 7,
            state_after: 21,
        }],
    )
    else {
        panic!("the handled Force request returns before the consumer");
    };
    assert_eq!(result_value, 7);
    assert_eq!(final_state, 21);

    let request = Request {
        operation: "Publish",
        origin: 31,
        continuation: 47,
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

    let ResultConsumerOutcome::Returned {
        callback_trace: resumed_callback,
        consumer_trace,
        callback_result,
        final_state: consumer_final_state,
        actual_role,
        callback_view,
    } = resume_designated_result_consumer(
        suspended,
        RequestDecision::Handle {
            value: 1,
            state_after: 22,
        },
    )
    else {
        panic!("resuming the consumer request returns from the consumer");
    };
    assert_eq!(resumed_callback, callback_trace);
    assert_eq!(callback_result, result_value);
    assert_eq!(consumer_final_state, 22);
    assert_eq!(actual_role, ReceiverRole::Pure);
    assert_eq!(callback_view, ReceiverRole::HandlerView);
    assert_eq!(
        consumer_trace,
        vec![
            ResultConsumerStep::Request {
                request: request.clone(),
                state: 21,
            },
            ResultConsumerStep::Resume {
                origin: request.origin,
                continuation: request.continuation,
                state_before: 21,
                state_after: 22,
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
}
