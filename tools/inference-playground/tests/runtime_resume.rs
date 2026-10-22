use std::sync::Arc;
use yu_hir::shadow::{SourceOperationId, lower_module_with_local_source};
use yu_hir::{
    FileId, FileKey, HirErrorAttachment, HirErrorKind, HirErrorOrigin, HirItem,
    ModuleIdentity, ResolvedExpr, SemanticImports, SourceRootId,
};
use yu_playground::runtime::{
    Machine, RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeUnavailable, RuntimeValueKind,
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const IO: &str = "act io:\n    our tick: int -> int\n    our other: int -> int\n";
fn machine(source: &str) -> (Machine, Vec<(Box<str>, SourceOperationId)>) {
    let (machine, operations, _) = machine_with_hir(source);
    (machine, operations)
}
fn machine_with_hir(
    source: &str,
) -> (
    Machine,
    Vec<(Box<str>, SourceOperationId)>,
    Arc<yu_hir::HirModule>,
) {
    let text: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        text.clone(),
        Arc::new(scan_header(text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("runtime-resume", "test.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty(), "{source}");
    let operations = hir
        .source_effect_declarations()
        .iter()
        .flat_map(|family| &family.operations)
        .map(|operation| (operation.spelling.clone(), operation.id.clone()))
        .collect();
    let program = RuntimeProgram::from_hir(hir.clone(), RuntimeEvidence::default()).unwrap();
    let roots = program.execution_roots().unwrap();
    (
        program
            .start(program.definition_named("main").unwrap(), &roots)
            .unwrap(),
        operations,
        hir,
    )
}
fn assert_integer(source: &str, expected: &str) {
    let (mut machine, _) = machine(source);
    let outcome = machine.run(30_000);
    let RuntimeOutcome::Completed(value) = outcome else {
        panic!("expected completion, got {outcome:?}");
    };
    let RuntimeValueKind::Integer(actual) = &machine.value(value).unwrap().kind else {
        panic!("expected integer");
    };
    assert_eq!(actual.as_ref(), expected);
}

#[test]
fn ordered_tuple_prefix_survives_resumes_without_replaying_prior_children() {
    let source = format!(
        "{IO}my ticked (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 10 }}\nmy other (thunk:[io] int) = catch thunk {{ io::other(p), k -> k 20 }}\nmy main = (42, ticked {{ io::tick 1 }}, other {{ io::other 2 }})"
    );
    let (mut machine, _) = machine(&source);
    let RuntimeOutcome::Completed(tuple) = machine.run(30_000) else {
        panic!("expected the ordered tuple to complete after both requests")
    };
    let RuntimeValueKind::Tuple(elements) = &machine.value(tuple).unwrap().kind else {
        panic!("expected tuple result")
    };
    let integers: Vec<_> = elements
        .iter()
        .map(|element| match &machine.value(element.value()).unwrap().kind {
            RuntimeValueKind::Integer(value) => value.as_ref(),
            other => panic!("expected integer tuple element, got {other:?}"),
        })
        .collect();
    assert_eq!(integers, ["42", "10", "20"]);
}

#[test]
fn nested_tuple_runtime_values_keep_source_element_order() {
    let (mut machine, _) = machine("my main = (1, (2, 3), 4)");
    let RuntimeOutcome::Completed(outer) = machine.run(30_000) else {
        panic!("expected nested tuple completion")
    };
    let RuntimeValueKind::Tuple(elements) = &machine.value(outer).unwrap().kind else {
        panic!("expected outer tuple")
    };
    assert_eq!(elements.len(), 3);
    let RuntimeValueKind::Integer(first) = &machine.value(elements[0].value()).unwrap().kind else {
        panic!("expected first integer")
    };
    let RuntimeValueKind::Tuple(inner) = &machine.value(elements[1].value()).unwrap().kind else {
        panic!("expected nested tuple")
    };
    let RuntimeValueKind::Integer(last) = &machine.value(elements[2].value()).unwrap().kind else {
        panic!("expected last integer")
    };
    assert_eq!(first.as_ref(), "1");
    assert_eq!(last.as_ref(), "4");
    let nested: Vec<_> = inner
        .iter()
        .map(|element| match &machine.value(element.value()).unwrap().kind {
            RuntimeValueKind::Integer(value) => value.as_ref(),
            _ => panic!("expected nested integer"),
        })
        .collect();
    assert_eq!(nested, ["2", "3"]);
}

fn operation_v1_runtime_source(outer_arm: &str, callback_operation: &str) -> String {
    format!(
        "act outer:\n    our next: () -> int\n    our other: () -> int\nact signal:\n    our ping: () -> (int -> [outer] int)\nmy relay (thunk:[signal, outer] int) = catch thunk {{ outer::next(), _ -> {outer_arm}, value -> value }}\nmy main = relay ((catch signal::ping() {{ signal::ping(), k -> {{ my response: int -> [outer] int = \\x -> outer::{callback_operation}(); my other_response: int -> [outer] int = \\x -> outer::next(); k response }}, v -> v }}) 0)"
    )
}

fn operation_v1_local_binding_source() -> String {
    operation_v1_runtime_source("42", "next")
        .replace("my main = relay ((catch signal::ping()", "my main = relay { my g = catch signal::ping()")
        .replace("}) 0)", "}; g 0 }")
}

fn assert_unchanged_operation_v1_static_receipt(source: &str, name: &str) {
    let text: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        text.clone(),
        Arc::new(scan_header(text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(name, "test.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    assert_candidate_mode_hir_error_owners(&hir, source);
    let candidate = CandidateInference::solve_operation_v1_research(hir.clone()).unwrap();
    assert!(candidate.observes_hir(&hir));
    assert!(candidate.candidate_conflicts().is_empty(), "{source}");
    let receipts: Vec<_> = candidate.operation_v1_field_bounds().collect();
    assert_eq!(receipts.len(), 1, "{source}");
    assert!(receipts[0].consumed, "{source}");
    RuntimeProgram::evidence_for_operation_v1(&hir, &candidate).unwrap();
}

fn assert_candidate_mode_hir_error_owners(hir: &yu_hir::HirModule, source: &str) {
    use std::collections::{HashMap, HashSet};

    let mut declaration_placeholders = HashMap::new();
    for declaration in hir.source_effect_declarations() {
        for id in &declaration.placeholder_errors {
            assert!(
                declaration_placeholders
                    .insert(*id, (declaration.spelling.clone(), declaration.range.clone()))
                    .is_none(),
                "duplicate declaration-owned placeholder {id:?}: {source}"
            );
        }
    }

    // Match solve_mode's local-source carrier and fallback-expression paths.
    let mut source_placeholders = HashMap::new();
    let mut fallback_apply_errors = HashMap::new();
    for item in hir.items() {
        let HirItem::Binding(binding) = item else {
            // The only fallback direct expression admitted by solve_mode is an integer.
            continue;
        };
        let owner = SourceRootId::Definition(binding.definition_root().clone());
        let local_source = hir
            .local_source_for(&owner)
            .unwrap_or_else(|error| panic!("candidate-mode source owner lookup failed: {error:?}: {source}"));
        if local_source.is_some() {
            // retain_placeholder_errors accepts only the outer Lambda chain's terminal Error.
            let mut value = binding.value();
            while let ResolvedExpr::Lambda { body, .. } = value {
                value = body;
            }
            if let ResolvedExpr::Error { errors, .. } = value {
                for id in errors.iter().copied() {
                    assert!(
                        source_placeholders
                            .insert(id, binding.id().clone())
                            .is_none(),
                        "duplicate source-owned placeholder {id:?}: {source}"
                    );
                }
            }
        } else {
            // Mirror preflight_expression's only error-bearing node: Apply.
            let mut pending = vec![binding.value()];
            while let Some(value) = pending.pop() {
                match value {
                    ResolvedExpr::Apply { callee, argument, errors, .. } => {
                        for id in errors.iter().copied() {
                            assert!(
                                fallback_apply_errors
                                    .insert(id, binding.id().clone())
                                    .is_none(),
                                "duplicate fallback Apply error {id:?}: {source}"
                            );
                        }
                        pending.push(argument);
                        pending.push(callee);
                    }
                    ResolvedExpr::Group { inner, .. } => pending.push(inner),
                    ResolvedExpr::Lambda { body, .. } => pending.push(body),
                    ResolvedExpr::Integer { .. } | ResolvedExpr::Name { .. } => {}
                    _ => panic!("fallback expression is outside solve_mode preflight: {source}"),
                }
            }
        }
    }

    assert!(
        hir.errors().len() <= 16,
        "bounded HIR owner diagnostic exceeded 16 errors: count={}, source={source}",
        hir.errors().len()
    );
    let observed = hir
        .errors()
        .iter()
        .map(|error| {
            let owner = declaration_placeholders
                .get(&error.id())
                .map(|(declaration, _)| format!("declaration:{declaration}"))
                .or_else(|| source_placeholders.get(&error.id()).map(|binding| format!("source-binding:{binding:?}")))
                .or_else(|| fallback_apply_errors.get(&error.id()).map(|binding| format!("fallback-apply:{binding:?}")))
                .unwrap_or_else(|| "UNOWNED".to_owned());
            format!(
                "id={:?} owner={} origin={:?} kind={:?} attachment={:?} range={:?}",
                error.id(),
                owner,
                error.origin(),
                error.kind(),
                error.attachment(),
                error.range()
            )
        })
        .collect::<Vec<_>>();
    eprintln!("candidate-mode HIR errors (bounded): {observed:?}");

    let expected_ids = declaration_placeholders
        .keys()
        .copied()
        .chain(source_placeholders.keys().copied())
        .chain(fallback_apply_errors.keys().copied())
        .collect::<HashSet<_>>();
    let mut observed_ids = HashSet::new();
    for error in hir.errors() {
        assert!(observed_ids.insert(error.id()), "duplicate HIR error id: {observed:?}");
        assert_eq!(error.origin(), HirErrorOrigin::Lowering, "{observed:?}");
        if let Some((declaration, range)) = declaration_placeholders.get(&error.id()) {
            assert_eq!(error.kind(), HirErrorKind::UnsupportedItem, "{observed:?}");
            assert_eq!(error.range(), range, "declaration {declaration}: {observed:?}");
            let HirErrorAttachment::DirectRootItem(ordinal) = error.attachment() else {
                panic!("declaration placeholder lacks direct-root owner: {observed:?}");
            };
            assert!(matches!(
                hir.items().get(*ordinal as usize),
                Some(HirItem::Error { errors, .. }) if errors.contains(&error.id())
            ), "declaration {declaration} placeholder is attached to another root: {observed:?}");
        } else if let Some(binding) = source_placeholders.get(&error.id()) {
            assert_eq!(error.kind(), HirErrorKind::UnsupportedExpression, "{observed:?}");
            assert_eq!(
                error.attachment(),
                &HirErrorAttachment::Value(binding.clone()),
                "source placeholder has the wrong binding owner: {observed:?}"
            );
        } else if let Some(binding) = fallback_apply_errors.get(&error.id()) {
            assert_eq!(error.kind(), HirErrorKind::UnsupportedExpression, "{observed:?}");
            assert_eq!(
                error.attachment(),
                &HirErrorAttachment::Value(binding.clone()),
                "fallback Apply error has the wrong binding owner: {observed:?}"
            );
        } else {
            panic!("unowned or candidate-mode-forbidden HIR error: {observed:?}");
        }
    }
    assert_eq!(
        observed_ids, expected_ids,
        "owner placeholders and actual HIR errors differ: {observed:?}"
    );
}

#[test]
fn operation_v1_same_hir_candidate_resumes_the_source_closure_into_live_outer_arm_42() {
    let source = operation_v1_runtime_source("42", "next");
    let receipt = yu_playground::execute_operation_v1_runtime_research(
        &source,
        "operation-v1-runtime-resume.yu",
        30_000,
    )
    .unwrap_or_else(|error| panic!("expected completed Phase-R receipt: {error}"));
    assert_eq!(receipt.result.as_ref(), "42");
    assert_eq!(
        receipt.response_definition.definition_root(),
        receipt.response_closure_source.source_root.definition_root(),
        "the selected runtime closure retains the static response definition's source root"
    );
    assert_ne!(receipt.callback_operation_use, receipt.response_closure_source.occurrence);
    assert_eq!(
        receipt.response_argument_source.occurrence,
        receipt.response_argument_read_source.occurrence
    );
}

#[test]
fn operation_v1_local_g_binding_and_exact_cell_use_are_required_for_runtime_receipt() {
    let source = operation_v1_local_binding_source();
    assert_unchanged_operation_v1_static_receipt(&source, "operation-v1-local-binding-static");
    let receipt = yu_playground::execute_operation_v1_runtime_research(
        &source,
        "operation-v1-local-binding.yu",
        30_000,
    )
    .unwrap_or_else(|error| panic!("expected local-g lineage receipt: {error}"));
    assert_eq!(receipt.result.as_ref(), "42");
    assert_eq!(
        receipt.response_argument_source.occurrence,
        receipt.response_argument_read_source.occurrence
    );

    // A balanced shadowed g reads the outer closure into a distinct sibling
    // cell. Its use must not stand in for the initializer Catch's exact binder.
    let sibling = source.replace("}; g 0 }", "}; { my g = g; g 0 } }");
    assert_unchanged_operation_v1_static_receipt(
        &sibling,
        "operation-v1-local-binding-sibling-static",
    );
    let sibling_result = yu_playground::execute_operation_v1_runtime_research(
        &sibling,
        "operation-v1-local-binding-sibling.yu",
        30_000,
    );
    assert!(
        matches!(&sibling_result, Err(error) if error.contains("runtime unavailable: InvalidSourceReference")),
        "the unchanged static receipt must pass before the exact sibling lineage gate rejects it; got {sibling_result:?}"
    );
}

#[test]
fn operation_v1_runtime_receipt_is_withheld_for_non_42_unhandled_or_exhausted_runs() {
    let wrong_result = operation_v1_runtime_source("43", "next");
    assert!(yu_playground::execute_operation_v1_runtime_research(
        &wrong_result, "operation-v1-runtime-wrong-result.yu", 30_000
    ).is_err());

    let wrong_request = operation_v1_runtime_source("42", "other");
    assert!(yu_playground::execute_operation_v1_runtime_research(
        &wrong_request, "operation-v1-runtime-wrong-request.yu", 30_000
    ).is_err());

    let exhausted = operation_v1_runtime_source("42", "next");
    assert!(yu_playground::execute_operation_v1_runtime_research(
        &exhausted, "operation-v1-runtime-exhausted.yu", 0
    ).is_err());

    let without_handler = operation_v1_runtime_source("42", "next")
        .replace(" = catch thunk { outer::next(), _ -> 42, value -> value }", " = thunk");
    assert!(yu_playground::execute_operation_v1_runtime_research(
        &without_handler, "operation-v1-runtime-no-handler.yu", 30_000
    ).is_err());
}

#[test]
fn operation_v1_same_response_closure_at_a_different_apply_cannot_mint_receipt() {
    let source = operation_v1_runtime_source("42", "next");
    let different_apply = source.replace(
        "k response }",
        "if true: { my ignored = response 0; response } else: k response }",
    );
    assert_ne!(source, different_apply);
    assert!(
        yu_playground::execute_operation_v1_runtime_research(
            &different_apply,
            "operation-v1-runtime-different-apply.yu",
            30_000,
        )
        .is_err(),
        "calling the same source closure from the handler arm's Apply cannot stand in for the exact catch-result Apply"
    );
}

#[test]
fn operation_v1_static_receipt_cannot_select_a_same_family_different_definition() {
    let source = operation_v1_runtime_source("42", "next");
    let alternative = source.replace("k response", "k other_response");
    let lower = |text: &str, name: &str| {
        let text: Arc<SourceText> = Arc::from(text);
        let parsed = parse_file(
            text.clone(),
            Arc::new(scan_header(text)),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        Arc::new(lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(name, "test.yu"))),
            &parsed,
            SemanticImports::empty(),
        ).unwrap())
    };
    let original_hir = lower(&source, "operation-v1-original");
    let candidate = CandidateInference::solve_operation_v1_research(original_hir.clone()).unwrap();
    let evidence = RuntimeProgram::evidence_for_operation_v1(&original_hir, &candidate).unwrap();
    let alternate_hir = lower(&alternative, "operation-v1-original");
    assert!(
        RuntimeProgram::from_hir(alternate_hir, evidence).is_err(),
        "the original response-definition receipt must not attach to a same-family other_response application"
    );
}

#[test]
fn raw_response_enters_the_hole_under_the_still_active_containing_owner() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 9 }}\nmy main = relay {{ my result = io::tick 7; result }}"
        ),
        "9",
    );
}

#[test]
fn reusable_raw_context_writes_its_original_pending_local_cell() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> {{ my first = k 11; k 23 }} }}\nmy main = relay {{ my result = io::tick 7; result }}"
        ),
        "23",
    );
}

#[test]
fn inner_owner_completion_runs_the_outer_effectful_suffix_without_reinstalling_selection() {
    let source = format!(
        "{IO}my inner ignored = io::tick 7\nmy outer ignored = {{ my first = inner(); io::other first }}\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 11 }}\nmy main = relay (outer())"
    );
    let (mut machine, operations) = machine(&source);
    let outcome = machine.run(30_000);
    let RuntimeOutcome::UnhandledRequest {
        operation, payload, ..
    } = outcome
    else {
        panic!("expected shallow suffix request, got {outcome:?}");
    };
    assert_eq!(
        operation,
        operations
            .iter()
            .find(|(name, _)| name.as_ref() == "other")
            .unwrap()
            .1
    );
    let RuntimeValueKind::Integer(payload) = &machine.value(payload).unwrap().kind else {
        panic!("expected integer payload");
    };
    assert_eq!(payload.as_ref(), "11");
}

#[test]
fn forwarded_handler_reentry_runs_its_normal_value_arm_before_parent_completion() {
    assert_integer(
        &format!(
            "{IO}my helper (input:[io] int) = catch input {{ io::other(p), _ -> 99, value -> 23 }}\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 11 }}\nmy main = relay (helper (io::tick 7))"
        ),
        "23",
    );
}

#[test]
fn same_raw_continuation_reuses_suffix_under_each_current_receiver() {
    let positive = "act io:\n    our tick: int -> int\n    our other: int -> bool\nmy first (thunk:[io] bool) = catch thunk { io::other(p), _ -> true }\nmy second (thunk:[io] bool) = catch thunk { io::other(p), _ -> false }\nmy relay (thunk:[io] bool) = catch thunk { io::tick(p), k -> { my before = first (k 11); if before: second (k 23) else: true } }\nmy main = relay { my result = io::tick 7; io::other result }";

    let (mut positive_machine, _) = machine(positive);
    let outcome = positive_machine.run(30_000);
    let RuntimeOutcome::Completed(value) = outcome else {
        panic!("expected completion under the second current receiver, got {outcome:?}");
    };
    assert!(matches!(
        &positive_machine.value(value).unwrap().kind,
        RuntimeValueKind::Boolean(false)
    ));

    for (variant, receiver, expected_payload) in [
        (
            positive.replacen(
                "first (thunk:[io] bool) = catch thunk { io::other(p)",
                "first (thunk:[io] bool) = catch thunk { io::tick(p)",
                1,
            ),
            "first",
            "11",
        ),
        (
            positive.replacen(
                "second (thunk:[io] bool) = catch thunk { io::other(p)",
                "second (thunk:[io] bool) = catch thunk { io::tick(p)",
                1,
            ),
            "second",
            "23",
        ),
    ] {
        let (mut variant_machine, operations) = machine(&variant);
        let outcome = variant_machine.run(30_000);
        let RuntimeOutcome::UnhandledRequest {
            operation, payload, ..
        } = outcome
        else {
            panic!("expected forwarded request under {receiver}, got {outcome:?}");
        };
        assert_eq!(
            operation,
            operations
                .iter()
                .find(|(name, _)| name.as_ref() == "other")
                .unwrap()
                .1
        );
        let RuntimeValueKind::Integer(actual) = &variant_machine.value(payload).unwrap().kind else {
            panic!("expected integer payload under {receiver}");
        };
        assert_eq!(actual.as_ref(), expected_payload);
    }
}

#[test]
fn response_expression_is_forced_once_before_entering_the_saved_context() {
    assert_integer(
        &format!(
            "{IO}my answer (pending:[io] int) = catch pending {{ io::other(p), j -> j p }}\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> answer (k (io::other 11)) }}\nmy main = relay (io::tick 7)"
        ),
        "11",
    );
}

#[test]
fn recapture_after_inner_completion_retains_the_entire_remaining_resume_context() {
    assert_integer(
        &format!(
            "{IO}my inner ignored = io::tick 7\nmy outer ignored = {{ my first = inner(); io::other first }}\nmy answer (pending:[io] int) = catch pending {{ io::other(p), j -> j 23 }}\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> answer (k 11) }}\nmy main = relay (outer())"
        ),
        "23",
    );
}

#[test]
fn fresh_owner_reentry_does_not_resurrect_an_expired_receivers_grant() {
    let source = format!(
        "{IO}my helper (input:[io] int) = catch input {{ io::other(p), _ -> 99 }}\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 11 }}\nmy main = relay (helper {{ my first = io::tick 7; io::other first }})"
    );
    let (mut machine, _) = machine(&source);
    let outcome = machine.run(30_000);
    assert!(
        matches!(
            outcome,
            RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(_))
        ),
        "{outcome:?}"
    );
}

#[test]
fn forward_initializer_request_does_not_enter_the_name_callers_handler() {
    let source = format!(
        "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k p }}\nmy main = relay later\nmy later = io::tick 7"
    );
    // This reproduces the low-level initializer boundary. It is not a valid
    // source cache/Resume witness, an initialization-order result, or A/B closure.
    let (mut machine, operations, hir) = machine_with_hir(&source);
    let outcome = machine.run(30_000);
    let RuntimeOutcome::UnhandledRequest {
        operation,
        payload,
        source: site,
        ..
    } = outcome
    else {
        panic!("expected initializer request, got {outcome:?}");
    };
    assert_eq!(
        operation,
        operations
            .iter()
            .find(|(name, _)| name.as_ref() == "tick")
            .unwrap()
            .1
    );
    let definition = hir
        .items()
        .iter()
        .find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "later" => {
                Some(binding)
            }
            _ => None,
        })
        .unwrap();
    let carrier = hir
        .local_source(definition.definition_root())
        .unwrap()
        .unwrap();
    let application = carrier.expression(carrier.body()).unwrap();
    assert_eq!(
        site.source_root.definition_root(),
        Some(definition.definition_root())
    );
    assert_eq!(site.occurrence, application.occurrence);
    assert_eq!(site.range, application.range);
    assert_eq!(
        hir.occurrence_source_key(&site.occurrence).unwrap(),
        Some(&application.source)
    );
    let RuntimeValueKind::Integer(payload) = &machine.value(payload).unwrap().kind else {
        panic!("integer payload");
    };
    assert_eq!(payload.as_ref(), "7");
}

#[test]
fn raw_response_uses_the_declared_boolean_response_type() {
    let source = "act signal:\n    our choose: () -> bool\nmy relay (thunk:[signal] int) = catch thunk { signal::choose(), k -> k true }\nmy main = relay { my choice = signal::choose(); if choice: 7 else: 9 }";
    assert_integer(source, "7");
}

#[test]
fn initializer_internal_handler_can_resume_before_publishing_its_value() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 19 }}\nmy main = {{ my value = later; value }}\nmy later = relay (io::tick 7)"
        ),
        "19",
    );
}

#[test]
fn nested_initializer_request_does_not_enter_the_outer_initializers_name_handler() {
    let source = format!(
        "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 99 }}\nmy main = relay outer\nmy outer = relay inner\nmy inner = io::tick 7"
    );
    let (mut machine, operations, hir) = machine_with_hir(&source);
    let outcome = machine.run(30_000);
    let RuntimeOutcome::UnhandledRequest {
        operation,
        payload,
        source: site,
        ..
    } = outcome
    else {
        panic!("expected inner initializer request, got {outcome:?}");
    };
    assert_eq!(
        operation,
        operations
            .iter()
            .find(|(name, _)| name.as_ref() == "tick")
            .unwrap()
            .1
    );
    let definition = hir
        .items()
        .iter()
        .find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "inner" => {
                Some(binding)
            }
            _ => None,
        })
        .unwrap();
    let carrier = hir
        .local_source(definition.definition_root())
        .unwrap()
        .unwrap();
    let application = carrier.expression(carrier.body()).unwrap();
    assert_eq!(
        site.source_root.definition_root(),
        Some(definition.definition_root())
    );
    assert_eq!(site.occurrence, application.occurrence);
    assert_eq!(site.range, application.range);
    assert_eq!(
        hir.occurrence_source_key(&site.occurrence).unwrap(),
        Some(&application.source)
    );
    let RuntimeValueKind::Integer(payload) = &machine.value(payload).unwrap().kind else {
        panic!("integer payload");
    };
    assert_eq!(payload.as_ref(), "7");
}

#[test]
fn forward_function_initialization_finishes_before_its_latent_request_uses_the_caller_handler() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 29 }}\nmy main = relay (later())\nmy later ignored = io::tick 7"
        ),
        "29",
    );
}

#[test]
fn initializer_internal_handler_can_discard_the_request_before_publication() {
    assert_integer(
        &format!(
            "{IO}my main = {{ my value = later; value }}\nmy later = catch io::tick 7 {{ io::tick(p), _ -> 17 }}"
        ),
        "17",
    );
}
