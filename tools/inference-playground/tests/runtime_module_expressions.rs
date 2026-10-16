use std::sync::Arc;
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{
    FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports, SourceRootId,
    lower_module,
};
use yu_playground::runtime::{
    ExecutionRoot, Machine, RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeUnavailable,
    RuntimeValueKind,
};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const IO: &str = "act io:\n    our tick: int -> int\n    our other: int -> int\n";

fn hir(source: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    Arc::new(
        lower_module(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "runtime-module-expressions",
                "test.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    )
}
fn program(source: &str) -> Arc<RuntimeProgram> {
    RuntimeProgram::from_hir(hir(source), RuntimeEvidence::default()).unwrap()
}
// Existing opt-in carrier route for Act declarations and annotated top-level headers.
fn opt_in_program(source: &str) -> Arc<RuntimeProgram> {
    let source: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new(
            "runtime-module-expressions",
            "test.yu",
        ))),
        &parsed,
        SemanticImports::empty(),
    )
    .unwrap();
    RuntimeProgram::from_hir(Arc::new(hir), RuntimeEvidence::default()).unwrap()
}
fn machine(source: &str) -> Machine {
    let program = program(source);
    program
        .start(
            program.definition_named("main").unwrap(),
            &program.execution_roots().unwrap(),
        )
        .unwrap()
}
fn opt_in_machine(source: &str) -> Machine {
    let program = opt_in_program(source);
    program
        .start(
            program.definition_named("main").unwrap(),
            &program.execution_roots().unwrap(),
        )
        .unwrap()
}
fn opt_in_assert_selected(source: &str, expected: &str) {
    let mut machine = opt_in_machine(source);
    let outcome = machine.run(30_000);
    let RuntimeOutcome::Completed(value) = outcome else {
        panic!("expected selected definition, got {outcome:?}");
    };
    let RuntimeValueKind::Integer(value) = &machine.value(value).unwrap().kind else {
        panic!("expected integer selection");
    };
    assert_eq!(value.as_ref(), expected);
}
fn assert_selected(source: &str, expected: &str) {
    let mut machine = machine(source);
    let outcome = machine.run(30_000);
    let RuntimeOutcome::Completed(value) = outcome else {
        panic!("expected selected definition, got {outcome:?}");
    };
    let RuntimeValueKind::Integer(value) = &machine.value(value).unwrap().kind else {
        panic!("expected integer selection");
    };
    assert_eq!(value.as_ref(), expected);
}

#[test]
fn mixed_plan_uses_original_item_order_and_every_expression_identity() {
    let hir = hir(
        "my first = { my value = 1; value }; first; 99; my later = { my value = 2; value }; later; my main = 7",
    );
    let program = RuntimeProgram::from_hir(hir.clone(), RuntimeEvidence::default()).unwrap();
    let roots = program.execution_roots().unwrap();
    let mut roots = roots.iter();
    for item in hir.items() {
        match item {
            HirItem::Binding(binding) if binding.name().spelling() != "main" => {
                assert!(
                    matches!(roots.next(), Some(ExecutionRoot::Definition(id)) if id == binding.id())
                );
            }
            HirItem::Expression(expression) => {
                assert!(matches!(roots.next(), Some(ExecutionRoot::Expression(root))
                    if Some(root.source_root()) == hir.expression_root(expression.occurrence()).unwrap()));
            }
            _ => {}
        }
    }
    assert!(roots.next().is_none());
}

#[test]
fn forward_name_demand_and_discarded_values_keep_selected_definition() {
    assert_selected(
        "later; 99; my later = { my value = 11; value }; later; my main = 7",
        "7",
    );
    assert_selected("99; my main = 7; 23", "7");
    assert_selected("my main = 7; main", "7");
}

#[test]
fn polymorphic_expression_results_are_discarded_before_selected_definition() {
    assert_selected(
        r"my id x = x; id 1; id (\x -> x); my main = 7",
        "7",
    );
}

#[test]
fn forward_alias_expression_calls_discard_results_before_selection() {
    assert_selected(
        r"alias 1; alias (\x -> x); my alias = id; my id x = x; my main = 7",
        "7",
    );
}

#[test]
fn a_returned_expression_closure_is_discarded_without_invocation() {
    opt_in_assert_selected(&format!("{IO}\\ignored -> io::tick 99; my main = 7"), "7");
}

#[test]
fn primitive_direct_expression_handler_has_module_run_permission() {
    opt_in_assert_selected(
        &format!("{IO}catch io::tick 99 {{ io::tick(p), _ -> p }}; my main = 7"),
        "7",
    );
    opt_in_assert_selected(
        &format!(
            "{IO}{{ my value = 99; catch io::tick value {{ io::tick(p), _ -> p }} }}; my main = 7"
        ),
        "7",
    );
}

#[test]
fn every_expression_lambda_and_arm_participates_in_the_closed_certificate() {
    for suffix in [
        "\\x -> x",
        "{ my unused x = x; 99 }",
        "catch 99 { value -> value, _ -> { my unused x = x; 99 } }",
    ] {
        let mut machine = opt_in_machine(&format!(
            "{IO}catch io::tick 11 {{ io::tick(p), _ -> p }}; {suffix}; my main = 7"
        ));
        assert!(matches!(
            machine.run(30_000),
            RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(_))
        ));
    }
}

#[test]
fn expression_owned_local_parameter_and_catch_schema_follow_real_invocation() {
    opt_in_assert_selected(
        &format!(
            "{IO}{{ my relay (thunk:[io] int) = catch thunk {{ io::tick(p), _ -> p }}; relay (io::tick 99) }}; my main = 7"
        ),
        "7",
    );
    // The nested helper cannot use the containing relay's receiving permission.
    let mut machine = opt_in_machine(&format!(
        "{IO}{{ my relay (thunk:[io] int) = {{ my helper ignored = catch thunk {{ io::tick(p), _ -> p }}; helper() }}; relay (io::tick 99) }}; my main = 7"
    ));
    assert!(matches!(
        machine.run(30_000),
        RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(_))
    ));
}

#[test]
fn repeated_permitted_resume_returns_before_the_next_expression_root() {
    let program = opt_in_program(&format!(
        "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> {{ my first = k 11; k 23 }} }}; relay (io::tick 7); relay (io::tick 9); my main = 5"
    ));
    let mut machine = program
        .start(
            program.definition_named("main").unwrap(),
            &program.execution_roots().unwrap(),
        )
        .unwrap();
    let RuntimeOutcome::Completed(value) = machine.run(30_000) else {
        panic!("expected selected definition");
    };
    let RuntimeValueKind::Integer(value) = &machine.value(value).unwrap().kind else {
        panic!("expected integer selection");
    };
    assert_eq!(value.as_ref(), "5");
    let program = opt_in_program(&format!(
        "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> {{ my first = k 11; my second = k 23; io::other second }} }}; relay (io::tick 7); io::other 99; my main = 5"
    ));
    let mut machine = program
        .start(
            program.definition_named("main").unwrap(),
            &program.execution_roots().unwrap(),
        )
        .unwrap();
    let RuntimeOutcome::UnhandledRequest {
        payload, source, ..
    } = machine.run(30_000)
    else {
        panic!("the first expression's arm must run before the next root");
    };
    let RuntimeValueKind::Integer(value) = &machine.value(payload).unwrap().kind else {
        panic!("integer payload");
    };
    assert_eq!(value.as_ref(), "23");
    assert!(matches!(source.source_root, SourceRootId::Definition(_)));
}

#[test]
fn budgeted_resume_preserves_module_root_cursor_and_result() {
    let source = format!(
        "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> {{ my first = k 11; k 23 }} }}; relay (io::tick 7); relay (io::tick 9); my main = 5"
    );

    let mut uninterrupted = opt_in_machine(&source);
    let outcome = uninterrupted.run(30_000);
    let RuntimeOutcome::Completed(expected) = outcome else {
        panic!("uninterrupted execution must complete, got {outcome:?}");
    };
    let uninterrupted_steps = uninterrupted.steps();
    assert!(uninterrupted_steps > 0);
    let RuntimeValueKind::Integer(expected_value) = &uninterrupted.value(expected).unwrap().kind
    else {
        panic!("uninterrupted result must be an integer");
    };
    assert_eq!(expected_value.as_ref(), "5");
    assert!(matches!(
        uninterrupted.run(0),
        RuntimeOutcome::Completed(value) if value == expected
    ));
    assert_eq!(uninterrupted.steps(), uninterrupted_steps);
    assert!(matches!(
        uninterrupted.run(1),
        RuntimeOutcome::Completed(value) if value == expected
    ));
    assert_eq!(uninterrupted.steps(), uninterrupted_steps);

    for chunk in [1, 2, 7] {
        let mut resumed = opt_in_machine(&source);
        assert_eq!(resumed.steps(), 0);
        assert!(matches!(
            resumed.run(0),
            RuntimeOutcome::ResourceExhausted { steps: 0 }
        ));
        assert_eq!(resumed.steps(), 0);

        let mut completed = None;
        for _ in 0..30_000 {
            let before = resumed.steps();
            assert!(before + chunk <= 30_000, "chunked execution exceeded its step cap");
            match resumed.run(chunk) {
                RuntimeOutcome::ResourceExhausted { steps } => {
                    assert_eq!(steps, resumed.steps());
                    assert_eq!(steps, before + chunk);

                    let paused_steps = resumed.steps();
                    assert!(matches!(
                        resumed.run(0),
                        RuntimeOutcome::ResourceExhausted { steps } if steps == paused_steps
                    ));
                    assert_eq!(resumed.steps(), paused_steps);
                }
                RuntimeOutcome::Completed(value) => {
                    completed = Some(value);
                    break;
                }
                outcome => panic!("chunked execution escaped with {outcome:?}"),
            }
        }

        let actual = completed.expect("chunked execution completes within 30,000 steps");
        let actual_steps = resumed.steps();
        assert_eq!(actual_steps, uninterrupted_steps);
        let RuntimeValueKind::Integer(actual_value) = &resumed.value(actual).unwrap().kind else {
            panic!("chunked result must be an integer");
        };
        assert_eq!(actual_value.as_ref(), "5");
        assert!(matches!(
            resumed.run(0),
            RuntimeOutcome::Completed(value) if value == actual
        ));
        assert_eq!(resumed.steps(), actual_steps);
        assert!(matches!(
            resumed.run(1),
            RuntimeOutcome::Completed(value) if value == actual
        ));
        assert_eq!(resumed.steps(), actual_steps);
    }
}

#[test]
fn expression_request_retains_original_provenance_and_pending_suffix() {
    let mut machine = opt_in_machine(&format!("{IO}io::tick 99; my main = 7"));
    let RuntimeOutcome::UnhandledRequest {
        source,
        continuation,
        ..
    } = machine.run(30_000)
    else {
        panic!("expected the root request before selected-definition completion");
    };
    assert!(matches!(source.source_root, SourceRootId::Expression(_)));
    assert!(machine.continuation_depth(continuation).unwrap() > 0);
}

#[test]
fn foreign_expression_plan_cannot_enter_another_artifact() {
    let first = program("99; my main = 7");
    let foreign = program("99; my main = 7");
    assert!(matches!(
        first.start(
            first.definition_named("main").unwrap(),
            &foreign.execution_roots().unwrap()
        ),
        Err(RuntimeUnavailable::InvalidSourceReference)
    ));
    let mut duplicate = first.execution_roots().unwrap();
    duplicate.push(duplicate[0].clone());
    assert!(matches!(
        first.start(first.definition_named("main").unwrap(), &duplicate),
        Err(RuntimeUnavailable::ModuleInitializationOrder)
    ));
}

#[test]
fn definition_root_validation_preserves_program_ownership() {
    let source = "my first = { my value = 11; value }; 99; my main = 7";
    let local = program(source);
    let source_text: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        source_text.clone(),
        Arc::new(scan_header(source_text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let foreign_hir = lower_module(
        ModuleIdentity::source_root(FileId::new(FileKey::new(
            "runtime-module-expressions-foreign",
            "test.yu",
        ))),
        &parsed,
        SemanticImports::empty(),
    )
    .unwrap();
    let foreign = RuntimeProgram::from_hir(Arc::new(foreign_hir), RuntimeEvidence::default())
        .unwrap();
    assert_ne!(
        local.definition_named("main").unwrap(),
        foreign.definition_named("main").unwrap()
    );
    assert_ne!(
        local.definition_named("first").unwrap(),
        foreign.definition_named("first").unwrap()
    );
    let roots = local.execution_roots().unwrap();

    assert_eq!(roots.len(), 2);
    assert!(matches!(
        &roots[0],
        ExecutionRoot::Definition(id) if id == local.definition_named("first").unwrap()
    ));
    assert!(matches!(&roots[1], ExecutionRoot::Expression(_)));

    match local.start(foreign.definition_named("main").unwrap(), &roots) {
        Err(RuntimeUnavailable::MissingDefinition) => {}
        Err(error) => panic!("unexpected foreign selected-definition error: {error:?}"),
        Ok(_) => panic!("foreign selected definition was unexpectedly accepted"),
    }

    let mut foreign_first = roots.clone();
    foreign_first[0] = ExecutionRoot::Definition(foreign.definition_named("first").unwrap().clone());
    match local.start(local.definition_named("main").unwrap(), &foreign_first) {
        Err(RuntimeUnavailable::MissingDefinition) => {}
        Err(error) => panic!("unexpected foreign scheduled-definition error: {error:?}"),
        Ok(_) => panic!("foreign scheduled definition was unexpectedly accepted"),
    }

    let mut duplicate_first = roots.clone();
    duplicate_first.push(ExecutionRoot::Definition(
        local.definition_named("first").unwrap().clone(),
    ));
    assert!(matches!(
        local.start(local.definition_named("main").unwrap(), &duplicate_first),
        Err(RuntimeUnavailable::ModuleInitializationOrder)
    ));

    let mut machine = local
        .start(local.definition_named("main").unwrap(), &roots)
        .unwrap();
    let RuntimeOutcome::Completed(value) = machine.run(30_000) else {
        panic!("expected selected definition to complete");
    };
    let RuntimeValueKind::Integer(value) = &machine.value(value).unwrap().kind else {
        panic!("expected integer selection");
    };
    assert_eq!(value.as_ref(), "7");
}

#[test]
fn unavailable_or_recovered_expression_source_is_never_skipped() {
    for source in ["(1, 2); my main = 7", "f(@missing); my main = 7"] {
        assert!(matches!(
            RuntimeProgram::from_hir(hir(source), RuntimeEvidence::default()),
            Err(RuntimeUnavailable::MissingSource)
        ));
    }
    let error = yu_playground::execute(
        "@; my main = 7",
        "runtime-module-expressions.yu",
        "main",
        30_000,
        false,
    )
    .unwrap_err();
    assert!(error.starts_with("syntax diagnostics:\n"));
}
