use yu_playground::infer;

#[test]
fn inline_identity_definition_and_call_render_retained_graphs() {
    let output = infer(
        "my identity = \\x -> x; my answer = identity 1",
        "inline-identity.yu",
    )
    .unwrap();
    assert!(output.contains("definition identity:"));
    assert!(output.contains("definition answer:"));
    assert!(output.contains("Function(argument="));
    assert!(output.contains(" <: "));
    assert!(output.contains("no principal-type"));
}

#[test]
fn direct_inline_application_renders_answer_and_constraints() {
    let output = infer("my answer = (\\x -> x) 1", "inline-direct.yu").unwrap();
    assert!(output.contains("definition answer:"));
    assert!(output.contains(" <: "));
    assert!(output.contains("no principal-type"));
}

#[test]
fn inline_local_initializer_reaches_existing_call_inference() {
    let output = infer(
        "my value = { my identity = \\x -> x; identity 1 }",
        "inline-local.yu",
    )
    .unwrap();
    assert!(output.contains("definition value:"));
    assert!(output.contains(" <: "));
    assert!(output.contains("no principal-type"));
}

#[test]
fn inline_provider_matches_known_function_slot() {
    let output = infer(
        "my apply (f:int -> int) = f 1; my answer = apply (\\x -> x)",
        "inline-known-slot.yu",
    )
    .unwrap();
    assert!(output.contains("definition apply:"));
    assert!(output.contains("definition answer:"));
    assert!(output.contains("Function(argument="));
    assert!(output.contains(" <: "));
    assert!(output.contains("no principal-type"));
}

#[test]
fn incompatible_inline_provider_withholds_graph_exports() {
    let error = infer(
        "my apply (f:int -> int) = f 1; my answer = apply (\\x -> ())",
        "inline-conflict.yu",
    )
    .unwrap_err();
    assert!(error.contains("candidate type conflicts"), "{error}");
    assert!(!error.contains("unsupported source"));
    assert!(!error.contains("definition apply:"));
    assert!(!error.contains("definition answer:"));
}
