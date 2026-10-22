# R321 — exact member-only HIR into the candidate session

## Entry evidence

R320 verified imported operator candidate dependency ordering, strict infix lowering to two curried Apply relations, per-occurrence FreshUse, and nested provider execution with dependent-first roots intentionally reversed. Focused solver tests pass; playground passes 42/42; sprint tooling and diff checks pass. The R320 bounded candidate correspondence is recorded as RESULT. This does not close the unchanged Types sample or any source/native theorem gate.

The current Types test still expects `DeferredSelectionUnavailable` at `pair.say`. Its pinned module readback sees receiver `(Int, Str)`, one exact tuple Display target, substitution `a=int, b=str`, and exact `Display` prerequisites for `int` and `str`. R314's member-only carrier now reaches candidate graph capture in the same session as that unchanged consumer FieldTail. The sample still stops before implementation selection and successful inference.

## R321 question

Can an exact source-selected role-default or implementation-member body enter the candidate session that owns the consumer's deferred FieldTail while preserving its actual source member identity, receiver/result/effect rows, and nested FieldTail obligations?

The test must use the exact pinned source projection and the unchanged Types consumer, then observe a same-session `MemberGraph`. A standalone selected-member HIR, a receiver-shape readback, or a green fixture that never links to the consumer does not answer the question.

## Construction route

1. Reproduce selected-member-only `Unsupported` at candidate entry and trace `Display.say` to its exact host operation source.
2. Parse `pub host act out` and its `write` member as source-owned declaration nodes; route `std::io::out::write` through the exact public family re-export and preserve its signature and declaration key in the selected carrier.
3. Admit only the exact `Display.say` member carrier and its exact imported operator provider roots. Retain an operator provider by exact parse-owned declaration/body keys even when its syntax-environment revision is untracked.
4. Preserve argument-bearing `our x.add y` headers as dotted method targets, visit both operands of infix source nodes, and skip an operator provider root in the generic expression loop after its graph is captured once.
5. Capture one same-session `MemberGraph` for the exact `Display.say`; verify the unchanged consumer `pair.say` remains a deferred receiver row and nested `a.show` is retained in the member graph's FreshUse layout.
6. Continue from this boundary toward ordinary Types inference and execution. Method selection, where-prerequisite discharge, generic target coverage, later-bound stability, Console, R149, source/native A/B, parent proof closure, and production remain OPEN.

## Open gates

Method selection and where-prerequisite discharge are still unimplemented. Generic target coverage, later-bound stability, Console, R149, source/native A/B, independent review, parent proof closure, and production remain OPEN. No test result in this note certifies those claims.

## Verification receipt

- `cargo test -p yu-hir --lib`: 167 passed, including the exact argument-bearing implementation method header case.
- `cargo test -p yu-playground --lib`: 42 passed. The unchanged Types case captures one exact same-session member graph, its nested `show` FieldTail FreshUse layout, and the consumer's deferred `say` receiver; Console boundary also passes.
- Focused solver tests `nested_operator_provider_rhs_uses_dependency_before_capture` and `imported_operator_expression_is_captured_before_consumer_admission`: passed with `shadow-apply-candidate` enabled.
- Full solver suite remains unresolved: default feature invocation does not compile the research-only candidate configuration; feature-enabled parallel run overflowed its stack; single-thread rerun remained at `queued_relation_equality_transport_retains_context_ancestry_and_retry` and was stopped without a final result.
- `python3 tools/agent_sprint.py check`: static check pass.
- `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`: 57 passed.
- `git diff --check`: pass.

These checks validate same-session member graph capture. They do not select an implementation, type or execute the unchanged sample successfully, discharge prerequisites, or close a proof gate.
