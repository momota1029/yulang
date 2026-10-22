# R315 — parser-associated multi-infix member source carrier

## Entry

R314's unchanged-sample session still ends at `DeferredSelectionUnavailable`. The ordered-pair `Display.show` source body is preserved in the pinned fmt blob as `case value: (a, b) -> "(" + a.show + ", " + b.show + ")"`. Its flat tuple case pattern already has a source carrier. Its `OperatorChain` has four infix uses, while the current local source constructor only admits one. R308 authenticates the imported `+` syntax use to the exact provider declaration/body, but it does not supply an operator candidate scheme.

The R315 implementation step retains the parser-associated operator tree and every source identity in a supported member carrier. Candidate source admission rejects `InfixOperator` today; this sprint does not change that rejection or claim that the method body is typed. R149 and all parent proof/production gates stay OPEN.

## Evidence and remaining work

The exact member body is `our value.show = case value: (a, b) -> "(" + a.show + ", " + b.show + ")"`. Its flat tuple case pattern was already supported. The former R314 attribution to that pattern was too broad and is corrected in the R314 note and contract.

`LoweringCounters` now retains the parser-associated HIR subtree for each operator-use range. `Builder::expression` retrieves the subtree by exact chain range and maps each nested binary infix application to `LocalSourceForm::InfixOperator`. It validates the exact operator-use syntax node, exact retained `HirOperator`, unique occurrence range, expected operator-use count, and ordered operands. Leaf values are reconstructed only from exact syntax kind/range matches; FieldTail retains the member token and receiver chain. Recovered, duplicate, incomplete, or mismatched trees fail closed. No operator meaning is inferred from spelling.

The regression compares the full four-application LocalSource tree with the parser-associated HIR tree, checks ordered left/right recursion and exact `HirOperator` equality, and verifies parse ownership of each local and operator source key. Checks passed:

- `cargo test -p yu-hir --lib pinned_generic_say_header_and_operator_body_form_a_source_carrier`
- `cargo test -p yu-playground --lib pinned_fmt_role_and_tuple_impl_keep_exact_module_and_parse_positions -- --nocapture`
- `cargo test -p yu-hir --lib` — 164 passed
- `cargo test -p yu-playground --lib` — 41 passed
- `cargo test -p yu-playground --lib unchanged_types_sample_reads_receiver_bounds_from_its_pinned_module_session -- --nocapture`

The unchanged Types sample still returns `DeferredSelectionUnavailable`; `Display.say` remains unsupported and was not isolated to its exact constructor by this probe. The solver candidate-source collection still rejects `LocalSourceForm::InfixOperator`. The next gate is an explicitly leased solver consumer (starting at `crates/yu-solver/src/candidate_source.rs`) that must preserve authenticated imported operator provenance. This carrier result does not establish candidate completeness, typing, selection, runtime execution, or any parent proof/production closure.
