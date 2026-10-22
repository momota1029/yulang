# R326 — unchanged Console and whole-module execution

## Parent

The unchanged-samples goal remains broader than the Types and Console pair. R149 fixes the exact 92-byte Console source and its two captured write events, in source order:

```yu
// println is a library effect handled by the host.

println "hello from Yulang"
say: 1 + 2
```

Expected CLI output is `hello from Yulang\n3\n`. R325 now runs the exact Types sample and captures `(42, Yulang)\n` through an exact source-operation import identity and the saved continuation template.

## R326 claim

The runtime must run the original mixed source schedule without requiring an arbitrarily selected definition. It must visit every expression/computation root in source order, retain lazy value materialization and initialization behavior, and complete only after the schedule has drained. The Console source has no injected `main` definition, so selected-definition execution alone cannot meet this behavior.

Host operation handling reuses R325's exact `SourceOperationPathImport` capability, the resolved export identity, and the checked `str -> ()` signature. Runtime dispatch compares `SourceOperationId`, validates each actual string payload, captures one event, supplies unit, and resumes the corresponding saved continuation once. The CLI concatenates the two payloads in source order. A source/native proof, full `out::write` adequacy proof, solver soundness, principality, and other Yulang2 samples remain open.

## Evidence and next premises

The exact source hash is `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`. Completion requires ordinary candidate inference and actual CLI execution with the original bytes, plus preservation tests for selected-definition mode. These executable checks establish only the bounded implementation path. General schedule coverage, source correspondence, and the parent proof need separate evidence and review.

Contravariant `[io]` annotations continue to mean `[io,'e]`; `[state]` is permitted. No implementation may tighten that rule to make the samples pass.

## Candidate inference boundary (2026-10-22)

The provider projection now follows imported names in authentic source expression roots. A selected source member's short `out::write` path can resolve either through its exact imported family export or through the same file's exact local Act declaration. Both routes retain the family declaration and operation identity. The focused Console test lowers selected `println` while omitting unrelated Act/member carrier work.

Selected source roots can mention a name declared locally in their file. Implicit-prelude lookup now skips those local declarations, so an unrelated recovered export with the same spelling cannot make a local source root unavailable. The unchanged Console projection now crosses this import boundary and operation preflight; its exact CLI proceeds to `DeferredSelectionUnavailable` in FieldTail selection.

Normal candidate preflight reaches `console.say` and retains its `where 'a: Display` obligation with the authenticated role identity. A temporary environment-only bypass used for diagnosis is removed. The exact unchanged Console command still reaches `DeferredSelectionUnavailable` in FieldTail dispatch. The source operator readback distinguishes three FreshUses of the same imported `+` provider: the top-level `1 + 2` receiver has shape `Int`, matches the exact `int: Add` implementation, and requests that implementation member's source; two nested `+` uses owned by generic `console.say` and `console.println` have no receiver bounds at definition scope. Nested operator FieldTail templates are now attached to their enclosing definition graph and activated through that definition's FreshUse. The remaining `say` use has a `show` receiver linked to its authenticated `Display` subject by an upper bound, but no positive shape reaches the receiver; the top-level argument's `Int` shape has not been transported into that fresh row. The next solver step is to trace the concrete Apply argument through the instantiated function input and prove the variance-correct row flow without closing an open effect row. Console output and the source/native theorem remain open.
