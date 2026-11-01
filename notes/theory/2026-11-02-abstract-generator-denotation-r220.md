# R220 abstract literal fragment and source boundary

## Result

`YulangClosure.AbstractGeneratorDenotationR220` gives a source-independent
structural fragment for all eight raw literal constructors. Its Value store has
both `atom(code l) ≤ var(q)` and `var(q) ≤ atom(code l)`; its Effect store has
`var(e) ≤ bottom`. For every assignment satisfying this fragment in the pinned
regular graph model, the designated Value reference reads the exact atom shape
and code, and the designated Effect reference reads `bottom`. The theorem does
not assert reference-index equality.

The module compiled with Lean 4.35.0. Its six declarations passed the project
checker. Each printed axiom audit is `[propext]`. Full types, command receipts,
and direct artifact hashes are recorded in the [R220 outcome](../../tasks/agent-loop/history/20261102-abstract-generator-denotation-r220-outcome.md).
An independent compiler-referee review passed the structural leaf with no
blocking, major, or minor findings; it did not review or close the original
source parent.

## Exact source cut

The structural result does not recover the adopted literal row. Its `literalCode`
retains only the constructor tag; it does not decode the original payload to
`PaperTypes.Value.literal` or establish the descriptor `Value(τ(l))`.
`OriginalSourceGeneration.sourceRules` emits `literalDeclaration` at the
original site. `SourceAssignment.row` reads descriptor, value and root at
`⟨site, finalRoot⟩` and carries its event. The source syntax separately names
`synthesis`, `finalRoot` and `writtenTarget`; the annotated rule connects
synthesis to writtenTarget. No existing equation connects the structural
references to the source descriptor/value/root/event fields or to the original
`(q,r,e₀,ξ,ω)`.

`LiteralAtom` consumes a supplied declaration relation plus ground descriptor
and row facts. It does not derive them from `StoreSatisfied`. The adopted L1 rule
also requires the same raw payload, original root/event/scope/shared witness,
and pure `Comp(empty, τ(l))` Return. Intrinsic empty Effect does not discharge
contextual permission, inflow, residual, Call, or future obligations.

Therefore the unchanged `SourceProblem.InferenceSoundness` literal premise has
not been removed. Parent-premise delta remains **0**; roots **0/4**, packages
**0/5**, and Effect-hygiene theorem delta **0**. This is an exact missing model
equation, not a source-qualified counterexample or a refutation of L1.

## Scope

No Rust change is admitted: R219's reviewed `NO_SAFE_CODE_SLICE` remains the
current implementation result. R220 changes no source semantics and does not
prove principality, termination, full-language soundness, source coverage,
contextual-effect hygiene, or Rust/native correspondence. The next useful work
must construct and prove the original endpoint/readout connection before any
literal parent application can count.
