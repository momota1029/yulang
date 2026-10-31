# R4 independent review — EFFECT-PERMISSION-NATIVE-DECODE/20261029-r4

## Verdict

**BLOCKING for proof acceptance; preserve as incomplete research construction.**

## Blocking finding

`notes/theory/lean/YulangClosure/FormalPermissionAuthenticatedNativeDecode.lean:41,64` places declaration documentation comments immediately before `mutual` blocks. Lean 4.35.0 rejects both (`42:81`, `66:82`, `unexpected token 'mutual'`). The selected module build exits 1, so none of the 13 requested theorem types or transitive axiom sets was audited. This fails R4's fixed outcome and the Lean proof-closure contract. Closure requires a newly authorized packet, corrected comment placement, frozen bytes, and a successful exact theorem/type/axiom audit. No retry or edit occurred during review.

## Construction review

No additional concrete correctness defect was found in the uncompiled construction:

- `encodeSource` explicitly projects the observed Int/Unit, Function, Tuple and argument/result row structure. The exact nine-node source tree and four chronological ports match the pinned source and R3 observation.
- Native constructor order is argument value, result value, argument port, result port. Ordered tuple recursion adds no effect allocations for these atomic leaves. The decoder recurrence computes births `n,n+1,n+2,n+3`. The conditional arithmetic, together with the complete recurrence and observed first origin 22, supports slice base 21; it does not establish the solver's global initial state.
- Tags and all State fields are universally quantified. This bounded slice reads only `nextEffect`; retained entries and expected observations do not depend on tags or the other seven State coordinates. Shapes may vary with tags.
- Context, rows, paths, distinct operands, original/canonical rows 22/24, capture 4, root 0, negative nodes 17/14, and returned ports agree with the frozen raw observation.
- `extracted_instance` applies the unchanged parent-facing theorem to both paths using the same computed dependent output. No native-State equality is assumed.

The reviewer independently verified all 45 manifest inputs, all 12 copied project inputs, target/scratch equality, submitted artifact and handoff hashes, and all four audit receipt hashes. The dependency-cone scan found no proof holes, project axioms, or checker bypasses. That scan does not substitute for the unavailable axiom audit.

## Status and gates

The handoff's earlier `audit NOT RUN` stop description was superseded by its final revision-2 failed-audit receipt. The exact single invocation exited 1; there was no retry. All 13 declarations remain **UNCHECKED**.

The original parent, source/native authenticity, effect hygiene, consumer residual, unequal transport, soundness, principality, termination, and production gates remain **OPEN**. This review does not close any of them.
