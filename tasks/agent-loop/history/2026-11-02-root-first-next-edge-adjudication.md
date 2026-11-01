# Root-first next-edge adjudication

Status: **READ-ONLY DISPATCHER RESULT**; no sprint or theorem packet admitted.

## Exact parent edge

`Contracts.lean:128–130` requires:

```text
generates(s, x, d) ∧ solves(d, a)
  → ∃ e, sourceJudgment(s, x, e) ∧ sameScoped(s, x, e, a)
```

An endogenous algorithm theorem of the form
`acceptedRun(d, n) → solves(d, readout(n))` has **zero delta** for that root.
The parent already assumes `solves(d, a)` for every satisfying assignment;
one produced assignment cannot establish the source derivation for an
arbitrary satisfying assignment. Defining every solution as run-produced
would add a separate completeness premise and change the parent edge.

The unresolved edge remains independent generated-constraint satisfaction
implying the original source-rule premises under the same assignment, source
scope, and shared witness. Literal L1 is the first concrete missing source
equation. Annotated literals also need the original synthesis-to-written-target
boundary and final-root readout.

## Next action

Use the existing R206/R207 material to finish the authority step for Literal
L1: authenticate an existing original rule, or present the concrete reviewed
definition for approval. Do not repeat the payload table or launch a solver
reflection theorem assuming the missing relation. The approved structural
Union operator remains in the core; typed Union's selected dependent result
telescope remains at source Call/incidence.

This is not evidence that Yulang soundness is false or semantically
underdetermined. No original root or package closes here. State remains
**0/4 roots; 0/5 packages**. R209 remains `CLOSED_INCOMPLETE`; no new sprint,
source semantics, proof, build, test, Rust change, or environment was started.

Dispatcher: `/root/r172_next_packet_selector`, read-only follow-up after the
independently reviewed root-first plan. Its prior whole-run recommendation is
corrected: that result can later support implementation/output soundness but
does not reduce the original `InferenceSoundness` root without an exact
composition edge.
