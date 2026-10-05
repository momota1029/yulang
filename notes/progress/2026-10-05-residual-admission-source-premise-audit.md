# Source-premise audit for residual admission retraction

Date: 2026-10-05
Status: read-only design-source characterization; no source rule or implementation authority
Baseline: `a38e79e61`
Inputs: [admission-retraction conditional theorem](2026-10-05-residual-admission-retraction-proof.md), [open residual factorization](../design/2026-10-03-open-residual-factorization.md) §§2–7, [scoped structural projection](../design/2026-10-03-scoped-structural-projection.md) §§2–6, [source-generated C/S theorems](../design/2026-10-04-source-generated-callback-structural-theorems.md) §§2–7

## Result

The reviewed structural construction already transports the one-class
mandatory-Record bound, fixed visible upper comparisons, and propagated rigid
permissions through projection and the closed-copy/fresh-root graft. The
unclosed condition is the candidate-dependent leaf of joint admission:

```text
A(T, omega) = Guards(T, omega) and Phi(T, omega)
```

The source documents do not give an exhaustive primitive interpretation for
how these guards and Phi/K,D inspect the varying structural endpoint, retain
its original operand tuples, or update comparison context on derived checks.
That is the data needed to prove decidability/extensionality and to transport
admission to the graft. Theorem C's lift preserves every old operand
unchanged, while grafting changes the structural operand T; Theorem C
therefore does not establish this transport. Theorem S explicitly leaves
arbitrary guards and Phi/K,D outside its scope.

This is not evidence that any actual Yulang source predicate violates a
retraction property. No such source counterexample was found. It also does not
justify taking “admission is graft-preserving” as a language restriction:
that would assume the key step of the membership theorem. Production
membership must retain existential original assignments unless and until its
primitive admission clauses prove otherwise.

## Minimum missing source rule

Specify each primitive admission clause that mentions the changing endpoint,
including its complete operand tuple and the source context attached to every
derived comparison. Then establish, clause by clause, whether its existing
joint witness and context can be reused after structural projection/grafting.
The already-closed structural and permission transports can be factored out;
the unresolved portion is source incidence/provider/equality and guarded
comparison admission. This is an exact missing source interpretation, not a
new carrier and not a decision to reject programs outside the conditional
theorem.

The audit is bounded to the cited design sources. It did not inspect a
production Admit_F implementation or establish that one exists; source HIR
and current solver coverage are separate evidence. No code, tests, probes,
or Git state were changed by the auditor.
