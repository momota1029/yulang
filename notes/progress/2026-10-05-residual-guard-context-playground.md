# Residual guard-context transport playground

Date: 2026-10-05
Status: Synthetic path-guard characterization; no scope or solver authority
Governing sources: [open residual factorization](../design/2026-10-03-open-residual-factorization.md) §§3, 7.1–7.2; [research playground direction](../design/2026-10-04-inference-research-playgrounds.md)

## Experiment

[`tools/research_residual_guard_context.py`](../../tools/research_residual_guard_context.py)
uses one Function bound and a synthetic guard context over five comparison
paths: the root, contravariant Function argument and its Record field, the
covariant result, and a required result Record field. All 32 permission masks
are checked for a residual Record example. Direct guarded comparison and
decomposition followed by residual solving agree for each mask: two succeed
and the other 30 fail at a denied path.

The initial fail-fast normalizer exposed a precedence counterexample. In
`Function(x, Int) <: Function(y, Bool)`, the contravariant argument yields an
open residual before the result has a known structural mismatch under this
model's depth-first Function traversal. With
`x = {a: Int}`, `y = {a: Int}`, and the guard denying the residual field path,
direct assigned comparison returns `GuardFailure`; the fail-fast symbolic
summary returned `StructuralFailure`. The checker was revised to replay the
earlier residual before the later terminal mismatch. The revised model agrees
with direct comparison for all 32 path masks for this witness family. This
refutes fail-fast error summarization for this chosen traversal model; it does
not establish global failure precedence or require an ordered-storage design
in production. The governing source specifies guard-before-local-structural
checks, but does not settle this broader precedence question.

A denied root still returns `GuardFailure`, while an admitted root with
mismatched atoms returns `StructuralFailure`; the two outcomes remain
distinguishable.

## Mutation witness

The context-reset source bound is

```text
Function(Int, x) <: Function(Int, {a: Int})
x = {a: Int}
```

The original context admits every path, so direct comparison and correctly
retained residual comparison succeed. A mutant replaces the residual's
original context with one that denies only the Record-field path. That mutant
returns `GuardFailure`. The witness shows why residual decomposition must
retain its original guard/evidence context. The context and paths here are
synthetic; they do not encode Yulang lexical binder rules.

## Boundary

Each bound specimen visits at most four paths within the five-path union used
to enumerate masks. The probe covers acyclic Function/Record derivations only. It does
not establish that production/source generation creates a finite stable guard
context, model rigid-name permissions, cover recursive feedback, effects, or
integrate a residual graph solver. It gives no acceptance/rejection rule and
does not close the stable-context premise in the governing theorem.

## Review and checks

Focused command: `python3 -B tools/research_residual_guard_context.py`.
The residual and deferred-failure probes pass over their bounded mask spaces;
the context-reset mutant fails as intended. An independent spec review checked
the path-context interpretation, then its two wording findings were narrowed:
the evidence is limited to this traversal's premature terminal reporting, and
the five-path union covers specimens visiting at most four paths. The focused
Python checker and `git diff --check` pass. No Cargo or workspace tests were
run because this isolated checker changes no compiler code.
