# NPAIR source-admission sprint closeout

Sprint `npair-source-admission-correspondence-20261018`, contract rev1. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original source domain and
quantifiers are unchanged.

## Outcome

- Original parent conditions closed: **0**. Universal source/native
  correspondence, F1/FK1, N-Transport, N-Subtract-Elim, Call, soundness,
  principality and termination remain open.
- The adopted nonempty concrete-only negative formal-port source instance now
  passes normal parse -> HIR -> source annotation identity checks ->
  `CandidateInference::solve`. The candidate implementation changes only
  `candidate_source::preflight_formal`; all other source shapes retain their
  existing decision. The regression covers the adopted target, formerly
  accepted omitted/symbolic/positive cases, empty/mixed solver refusals and a
  multiple-symbol HIR refusal.
- Independent first-pass compiler and spec reviewers found no predicate or
  scope defect. They caught an evidence gap because the test initially merged
  HIR and solver errors. Luna repaired the helper to require HIR success before
  solver-refusal assertions. Fresh compiler and spec delta reviews were CLEAN.

## Verification and review snapshot

Final code: `crates/yu-solver/src/candidate_source.rs`, SHA-256
`4ea9d89e4a31e7be4ce170517e50eea31dd9e054c360cedba9ccc9cb7ced69ce`.

The focused test command ran **1 passed, 0 failed**. The repaired test requires
successful HIR construction before asserting empty/mixed solver refusal; it
checks multiple-symbol refusal separately at HIR. `git diff --check` and
`python3 tools/agent_sprint.py check` pass. The latter is static scheduling
evidence, not compiler or reviewer evidence.

Proof/audit output `notes/theory/2026-10-18-npair-hir-first-failure.md` is
conditional: `StructuralProjection` also hides `FormationError::Unsupported`,
so the exact producer of earlier fixture failures remains UNKNOWN. The
successful target runtime path resolves that source-entry fixture obstacle for
one instance only. No HIR/syntax code or expected outputs changed.

Resources: 4980 seconds fully charged/reserved, Astra0. Writer and reviewers
have STOPPED; the source file and evidence are frozen. Git outcome is recorded
in the current sprint state after integration.

## Next original prerequisite

Attack N-Ingress: associate an authentic contribution with its exact negative
formal incidence for both existing and future lowers. The reviewed constructor
provides permission and a paired row but does not itself provide `At(D,w,δ)`.
The next sprint must derive the incidence from ordinary Function decomposition
and lower propagation, then test real propagation without manufacturing
contributions. N-Transport and subtraction remain separate downstream gates.
