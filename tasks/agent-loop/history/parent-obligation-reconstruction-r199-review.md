# R199 parent-obligation reconstruction — independent review

Target: `notes/theory/2026-11-01-parent-obligation-reconstruction-r199.md`  
Frozen target SHA-256: `7c525a98e53a62a370096d85a3b371af5952dae19d8593b4e02cf3a812c3f36e`  
Reviewer: `/root/parent_obligation_plan_review` (`spec_auditor`; observed
model/effort UNKNOWN). Read-only; no Lean, tests, Rust, Git, or environment use.

## Findings and disposition

The initial review returned two major findings and one minor finding:

1. `PrincipalCoverage` directly implies `SourceScopedCoverage` for the same
   model. The initial draft incorrectly called the roots unrelated.
2. A genuinely new semantic or architecture choice requires recorded user
   approval before adoption, even when an observable difference is not yet
   demonstrated. Independent conformance review alone is insufficient.
3. The ordered plan needed to state where the unchanged coverage formula is
   discharged and how it is counted.

The author corrected all three. The revised note now records the direct
principal-to-coverage corollary and requires its application to close the
separately tracked coverage root; requires derivation from approved rules or
normal authority review and recorded user approval for a new choice; and
explicitly schedules the corollary or a direct coverage proof. The reviewer
confirmed all findings closed and reported no remaining blocker from the
corrections.

This review accepts the **research-plan reconstruction only**. It proves no
theorem, adopts no semantic rule, and leaves all five packages and four roots
open.
