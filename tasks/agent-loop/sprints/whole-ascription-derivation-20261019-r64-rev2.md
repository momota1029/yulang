# R64 contract revision 2 — review the frozen proof and record the stopped lane

Status: ACTIVE additive amendment to revision 1. Revision 1 remains byte-frozen
at SHA-256 `2f008cc535a4db8da53fc40acac6ae5750d25083be6d6abe4a5ee35f318576bf`.
This revision changes only review scope and owner-lane disposition after the
observed routing mismatch. It changes no source/semantic claim, dependency,
budget total, or proof lease.

Branch: `research/simple-sub-intrusion`; R64 source baseline remains
`e5e0ac4e5b72c51406fac82ed82986d734bf3552`. Luna owns activation, current
state, adjudication and Git. Parent/A/B remain OPEN 0→0; R50 NOT ADOPTED.

## Frozen R64 proof target

The proof author is STOPPED / WRITES_STOPPED / NO_DESCENDANTS. Review exactly
these two frozen R64 author outputs:

```text
notes/theory/2026-10-19-r64-whole-ascription-derivation.md
  SHA-256 b8041fae28a4a88d7143ab6e16be6658ce156f3de90888667dded93e8b643772
tasks/agent-loop/inbox/20261019-r64-proof.md
  SHA-256 ca77147a62dc1a43f5cbecacf09a0203add761f235b46998d1ef41255bc7ecc7
```

Review the immutable revision-1 contract and this amendment, plus all 22 exact
source/authority dependencies pinned in revision 1. Verify the proof's prefix
and its bounded first unsupported clause `R64-SRC-ANN-ARG-1`. The compiler
review attacks whether an inspected source constructor supplies the original
carrier interpretation at `p_A`, whether the native guard boundary is stated
accurately, and whether any hypothetical `Q` is mislabeled as emitted. The
spec review checks that the isolated clause is narrower than R63's general
gap, no applicable settled rule was missed, and no missing derivation is
promoted to semantic impossibility or ambiguity. Neither review may certify
complete `xi`, `Sol_src`, `Corr`, actual `Q`, both solution directions, or typed
substitution; the frozen proof explicitly leaves them unconstructed.

Acceptance is bounded clean review, a repaired review finding under a new
frozen revision, or a precise unresolved finding. It is not completion of the
original parent or production gate.

## Owner lane disposition and remaining resources

The planned Luna/high owner assignment `/root/r64_clause_owner` reported a
routing mismatch (`GPT-6` observed against requested Luna/high). Luna issued
STOP and interrupted the active turn. A later explicit receipt confirmed
STOPPED / WRITES_STOPPED / NO_DESCENDANTS. The lane read the pinned
`source_annotation.rs`, `local_source.rs`, `candidate_source.rs`,
`candidate_effect.rs`, R63 evidence and the R64 contract, but created or
modified neither planned owner output (both 0 bytes). Its 500-second grant
remains fully charged; actual runtime and session ID are UNKNOWN. The resolved
exact output paths are not reassigned:

```text
notes/progress/2026-10-19-r64-ascription-clause-owners.md  (no file, 0 bytes)
tasks/agent-loop/inbox/20261019-r64-implementation.md      (no file, 0 bytes)
```

No replacement author lane is funded or launched. The 700 seconds remaining
under R64 are reserved as fresh compiler review 200, fresh spec review 200,
and Luna integration 300; all were charged/reserved at sprint activation and
none carries forward. The stopped-lane reads are not an independently authored
owner deliverable.

## Luna integration and stop boundary

Within the existing 300-second integration allocation, Luna may read the
frozen proof outputs and the already pinned sources to adjudicate the clause
and reconcile the source/native boundary. This is primary integration evidence,
not a replacement for the missing independent owner lane. Luna's only new
artifact is `notes/progress/2026-10-19-r64-closeout.md`; Luna also updates the
central `tasks/agent-loop/current.json` and Git. Any source outside the existing
22-pin manifest, semantic choice, new author, lease, or budget requires a new
Luna decision before use. Do not claim four author outputs were delivered.

Successful integration reports the reviewed partial derivation, review
findings, stopped owner lane and its zero-output receipt, source/native limits,
all charged resources and exact open parent/TODO. `R64-SRC-ANN-ARG-1` and
`R61-SOURCE-ASCRIPTION-FORMATION-1` remain OPEN unless the missing authentic
rule and its derivation are actually established. No code, test, semantic,
source-domain, production or theorem status changes are authorized.

## Receipt

Dispatcher start/integration-boundary advice: reviews may proceed under this
explicit two-output scope; Luna may perform primary-only read-only inspection
under the existing integration grant; absent owner artifacts must be reported
as absent; no replacement lane or added budget is granted. R64 proof output
hashes and author-stop receipts are recorded above and in
`tasks/agent-loop/current.json`.
