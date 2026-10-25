# FORCE-SOURCE-MAPOP-CORRECTION-20261025/r5 outcome

Status: **ACCEPTED NARROW CORRECTION** after fresh independent CLEAN review.
This consumes the final 250 worker/reviewer seconds of r4's 1,800-second
envelope; F/P/audit charged 1,500 seconds and Luna's final adjudication was
bounded to the remaining 50 seconds. No carryover.

## Frozen inputs and receipts

| Artifact | SHA-256 |
|---|---|
| r5 contract `force-source-mapop-correction-20261025-r5.md` | `88b5f57c9606dc0cd6d27731a7f9aafc127aa14e2715cde261eff2ffc27fd13a` |
| source correction `inbox/20261025-force-source-mapop-correction-r5.md` | `203d55dc462046f0616eba027198c68224182fdf4ab03bf19ccb87548c691b8b` |
| F source report | `a849f178fbc55eb653c2fc4295e4b4675935e7c904cbef7da5100edb0b983212` |
| P source report | `d7f8853e07cf2ec73fb99d3cbe045f3ab5b2e6f5626469417648a9fbfc313f88` |
| operational paper | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |

Fresh Sol/low `spec_auditor` returned **CLEAN**. The correction matches the
source's matching-mapop payload direction `P_o(A) -> P_o(B)`, response
interface `Q_o(B) -> Q_o(A)`, and continuation
`let z' <- r(z) in mapop_w N0[z'/x]`. It keeps final result `T`, captures
binders safely, freshens once per resume, distinguishes nonmatching requests,
and leaves both adapter computations outside recursive mapping. It withdraws
P's unconditional mapop frame/response-type assertion. The auditor confirmed
all five digests.

The original P artifact remains byte-preserved. Read P's mapop equations only
through this narrow correction; no other P proposition is changed. F remains
accepted only as a bounded missing-source-derivation characterization. No
source-qualified semantic ambiguity was established.

## Remaining gates and boundaries

`O-NORM` (source administrative-step expansion and Lean trace adequacy) and
`O-RESULT` (`ForceReturnRows`, including exact incoming occurrences and
template domain/image) remain **OPEN**. The correction proves no source-to-Lean
projection, Force implementation, S/C, Call A/B, preservation, type safety,
inference correctness or parent theorem. No semantic choice, representation
adoption, production authority, or expected-output change is approved.

Researcher receipts: F 600s, P 600s, r4 reviewer 300s, r5 correction 100s and
r5 auditor 150s; all elapsed times UNKNOWN, so each full grant was charged.
The r5 auditor reports one read-only `git diff --stat` despite the frozen
no-Git rule; it reports no edits and no semantic evidence from that command.
The primary used no Git mutation; `.git` remains read-only in this workspace.
No Lean, build, test, compiler or scratch-file work occurred in r5.

Current-state record updated; static sprint checker passed after recording.
No commit/push is possible while `.git` is read-only. Proposed checkpoint
message when Git becomes writable: `research: correct captured mapop response adaptation and input typing`.
