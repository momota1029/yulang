# FORCE-SOURCE-MAPOP-CORRECTION-20261025/r5

Status: FROZEN by Luna. This is a 300-second bounded correction continuation
inside the original 1,800-second r4 envelope. No carryover or renewed grant.
Parent Lean semantics/inference, Force realization, Call S/C and Call A/B remain
OPEN.

## Inputs

The operational paper is authoritative; the two research reports are frozen
candidate evidence. Preserve both reports unchanged.

| Input | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| r4 contract `tasks/agent-loop/sprints/force-result-source-equations-20261025-r4.md` | `0574716388f51878a02d589780208746de292ea141a5e92f608dce1eba955e51` |
| F report `tasks/agent-loop/inbox/20261025-force-result-flow-derivation.md` | `a849f178fbc55eb653c2fc4295e4b4675935e7c904cbef7da5100edb0b983212` |
| P report `tasks/agent-loop/inbox/20261025-force-source-input-equations.md` | `d7f8853e07cf2ec73fb99d3cbe045f3ab5b2e6f5626469417648a9fbfc313f88` |
| r4 independent audit | frozen final response, verdict BLOCKING for P mapop; F classification CLEAN |

## Exact assignment — MAPOP-CAPTURE-RESPONSE

One fresh Sol/high researcher, maximum 100 seconds. Sole output lease:
`tasks/agent-loop/inbox/20261025-force-source-mapop-correction-r5.md`.

Correct only P's matching-mapop continuation equation and its unconditional
response-type preservation assertion. Derive from paper 694–719:

* For matching source instance A and target B, outgoing payload uses
  `a : P_o(A) -> P_o(B)`.
* The wrapped continuation accepts `Q_o(B)`, applies
  `r : Q_o(B) -> Q_o(A)`, then continues as
  `let z' <- r(z) in mapop_w N[z'/x]`.
* Preserve the final continuation result type. Alpha-rename captured binders
  before inserting response code; preserve exactly one source resume
  freshening.
* Separate nonmatching propagation: it preserves that request's interface and
  reinstalls mapop around its continuation.
* Keep response-adapter computation outside recursive transformation by the
  same mapper. State exactly when a frame-append equation does and does not
  preserve response type.

This packet is a source correction, not Lean code or a global representation
adoption. Give a compact delta that supersedes only P's cited mapop equations;
do not rewrite or modify P. Preserve its other candidate equations and open
premises as-is.

Falsifiers: unchanged matching response type; omitted or reversed response
adapter; wrong A/B direction; captured free names; double freshening; recursively
mapping the response-adapter computation.

## Independent delta audit

Only after the correction freezes and its author STOPs, one fresh Sol/low
spec_auditor gets a 150-second review-only assignment. Check the exact artifact
hash and equations against the pinned paper, capture/binder conditions,
matching versus nonmatching cases, and the stated frame-append scope. Return a
verdict and precise citations in the final response; write no file.

## Resources and gates

Original r4 envelope: 1,800 seconds total. Already charged: F 600, P 600,
review 300 = 1,500. Remaining: correction 100, audit 150, Luna adjudication
50 = 300. Charge full individual grants where elapsed time is UNKNOWN. No
descendants, code, Lean/Lake, tests, builds, compiler runs, Git, scratch files,
semantic promotion or representation adoption.

Acceptance means only: P is usable with this exact reviewed correction; F's
missing-evidence characterization remains accepted within its review scope.
O-NORM (administrative trace adequacy) and O-RESULT (`ForceReturnRows`) remain
OPEN. No Force realization, S/C, Call A/B or parent theorem closes here.
