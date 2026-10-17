# Sprint closeout: accepted-call-hir-admission-contract

Contract rev2 SHA-256:
`f92c1269f47ae1ba3c002244f7254ebc7792af5270ad6a634f033e91323cf19a`.
Baseline: `577172e30fe9e282f910cb5ff8267a42beea4a75`.

## 1. Original unresolved conditions

Genuinely discharged: **0**. Full original A/B, F1/FK1, N-Transport, Call,
soundness, principality, termination, OPRESP-DEFAULT-1, OPRESP-ENTRY-1 and
C-OMIT remain open/unadopted with their original quantifiers and source domains.

Astra's conditional source/HIR artifact
`notes/theory/2026-10-17-accepted-call-hir-projection.md`
(SHA `0c1a29f3d590f68064e980459a4373400702034a2366591dae32fe7b1572e25f`)
was independently compiler-reviewed CLEAN. It derives the authoritative
left-associated source form under an explicit CST-shape premise and traces both
application bodies to `UnsupportedExpression` in ordinary, carrier, and shadow
owners. Exact parser/source-key correspondence remains HIR-APP-CST-1. It proves
no Call typing or solver theorem.

## 2. New implementation behavior

No new compiler behavior was executed or established. No code, test, fixture,
expected output, or diagnostic implementation changed. The earlier fixed source
still fails its zero-HIR-error assertion before `CandidateInference::solve`.

The reviewed directional Draft is
`notes/design/2026-10-17-accepted-call-hir-admission-contract.md`
(SHA `2f3b6dbb6e735b3c5da96f0bbdaa8357f7580435999e08136ce24e1bf19174ab`);
its receipt is `tasks/agent-loop/inbox/20261017-accepted-call-hir-admission-contract.md`
(revision 3, SHA `ac9a5f5194e8dc7b8ec0d67d28eafc72ecbc14b6ddec7d852b9e6d91c607ad81`).
The spec review's major approval-sequence finding was repaired and delta-reviewed
CLEAN. Architect review is CLEAN as a directional Draft; its handoff digest
finding was corrected and receipt-delta reviewed CLEAN. These reviews do not
adopt A or B and do not authorize implementation.

Resource charge: 1400/1500 seconds; remaining 100 seconds retired. Charge
breakdown: selector 120, Astra 480, compiler review 100, Luna design 420, spec
review+delta 160, architect review+receipt delta 120. Three inherited UNKNOWN
writer reservations and the legacy board lease remain quarantined.

## 3. Remaining item and next action

`HIR-APP-ADMISSION-1` remains unresolved. The user must select a direction:

- **A:** admit structurally associated application expressions in ordinary HIR.
  This is the shortest route to the existing zero-HIR condition, but supersedes
the current unsupported-application contract and needs a complete successor
contract and explicit final approval after independent review.
- **B:** preserve ordinary HIR's current `UnsupportedExpression` and pursue a
separate provisional source-carrier/consumer contract. This can keep independent
implementation work alive but does not pass the current zero-HIR gate.

The design contains the exact compatibility boundary. After direction
selection, Luna must write and independently review the complete grammar,
recovery, representation, diagnostics, identity/allocation, consumer and
resource contract; then obtain explicit user approval of that exact contract
and its supersession before code. No test assertion is weakened. The source-to-
constraints/propagation/consumer path remains unestablished.
