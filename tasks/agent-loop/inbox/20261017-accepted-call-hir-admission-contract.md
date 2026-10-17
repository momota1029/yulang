# Frozen design handoff: accepted-call-hir-admission-contract

Sprint: `accepted-call-hir-admission-contract-20261017`, contract revision 2,
SHA-256 `f92c1269f47ae1ba3c002244f7254ebc7792af5270ad6a634f033e91323cf19a`.
Design: `notes/design/2026-10-17-accepted-call-hir-admission-contract.md`.
Design SHA-256: `2f3b6dbb6e735b3c5da96f0bbdaa8357f7580435999e08136ce24e1bf19174ab`.
Handoff revision: 3 (design-hash correction). Status: frozen Draft; direction only, with final implementation authority still requiring exact reviewed contract approval.

## Parent and outcome

Original inference/execution goal, full A/B/F1/FK1/N-Transport/Call,
soundness/principality/termination and source/native quantifiers remain OPEN.
Original premises discharged: 0. No compiler behavior executed or established
by this sprint. The source `my id x = x; my apply f = f 1; my answer = apply id`
still fails the previous zero-HIR-error gate before candidate solving.

## Result for Luna's intake

Astra's artifact
`notes/theory/2026-10-17-accepted-call-hir-projection.md` (SHA
`0c1a29f3d590f68064e980459a4373400702034a2366591dae32fe7b1572e25f`), reviewed
CLEAN by independent compiler_referee (`/root/accepted_call_hir_projection_compiler_review`,
requested gpt-6.1-sol/medium, observed UNKNOWN, 100 seconds), establishes only
conditional source/HIR correspondence under its explicit CST-shape premise.
It derives left-associated Apply structures and node-based occurrence
preservation; it identifies HIR-APP-ADMISSION-1, which current authority leaves
unselected. HIR-APP-CST-1 remains open for exact parser/source-key audit.

The Draft presents two unselected paths:

- A: supersede current HIR unsupported-application admission for the specified
  structurally supported forms. This can meet the present zero-HIR diagnostic
  gate, but still does not prove that CandidateInference generates/propagates
  Call constraints. It requires an explicit decision and broader consumer,
  diagnostic, identity, recovery and resource contracts.
- B: preserve ordinary HIR's `UnsupportedExpression` and continue only through
  a separately specified experimental source carrier. This preserves the
  current HIR contract but does not meet the present zero-HIR gate.

No option is adopted. “Ignore errors” or weakening the existing assertion is
not proposed. User direction is required before any code/diagnostic change. A directional selection alone is insufficient: the complete successor contract must specify grammar, recovery, representation, diagnostics, identity/allocation, consumers, and resource limits; then fresh spec/compiler/architect review and explicit final user approval of that exact contract and its supersession must precede implementation. Earlier approval counts only if its recorded scope already decides those details.

## Sequence and source limits

Fresh `spec_auditor` then `architect` reviews completed on the frozen design
bytes. The initial spec review found a major underspecification in the approval
sequence; revision 2 closed it by requiring explicit approval of the exact final
reviewed successor contract. The spec delta review is CLEAN. The architect review
is CLEAN as a directional Draft and found only that this handoff embedded the
prior design hash; revision 3 corrects that receipt, with no design-byte change.
The handoff correction is awaiting its bounded receipt delta check. No review
approves a semantic choice. This handoff grants no compiler-source, test or
execution lease. If A is selected, perform the exact parser/CST/source-
key audit and freeze a reviewed superseding contract before code. If B is
selected, define and review its separate provisional source-carrier/solver
boundary, keeping the accepted-source gate open. In either case, later
source-to-constraints, propagation and actual consumer remain separate evidence.

All original source/solver gates, OPRESP-DEFAULT-1, OPRESP-ENTRY-1, C-OMIT,
F1/FK1 and N-Transport stay open. Astra and compiler reviewer STOPPED; no
coauthors, tests, builds, probes, Cargo, Git, code edits, descendants or scratch
paths. Luna owns the design Draft and handoff. Neither review certifies the design as
Authoritative; primary adjudication follows receipt reconciliation.
