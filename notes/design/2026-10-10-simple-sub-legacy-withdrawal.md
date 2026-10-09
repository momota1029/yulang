# Withdrawal of legacy inference prerequisites

Status: Authoritative
Scope: Retirement of mechanisms introduced to bypass Simple-sub, and their current inference dependencies
Approved-by: user (direct explicit instruction)
Approved-at: 2026-10-10
Drafted-by: primary, transcription of the current user decision
Reviewed-by: bounded implementation and dependency reviews recorded at delivery
Supersedes: compulsory legacy mechanisms only where the replacement and dependency removal are evidenced below

## Selected policy

The user explicitly requires active withdrawal of old designs, implementations,
and proof obligations introduced to bypass Simple-sub. Adding another Simple-sub
path is insufficient. Identify local decision rules, early satisfiability
requirements, source-directed special cases and registry construction prerequisites
that constraint generation, propagation, extrusion, intrusion and generalization
replace; remove their actual implementation dependencies.

Obsolete proof prerequisites must leave the active dependency graph with an
explicit reason. Retirement is not discharge or proof closure. Historical
documents may remain, but cannot serve as current design authority for a
withdrawn mechanism.

Complete Call semantics, effect hygiene, soundness and principality remain
genuine requirements. Missing compiler correspondence, semantic evidence or
termination arguments are not retired merely because an older proof route is
withdrawn. The existing annotation polarity policy and parent/copy equality
contract remain in force.

Prefer actual refactoring and regression tests. Record the precise remaining
legacy entrypoints rather than declaring retirement from documentation alone.

## First bounded retirement

1. Remove the mandatory finite source-context/static-port enumeration
   presentation (`CTX_FINITE`) from the active successor DAG. The current
   Simple-sub worklist does not consume this construction. Preserve the complete
   effective joint solving/residual requirement (`JOINT_DEC`) and its genuine
   semantic correspondence and resource obligations. The old source-directed
   decision lemma is historical evidence, not certification of the current
   kernel.
2. Remove the exact captured-local binding reconstruction prerequisite from
   successor graph inference. Actual lexical source formation owns binders,
   scopes, constraints and use-time generalization. Do not infer ownership from
   the former fixture's shape or suppress invalid source/ownership checks.
3. Preserve historical observer clients only where they still have actual
   callers, explicitly distinguishing them from the successor route. Their
   existence is a remaining migration task, not evidence of complete withdrawal
   or public cutover.

This policy supersedes older compulsory construction routes in this stated
scope. It does not replace genuine source evidence with arbitrary native IDs,
erase symbolic effect flow, weaken Call to arrow decomposition, or certify the
current private successor as the production inferencer.

## Implemented candidate lifecycle retirement

The [candidate lifecycle delivery](../progress/2026-10-10-candidate-closed-lifecycle-retirement.md)
removes closed-finalization construction, finish and closed-scheme slots from
the private graph candidate lifecycle. Live graph execution and per-use
freshening replace that runtime prerequisite. Public legacy closed observers
retain their actual finalization owner until public successor migration is
complete. This is implementation dependency removal, not discharge of a
semantic proof node; complete Call, public export, hygiene, soundness and
principality remain required.

## Implemented unused draft resource retirement

The [unused draft delivery](../progress/2026-10-10-candidate-unused-draft-withdrawal.md)
removes the candidate startup reservation of legacy `DraftScheme` scratch.
Actual graph staging replaces that storage owner; every mutable draft consumer
belongs to the legacy SCC branch. The legacy owner retains its real allocation
and failure behavior. Candidate inference no longer depends on success of an
unused F5 reservation. This is runtime dependency removal, not proof discharge;
genuine semantic obligations and public migration remain open.

## Related authority

- [Parent/copy SCC intrusion](2026-10-10-parent-copy-scc-intrusion.md).
- [Annotation effect hygiene](2026-10-10-annotation-effect-hygiene-integration.md).
- [Delivery and remaining migration](../progress/2026-10-10-simple-sub-legacy-withdrawal.md).
