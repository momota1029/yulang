# Question: native ordinary Direct consumer architecture

Question ID: `native-direct-consumer-architecture`
Question revision: `q1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `6982402afa95f93552bdd5954d22c852b27b3f92`; reviewed proposal SHA-256 `1947eff96d4450f33f446988e75f5d818bf5d75b641bdbfbfbb0d0dc2e6aae60`
Task/thread locator: unavailable; the active objective is supplied in the conversation context, with no exposed thread identifier
Governing source/section: `rules/design-authority.md`, “Authority order”, “Design status”, and “Approval and implementation gate”; `notes/design/2026-10-08-native-projection-public-export-definition.md` §3; `notes/theory/2026-10-08-projection-public-export-construction.md` §§6.1–6.3; reviewed proposal `notes/design/2026-10-08-native-direct-consumer-plan.md`

## Requested scoped decision

Choose whether to adopt the proposed implementation architecture for a finite
ordinary `Direct(u,V)` proof checker against supplied native public roots, or
to defer this checker until its root producer and consumer can be designed as
one integration gate.

This decision concerns only the checker architecture direction. It does not
approve a public API, source/application semantics, an inference-routing
change, or replacement of F5. The exact numerical resource limits and the
complete production local-law owner inventory remain separate required gates
before implementation.

## Background and current premises

The selected native projection contract already defines a proof-directed
ordinary consumer with `Value`, `Computation`, and complete `Function` cases.
It requires checking against the actual submitted roots, original whole
scopes, complete alternatives and same-provider obligations. The reviewed
proposal translates that contract into a candidate flat proof arena, iterative
validation, a sealed immutable root environment, and one shared work/byte
budget per source-checking compilation.

Independent compiler-referee and specification reviews found no semantic or
conformance finding. A performance review identified incomplete work/resource
accounting; the proposal was repaired and a focused performance delta review
closed the remaining wording issue. No code, tests, builds, or measurements
were run. The proposal remains reviewed but non-authoritative.

The current production tree has no successor source-checking caller, public
root producer, or native Direct checker. F5 remains the only production
inference implementation. The pending flat-Application owner-family question
does not affect this checker-only scope.

## Options and consequences

1. **Select the flat-arena checker direction.** Adopt the reviewed architecture
   proposal as the direction for a checker-only implementation gate. Continue
   first with exact caller/law-owner mapping and numeric resource limits; no
   implementation or routing change is authorized by this choice. This allows
   checker work to proceed independently of the missing source producer, but
   the checker cannot be treated as a production inference path until the
   producer, source bridge and caller are established.

2. **Defer until producer and checker are designed together.** Keep the
   reviewed Direct theorem research-only and do not implement this checker yet.
   This avoids committing to an intermediate checker boundary, but postpones
   the ordinary Direct consumer gate while the native public-root producer is
   still missing.

These options do not change the selected `Direct` semantics or authorize F5
cutover.

## Affected work

Blocked scope: selecting this checker architecture for implementation and
writing its implementation plan.

Independent authorized work: continue the HIR/source producer bridge, the
authentic Parameter telescope investigation, public-root production, and
other open A/B inference and lifecycle gates without assuming either option.

Required answer: select option 1 or 2, with any scope restriction. Explicit
approval must refer to this question revision or the exact reviewed proposal
revision above.

Pending publication: keep this entire question directory unstaged and
uncommitted until the questioning primary discovers and validates an
explicitly approved local answer and commits the matching question/draft/
answer together. The answering primary never mutates Git. Posting does not
pause the goal; dependent work waits while independent work continues on
disjoint paths.
