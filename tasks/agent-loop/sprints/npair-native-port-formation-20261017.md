# Sprint npair-native-port-formation-20261017

Status: ACTIVE, proof and implementation-readiness only; no compiler-code lease.
Branch / baseline: `research/simple-sub-intrusion` /
`9948ca23f7034dd67d878257db3df2237a7e66bd`.
Original parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Authority: adopted NPAIR §§2–4, with all implementation and parent gates kept
separate as pinned below. Luna is primary, reviewer assigner and sole integrator.

## Original outcome and success evidence

Produce an implementation-ready, source-grounded account of the first missing
native producer for the adopted negative formal-pair interface. Prove how the
adopted N-Port-Intro/N-Function-Intro constraints map to the actual source-owned
formal annotation and its existing value/effect constraints. Then produce a
reviewable Draft code contract and unapplied patch for a possible future
producer change, including ownership, allocation/failure atomicity, accounting
and exact guard/preflight boundaries.

Success means: (1) source case coverage and both ordinary formal edges are
derived without changing the original source domain or inventing `C_sym`; (2)
one shared flexible negative effect port is distinguished from permission
metadata; (3) the structural path/scope/occurrence inputs available at the
source boundary are named, while authentic contribution-derived `At` remains
separate; (4) a coherent unapplied producer contract shows exact changes and
failure/resource behavior; and (5) fresh independent proof/compiler,
architecture and specification reviewers find no blocking/major flaw.

This does not implement native formation, enable source preflight, remove
refusal guards, authenticate ingress, transport `At`, select a receive
consumer, subtract a contribution, or close the parent. No expected-output
changes, tests, fixtures, diagnostics, or semantics may be edited.

## Governing inputs and immutable pins

- Adopted NPAIR definition:
  `notes/design/2026-10-17-negative-formal-pair-formation-proposal.md`,
  SHA-256 `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`.
- Adoption receipt:
  `notes/design/2026-10-17-source-formation-proposals-adoption.md`,
  SHA-256 `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`.
- Existing native readiness contract:
  `notes/design/2026-10-17-negative-pair-native-implementation-contract.md`,
  SHA-256 `36d9792d7a5bb4d06beeb4a1c62df28d38ff171fc324783061c2219a970ce064`.
- Frozen construction obstruction:
  `notes/theory/2026-10-17-receive-negative-pair-construction.md`,
  SHA-256 `2b526b92ef78b8514a81592b303e4db2310dedd13483c74bcfb4bd53798f0a8f`.
- Implemented local-use retention closeout:
  `notes/progress/2026-10-17-local-use-retention-implementation-closeout.md`,
  SHA-256 `674e67dc9f8a3484c58a2b706b8e634ed8b3ffa80495618bb3706d6fdd110087`.
- Retained-map applied correspondence:
  `notes/theory/2026-10-17-local-use-retention-applied-correspondence.md`,
  SHA-256 `198046b6eb398734cf657ab03f05e171f8be568c1e8feb31115b9adc46d5f1ff`.
- `candidate_effect.rs` baseline SHA-256:
  `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9`.
- `candidate_source.rs` baseline SHA-256:
  `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`.
- `candidate_context.rs` baseline SHA-256:
  `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`.
- `lib.rs` baseline SHA-256:
  `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`.
- Reviewed retention implementation commit: `9948ca23f7034dd67d878257db3df2237a7e66bd`.

Any hash mismatch or additional governing decision returns to Luna before the
affected artifact is relied on. Do not load the whole historical task ledgers.

## Proof lane — Astra/medium, maximum 900 seconds

Sole outputs:

- `notes/theory/2026-10-17-npair-native-port-formation.md`
- `tasks/agent-loop/inbox/20261017-npair-native-port-formation.md`

Derive the producer lowering from adopted N-Port-Intro/N-Function-Intro and the
actual source/constraint path. Inspect
`candidate_effect::candidate_formal_pair`,
`candidate_formal_effect_port`, `candidate_formal_annotation`, and
`candidate_source` registration/preflight. Cover the original annotation
shapes, one shared row and polarities, separate concrete permission
declarations, both ordinary formal links, all Function children, computation
effects and `C_sym`. Identify the exact occurrence/path/scope inputs carried by
the source action and which are insufficient to establish a contribution
derivation.

Trace existing symbolic, concrete and mixed source cases against the adopted
source domain. Do not infer that an unsupported current path makes the source
case semantically unsupported. If the adopted definition leaves a concrete
connection underdetermined, return the exact decision to Luna; do not silently
choose a join, split or source restriction. Distinguish the formal occurrence
descriptor/Permission from authentic constraint-derived `At(D,w,delta)`. Do not
claim later transport, whole-presentation `rho_u`, consumer selection or
subtraction. Apply useful derivations to the original recursive receive parent;
name the exact remaining source/native premise and owner.

Author only after receiving the assigned active receipt. Do not start a
subteam. Static/hash/source analysis only; no tests, probes, builds, Cargo,
compiler execution, expected-output changes or source edits. Freeze both
outputs and STOP before Luna's contract-author lane begins.

## Implementation-readiness lane — Luna/high, maximum 600 seconds

After Astra STOP and frozen proof pins, write only:

- `notes/design/2026-10-17-npair-native-port-code-contract.md`
- `tasks/agent-loop/inbox/20261017-npair-native-port-code-contract.md`

Use the proof and existing readiness contract to present one exact candidate
producer patch and alternatives. Name source owner, representation, sharing
key, polarity construction, ordinary edges, Permission storage, ownership,
allocation reservation, rollback and checked resource accounting. Identify
which source forms the exact adopted rule justifies and list unresolved
interpretations as decisions. Keep the negative-concrete refusal and source
registration/preflight refusal intact. Show explicitly why no current compiler
code or test lease follows from this contract.

Do not add native `At` producer, ingress transport, future scheduling,
subtraction consumer, Catch authority, or formal-absence inference. Retained
structural maps may be cited as crosswalk inputs only. They do not supply
Permission, lineage or authentic `At`. The design remains Draft pending
independent review and explicit user approval before any compiler change.

## Reviews, resources and stop conditions

Authors are sequential. Fresh reviewers after both lanes, read-only and
sequential:

1. `compiler_referee`, max 120s: proof-to-source lowering and exact proposed
   patch; ordinary edges, guard behavior, partial failure and accounting.
2. `architect`, max 120s: owner choice, identity/lifetime, failure atomicity,
   resource accounting and whether the proposed patch expands its write scope.
3. `spec_auditor`, max 120s: adopted NPAIR definition, original source domain,
   permission/inflow distinction, `C_sym`, J1/J2 and unchanged output scope.

Fresh envelope: 2100s (Astra proof 900, Luna contract 600, reviews 360,
coordination 120, reserve 120). No time carryover from the prior sprint. One
Astra assignment at a time; keep three historical UNKNOWN reservations and
quarantined board lease. No heavyweight/runtime process is authorized.

Stop on source-policy ambiguity, unavailable source occurrence/scope inputs,
unresolved cross-lane authority, pin mismatch, author cap, independent review
finding or parent counterexample. A reviewer finding returns to Luna; no writer
silently broadens the lease. Do not enable preflight or remove a refusal guard.
Consult the dispatcher again only at a material boundary described in the
operating rule. Luna remains sole current-state/Git owner.

## Parent gates that remain OPEN

Even a clean code contract closes only implementation readiness. Still open:
native source formation/acceptance, authentic `At`, N-Transport through both
Function results and later consumers, whole `rho_u`, future coverage, actual
receive subtraction consumer, N-Subtract-Elim, J1/J2 completeness, F1/FK1,
other independent parent obligations, source/native adequacy and production
authority.
