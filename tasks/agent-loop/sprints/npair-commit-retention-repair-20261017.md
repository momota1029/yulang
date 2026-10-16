# Sprint npair-commit-retention-repair-20261017

Status: adopted by Luna after the sprint-end selector delta and the user's
acceptance of that proposal. Revision 1.
Branch: `research/simple-sub-intrusion`.
Administrative baseline: `ab32591e91d0759620a2b9d3d0d54513fb4a0f73`.
Compiler baseline: `74bfaa6a8ce0a60051e40e531c54576516d6c151`; source-owner pins
below were rechecked against the working tree before opening this sprint.
Authority: adopted NPAIR proposal §§2–4; corrected native readiness contract
as planning guidance only; `rules/goal-driven-sprints.md`; prior bounded
conditional J2 proof and its CLEAN review within their recorded scope.

## Outcome

Repair the specific lifecycle gap found by the architect: `FreshUse` maps are
construction scratch and are discarded by `GraphState::commit_local_use`, so
the architecture candidate must identify the correspondence and dependencies
that survive commit for later consumers. Establish a bounded retention
invariant from the inspected capture/restore/commit path, apply it to the
candidate, then obtain fresh independent architect and spec-auditor reviews.

Original parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, its source
domain, quantifiers and accepted meaning remain OPEN and unchanged. Whole native
`rho_u`, J2 native correspondence, actual residual consumer, source/native
adequacy, extrusion/intrusion, symbolic coverage, F1/FK1, soundness, principality,
F5 and production remain OPEN. A retained-evidence design is not evidence that
current code already implements it, and does not authorize compiler changes.

Success: (1) a constructive, explicitly limited projection/retention argument
states which descriptor, contribution, derivation, use, scope and dependency
relations later consumers need and what the current commit path discards; (2)
the repaired Draft candidate specifies pre-commit promotion, committed owner,
lifetime, rollback/invalidation, pending-progress contract and bounded/shared
accounting; (3) fresh architect and spec-auditor reviews accept the exact frozen
bytes or return actionable findings. Do not claim whole `rho_u` or parent
closure from this local lifecycle result.

## Lanes, leases and sequence

1. Sol/high constructive proof, cap 240 seconds, at most four substantive
   stages. Exact writes:
   - `notes/theory/2026-10-17-npair-use-certificate-retention.md`
   - `tasks/agent-loop/inbox/20261017-npair-use-certificate-retention.md`
   Inspect `Graph` capture, fresh-use construction/restoration, and
   `GraphState::commit_local_use`. Derive the retained projection required by
   the candidate's later consumer; identify the exact map fields lost at commit
   and prove that the proposed retained record supports those consumers without
   reconstructing discarded maps. This is a design invariant, not a claim that
   native code complies. Stop on any need to assume missing NPAIR constructors,
   source correspondence, consumers or unleased edits.
2. After the prover has frozen its result and STOPPED, Luna/high, cap 600 seconds,
   repairs only:
   - `notes/design/2026-10-17-npair-native-architecture-candidate.md`
   - `tasks/agent-loop/inbox/20261017-npair-commit-retention-architecture-repair.md`
   The byte-exact prior candidate is preserved at
   `tasks/agent-loop/snapshots/20261017-npair-native-architecture-pre-commit-repair.md`.
   Promote required correspondence into the retained route/session Use owner
   before final commit. Specify lifetime, identity/reference accounting,
   rollback, invalidation and consumer access. Assign pending-association
   registration, wake-up events, completion criteria and a progress argument.
   Bound duplicate/path growth with a shared derivation DAG or equivalent and
   account for records, indexes, references, undo state and subscriptions.
   Keep all unproved native/source gates explicit. No code lease.
3. After Luna freezes the corrected candidate and handoff, fresh architect
   review (120s) then fresh spec-auditor review (120s), exact bytes and inputs.
   Stop on any major/blocking result. A substantive new proof claim that exceeds
   the bounded retention argument returns for reconciliation; do not silently
   widen proof authority.

Fresh envelope: 1200 seconds total — proof 240, architecture author 600,
reviews 240, coordination 60, reserve 60. One author at a time, no Astra,
descendants, code, tests, Cargo, builds or execution. No previous budget carries.
Preserve three historical UNKNOWN reservations and the quarantined
`tasks/agent-loop/board.md` lease. Unknown identities keep their reservations.

## Frozen inputs and owner pins

- Adopted definition: `notes/design/2026-10-17-negative-formal-pair-formation-proposal.md`,
  SHA-256 `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`.
- Adoption receipt: `notes/design/2026-10-17-source-formation-proposals-adoption.md`,
  SHA-256 `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`.
- Corrected readiness plan: `notes/design/2026-10-17-negative-pair-native-implementation-contract.md`,
  SHA-256 `36d9792d7a5bb4d06beeb4a1c62df28d38ff171fc324783061c2219a970ce064`.
- Bounded conditional proof: `notes/theory/2026-10-17-npair-whole-presentation-transport.md`,
  SHA-256 `cc9aee77661de00ac011a9da411b385e9e440277bb194bc13a83d71f973b0719`;
  CLEAN only for its conditional anchored J2 result.
- Prior candidate: `notes/design/2026-10-17-npair-native-architecture-candidate.md`,
  SHA-256 `278e1de992421fc237468a266eb3051388ea3c7e5019ca4f95daf9fe72ff96e6`.
- Prior candidate handoff SHA-256
  `5b86a5d8983d311715774368d2d1542e55d35c9d0672e310617b621efff4714e`.
- Pre-repair snapshot SHA-256
  `278e1de992421fc237468a266eb3051388ea3c7e5019ca4f95daf9fe72ff96e6`.
- Direct owner pins: `candidate_scheme.rs` `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`,
  `candidate_effect.rs` `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9`,
  `candidate_context.rs` `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`,
  `candidate_extrusion.rs` `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b`,
  `candidate_source.rs` `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`,
  `candidate_receiver.rs` `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3`,
  `shadow_apply.rs` `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`,
  and `lib.rs` `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`.
  Recheck before relying on each owner.

No expected-output changes, semantic narrowing, consumer invention or production
promotion. The next dispatcher consultation is at an authority/dependency/lease
change, substantive proof obstruction, integration seam or sprint close.
Luna owns state, review adjudication, exact-path staging and non-forced push.
