# R31 independent review receipt — Luna intake

Reviewer: `/root/effect_permission_r31_review` (`compiler_referee`), observed model/effort UNKNOWN. The reviewer is read-only and returned this review in its final message; it wrote no file. Luna records the independent result here without self-certifying it. Reviewer writes stopped, no descendants.

## Frozen inputs checked

- Rust patch SHA-256: `4eb744c6aec78d15c98724d6559440de3a477c1e67ec1116b6eee89ce38a6f85`.
- Rust handoff SHA-256: `3e1fbe2fabc5869feaad573453fa7bff8b463fa04cddd95e7ff2d27f8703596d`.
- Lean module SHA-256: `a0a8b53e1f73ed44e92ee01b3e87531d310775af0804999d30d6fbb0a68e378d`.
- Proof handoff SHA-256: `8c8864cfcd5a93deb66caf6c6c62c5d4078d469c136b75bc559f2ed1ee767732`.
- R30 archive/member hashes, manifest-pinned authorities and source identities matched. The 24,342-byte R26 module is an exact byte prefix of the Lean artifact.

## Disposition

**Major finding: R31 does not pass the faithful-projection gate.** The Rust proposal is correct as a source-level comparison repair within its stated limit. It remains unapplied, uncompiled, and has no observed typed inequality or runtime certificate. The Lean finite-index and conditional R26 proofs are kernel-accepted, but `callback_checked_catch` does not require the mapped operation and family lists to be covered by `IdentityTable`. It uses unchecked total `idxOf` mappings without connecting the callback theorem to the membership-qualified round-trip/injectivity and family-equivalence laws.

Concrete counterexample: with empty operation and family tables, distinct structural operations both encode as declaration ordinal `0` and family `0`, and both decode to `none`. For either operation, set the family row to its single structural family and permission row to `[0]`; supply matching coordinate joins and the mapped arm in the installation. The theorem's premises can hold and its R26 `checkedCatch` result follows even though the encoding table has no entry. This is a projection-coverage counterexample, not a typed native identity collision and not an invalid Lean proof.

Required repair before claiming a faithful finite bridge: require operation-table membership and coverage for every family in the permission row; connect the application theorem to operation round-trip and covered family-membership equivalence; derive consumer and arm coverage through their typed identity equalities or require it explicitly. An uncovered identity must fail coverage/lookup. Native extraction must later establish these hypotheses from an authenticated snapshot.

The reviewer independently reran pinned Lean 4.35.0 via read-only bwrap stdin: 30 theorems, exit 0, empty stderr, no diagnostics; all full theorem types and axiom summaries matched the proof handoff. Axioms: none for R26 `checked_use_inversion`, `permission_preserves_actual`, `empty_conserved`, `companion_emit_actual`, `lifetime_branches_distinct`, and R31 `callback_use_ready`; `propext` for R26 `emit_conserved`, `emit_events_before`, `commit_preserves_other_event`, `commit_removes_selected_event`, `shallow_discard_preserves_contributions`, `normal_return_deactivates`; `propext, Quot.sound` for the remaining 18 declarations. No `sorry`, `admit`, project axiom, `native_decide`, or kernel-check bypass.

The callback bridge still assumes supplied `UseReady`, execution/origin joins, row correspondence, structural operation equality, invocation liveness, and dynamic installation/arm joins. `callbackSlice` inserts the supplied request directly into singleton pending/emitted records. Neither theorem constructs actual request emission, native Grant, annotation/Name/Apply provenance, native `Step`, or native `History`. Original A/B quantifiers, full source domain, hygiene, soundness, principality, progress, termination and production remain OPEN.

Independent audit processes measured 5.646669272 s and 2.224587574 s; total reviewer active time is UNKNOWN. No Cargo, Lake, project copy, target, cache, scratch, log, or installation was created.
