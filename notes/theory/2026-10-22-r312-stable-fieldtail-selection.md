# R312 — stable FieldTail selection and same-use Member graph

Status: ACTIVE, solo primary, unreviewed. R149 remains OPEN.
Baseline: `3eb3b64eb`.
Contract: `tasks/agent-loop/sprints/r312-stable-fieldtail-selection-20261022.md`.

## Governing documents reread

Re-read the converted unified design §§4.1–4.5, 6, 9 stages 2/4 and 10, and the proof companion §§3.2–3.8, 4.5 and 7.2–7.4. The implementation must retain source occurrence and semantic payload together; method selection waits for the relevant receiver evidence and its stability condition. The Capture/FreshUse results transport records already in the graph and do not prove candidate completeness, source generation, selection soundness or source/native correspondence.

The effect correction remains binding: contravariant `[io]` means `[io,'e]`, so passing `[state]` alone is not a violation. Actual effect contributions remain present.

## Current source and solver evidence

R310 records an exact `SourceFieldTailObligation` with owner, occurrence, source key, member spelling, authenticated role-member candidate identities, receiver Value/effect rows and result Value/effect rows. Member templates are captured in a separate map keyed by exact `SourceMemberRootId`; no fake definition owner is introduced. Nested member-body FieldTail obligations remain in the Member graph.

The existing `FreshUse` already computes the four FieldTail row indices from the captured graph and retains that ordinal/index tuple with the same `rows` map. Its focused test confirms each local row is fresh and each shared anchor remains fixed. This is transport infrastructure, not a method selection.

Each candidate `MemberSchedule` now retains an exact `SourceImplementationMemberId` when its root is an implementation member; role defaults retain their distinct `SourceRoleMemberId`. `unique_implementation_member_schedule` resolves only that full implementation/declaration identity and rejects a missing, stale, or duplicate match. The existing mixed role-default/implementation fixture checks that the two identity classes stay disjoint and exercises stale and duplicate controls. This closes schedule identity lookup only; it does not join the implementation's role head to the imported `SourceRoleId`, compare targets, or select.

Added `resolve_source_role_implementation_members` to join one exact `SourceRoleMemberId` to each implementation in the authenticated cross-module inventory. It returns the exact implementation body member ID when that body overrides the role member, and records an explicit absent override for the caller to resolve against the role default, if one exists. A differently named implementation member cannot be substituted by ordering or nearby source text. Duplicate implementation candidates, stale role/member IDs, recovered bodies, and unsupported member headers remain unavailable. The focused source fixture checks both an exact override and an absent-override case; this still does not compare implementation targets or establish selection stability.

`CandidateInference::solve_modules_with_role_sources` now receives the exact `SourceExportIndex` and `SourceRoleImplIndex` sets already used by playground module loading. Before inference, it resolves the `SourceRoleMemberId`s retained by deferred FieldTail recipes and stores each implementation's source-owned target plus exact override member ID (or absent override) in the candidate source plan. The unchanged Types boundary test still reaches `DeferredSelectionUnavailable`, so the new route has not yet selected or typed a member. This step transports authenticated inputs into the solver; it supplies no stability witness.

The pinned `Display` implementation target for ordered pairs is exactly `('a, 'b)`. `SourceImplementationType` now retains a bounded structural view for simple names and recursively parenthesized tuples, while unsupported target syntax remains available as original source text with no matchable shape. The shape parser caps nesting at 128 and has a focused nested-tuple identity test. Candidate-plan resource accounting includes the owned shape vectors and names. This is structural source evidence only: generic where-clause obligations, receiver-bound matching, candidate completeness, and stability are still unresolved.

The unresolved seam is selection: there is no consumer that proves the receiver's relevant bounds are complete and stable, matches them against authenticated role implementation sources, requires a unique applicable source, and then attaches one per-use FreshUse copy of the selected Member graph. `unique_role_member_schedule` only identifies one exact role-default schedule; it neither selects a receiver implementation nor certifies applicability.

Contract revision 2 expands the HIR leases after an exact source audit: the pinned `Display` role declaration and its implementations live in different modules. The pre-existing `resolve_source_role_implementations` in `yu-hir/src/shadow.rs` chooses the `SourceRoleImplIndex` whose module equals `role_id.module`, then inspects implementations in that one index. It cannot enumerate `impl ...: Display` declarations in `std::core::fmt` for the imported role identity from `std::prelude`. The implementation index retains the exact syntactic role `SourceImplementationType` and member IDs, while `SourceExportIndex` retains import leaves and public role declarations; there was no function joining these across modules. A spelling scan over implementation text would not establish the role owner.

Added `resolve_source_role_implementation_candidates`. It joins one exact `SourceRoleId` to implementation declarations across module indexes through each implementation module's source import leaves (or its local role declaration), then checks the resolved export kind and exact parse-owned role source key. The result retains `(SourceRoleImplIndex, SourceImplementationDeclaration)` for each match. This is an inventory, not target-type matching, conformance, selection, or method typing. Missing source snapshots, duplicate module indexes, ambiguous role imports, recovered imports, non-role exports, applied role heads, recovered implementations, and missing bodies fail closed. The focused cross-module test verifies an implementation in `fmt` maps through `use roles::Display` to the exact role declaration in `roles`; duplicate source index and missing source index controls fail closed.

## R312 implementation checkpoint

The previous gate ran at the end of `execute_candidate_graph_plan`, after ordinary definitions and Member graphs were prepared but before loose and direct module-expression schedules ran. A nested FieldTail in any captured member template therefore prevented later source roots from contributing receiver bounds, even though the whole private result would be withheld either way.

Moved the gate to the end of the candidate source execution phase, after loose roots and all direct expression schedules. `execute_candidate_graph_plan` now completes template capture with obligations retained; `InferenceSession::execute` returns the same `DeferredSelectionUnavailable` only after expression constraints have been admitted. No candidate result or partial public output is exposed on this error. The member-source regression includes a direct integer expression and checks its actual positive Int lower bound after the deferred member-body FieldTails are reported, proving that the source schedule ran before the gate.

This exposes the correct phase boundary for later resolution but does not yet select a method or establish that receiver bounds are stable. The HIR implementation inventory records syntactic target/role text and member owners. The old resolver handles only the exact same-module simple role head; the new cross-module resolver returns an authenticated candidate inventory but does not compare receiver targets, prove applicability, or select. No R312 stability witness exists yet.

Checks:

- Focused solver regression `member_sources_form_separate_candidate_roots_with_receiver_inputs`: passed.
- Focused HIR test `imported_role_identity_resolves_implementation_in_another_module`: passed.
- The same HIR test passed again after adding the role-member-to-implementation-member bridge and duplicate candidate guard.
- `cargo test -p yu-playground --lib unchanged_types_sample_reaches_deferred_field_tail_boundary`: passed after wiring the authenticated target/member inventory into the solver input; the sample remains deferred.
- `cargo test -p yu-hir --lib`: 162 passed, 0 failed.
- Focused solver regression `member_sources_form_separate_candidate_roots_with_receiver_inputs`: passed after adding exact implementation-member schedule identities and stale/duplicate controls.
- `cargo test -p yu-playground --lib`: 40 passed, 0 failed.
- The unchanged Types boundary test still reaches the same `DeferredSelectionUnavailable` class.
- Full solver library run with default parallelism aborted with worker-thread stack overflow. A serial rerun did not produce a completion receipt within the observed interval and was interrupted; no full solver pass is claimed.
- `python3 tools/agent_sprint.py check` and `git diff --check`: passed after the cross-module resolver update.
- Final boundary recheck: `cargo test -p yu-hir --lib` passed (162/162); `cargo test -p yu-solver --features shadow-apply-candidate --lib member_sources_form_separate_candidate_roots_with_receiver_inputs -- --nocapture` passed; and the unchanged Types focused test passed again after solver-input wiring. The latter still returns the expected research boundary and does not execute the sample.
- `python3 tools/agent_sprint.py check` and `git diff --check`: passed again on the final worktree state.
- `cargo test -p yu-hir --lib implementation_target_retains_bounded_tuple_shape -- --nocapture`: passed; nested tuple/name structure is retained.
- `cargo check -p yu-solver --features shadow-apply-candidate`: passed with existing warnings.
- `cargo fmt --check` reported repository-wide formatting differences, including untouched files; check mode changed no files. No broad formatting rewrite was applied.
- The focused HIR resolver test passed again after that update.
- Git checkpoint remains unavailable in this workspace: local `git add` cannot create `.git/index.lock` because `.git` is read-only, and the GitHub blob tool requires approval while the active approval policy is `never`. The verified files remain uncommitted in the worktree.

## Next evidence

Next, use the retained tuple target shape to join exact implementation `SourceNodeKey`s to member schedules without collapsing overrides into role defaults. For the authentic `pair.say` receiver, derive the ordered tuple's saturated element bounds, discharge the implementation's two `Display` where obligations against those element types without candidate trial typing, and prove when the match remains unique under every later legal bound. Then instantiate the exact Member graph at the use with one FreshUse and drain its nested obligations. Test a later receiver-bound change and independent uses.

No change to pinned Yulang2 bytes or effect semantics is authorized. Console remains independently blocked on the authenticated operator-use-to-value-owner candidate/runtime route introduced by R311. Neither sample execution nor any A/B, principality, termination, review or production gate is closed here.
