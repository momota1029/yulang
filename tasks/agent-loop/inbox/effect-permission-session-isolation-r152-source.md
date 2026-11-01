# R152 implementation handoff — same-session permission binding

Sprint: `EFFECT-PERMISSION-SESSION-ISOLATION/20261102-R152`, contract revision 1, SHA-256 `5fd4a9441a90be2b1201b179d8afb83c71ca2bbf4a8ca25c6f78e4da0d5bcc51`.
Assignment: implementation lane, handoff revision 1.
Parent: Simple-sub/effect hygiene and the session-owned source/native permission binding; original A/B, source/native, INITIAL-STATE, CONSUMER, soundness, principality and production gates remain open.

## Frozen inputs and baseline

- Committed baseline: `225c5519943fc490c3d5620683918674f4f6afd5`.
- Frozen input patch: `tasks/agent-loop/inbox/effect-permission-session-isolation-r152-input.patch`, SHA-256 `643d75e8e8435253a8606af7800134c28ce8eb74c86b1880ab169d5b8891bd1a` (matched before reconstruction).
- Baseline Rust file SHA-256s, independently recomputed from `git show <baseline>:<path>`: `candidate_effect.rs` `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`; `candidate_scheme.rs` `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814`; `shadow_apply.rs` `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278`.
- Exact governing sources read: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` (SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`); `notes/design/2026-10-11-yulang-inference-top-level-principles.md` (SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`); `rules/design-authority.md` (SHA-256 `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1`).

## Candidate

Artifact: `tasks/agent-loop/inbox/effect-permission-session-isolation-r152.patch`, SHA-256 `3a5a2f73b75cd3caaecae7fbb0f36c60b9c33492502fe531f3e7237fdb9838c4`, 115,801 bytes. It is an unapplied, reconstructed three-file candidate against the baseline blobs. The target files are `candidate_effect.rs`, `candidate_scheme.rs`, and `shadow_apply.rs`; no Rust working-tree file was read or written.

The central repair restores the prior `bind_native_formal_entry_permission_use(session, route_index, incidence_index)` shape. It fetches the route, module FreshUse map, store, registered formal, context origin and retained permission through that one `InferenceSession`. This removes the cross-session mix of route A with registration/effect-state B even when their source IDs and local numeric ordinals coincide.

The binder retains these source/native checks: unique context origin for the exact registration; origin and FreshUse Lambda occurrence equality; computation role; raw origin entry is an Effect row; registration and fresh incidence carry that same raw entry; original Function argument effect is a negative Effect live variable at the raw ordinal; one matching lambda recipe; the registered source owner resolves to local source; the exact source expression is a Lambda with the registered parameter; the captured route row's current representative agrees with the raw entry representative; the mapped row is Effect; and the mapped native Function argument effect is the expected negative live Effect variable at the mapped ordinal. Permission lookup still requires the exact registration, source owner, scope, occurrence, parameter, entry effect and nonempty concrete payload.

The single old predicate intentionally not reinstated is `registered.owner == Definition(route.provider)`. The route provider names the target definition, while a returned/local function's authentic constructor/source owner may differ. The candidate instead uses the session's registration-to-origin join, unique recipe and exact source HIR Lambda/parameter checks. This is not evidence that all returned/local cases are covered; it is the unresolved source-owner seam below. No blanket provider-equals-source-owner rule is introduced.

The input's raw `entry_effect` addition is retained through `LambdaArgumentEffectCapture`, `LambdaArgumentEffectFreshUse` and native incidence reconstruction. It remains distinct from the captured route row's current canonical representative and the FreshUse mapped row. This supports binding the permission to source raw identity while checking captured canonical transport and mapped native shape. No changes to permission origin, inference decisions, handler behavior or rollback ownership were introduced. Existing route-transaction rollback code is untouched.

The remaining changes are test-only trace/fixture instrumentation behind `cfg(test)`: typed source-constructor, effect-port, origin, memo/delegation, canonical-intern, captured-row, owner and export observations. The legacy same-`io` fixture still asserts equal sibling permissions; the separate fixture with distinct annotation operands asserts distinct permissions. These assertions are source-evidence probes, not accepted results. No test or source behavior was run. `candidate_receiver.rs` and quarantined runtime files were excluded; their separate deleted owner/batch/live-state, provider/arm and exact permission-origin checks are not part of this patch and are not authorized for restoration here.

## Source/native path and limits

The inspected path is: source `FormalAnnotation` action → `candidate_formal_annotation` and retained permission/origin in the owning session → `LambdaArgumentEffectCapture` with raw entry row and captured graph representative → module FreshUse route and row map → same-session binder → borrowed `FormalEntryPermissionUse`. The trace additions describe how a focused test could observe constructor input through canonical capture/export. They do not execute the test or establish that the full ordinary propagation/handler consumer path behaves correctly.

This packet therefore produces a candidate for one identity-boundary repair plus retained raw-entry evidence. It does not implement or verify source-to-constraints-to-propagation-to-handler execution end to end. No parent theorem or production gate follows from this candidate.

## Reused evidence and checks

Reused the R152 admission, the frozen input hash, and `tasks/agent-loop/history/unpushed-rust-solver-diff-20261102-audit.md` (SHA-256 `89459ef4639a93f3db7a936ba8ca4b49fe83dd48debf30d7a9612f425588f37c`): the audit identified the cross-session join and specifically warned against unconditional provider/source-owner equality. Read the R111 compile-repair handoff and R141/R142 snapshot source handoffs for owner, snapshot and transaction context; none proves this candidate's runtime behavior. The original source-owner, raw/canonical and mapped-term predicates were restored from the pinned baseline and compared against the frozen patch hunk.

Checks performed: frozen input SHA-256; committed baseline blob reads and all three baseline file SHA-256s; in-memory reconstruction of the frozen three-file candidate; exact output byte count and SHA-256. No patch application/check, formatter, build, test, Lean, compiler execution, scratch/cache/environment/worktree creation or Git mutation was performed. No expectations or diagnostics were changed to obtain green output.

## Open TODOs and provisional boundary

- `R152-SAME-SESSION-BINDER-SOURCE-NATIVE-1` — proof/source owner: use the exact constructor and FreshUse provenance to establish that route, registration, retained permission and FreshUse occurrence all originate in the one owning `InferenceSession`; falsifier: two sessions with equal IDs/ordinals can still be joined by any remaining caller.
- `R152-CONSTRUCTOR-OWNER-ROUTE-1` — source owner/Luna: trace returned/local function construction and route-provider identities to confirm the unique registration/origin/recipe/HIR Lambda path selects the authentic constructor owner without assuming provider equality; falsifier: a valid returned/local case lacks that join or an unrelated constructor can satisfy it.
- `R152-RECEIVER-OWNER-CHECKS-1` — primary/source owner: separately adjudicate the excluded `candidate_receiver.rs` owner/batch/live-state, provider/arm and permission-origin deletions before any wider integration. This handoff does not write that file.

Test-only instrumentation is explicitly provisional. Falsifier: an independent owner trace or focused test shows that recorded source identity, raw/canonical transport, permission origin, provider/arm distinction, or rollback boundary can be satisfied by a different construction/session. Cleanup owner: Luna after the frozen review and source-owner disposition; remove the instrumentation if it is not needed for the source-evidence gate.

## Runtime, budget and stop

Author `/root/r152_implementer`; requested model/effort `gpt-6-luna/high`; observed model/effort `UNKNOWN/UNKNOWN` in this worker context. No descendants. Authorized implementation budget: 900 seconds; no heavy process, compiler/test/Lean process, or scratch output was started. Exact leased outputs: this patch and this source handoff only; no other path changed. Writes are stopped. The candidate is frozen awaiting the assigned independent reviewer and Luna's adjudication; it is not approved or applied.
