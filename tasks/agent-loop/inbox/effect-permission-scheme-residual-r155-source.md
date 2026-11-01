# R155 implementation handoff — scheme residual audit

Sprint / contract: `EFFECT-PERMISSION-SCHEME-RESIDUAL/20261102-R155`, revision 1, SHA-256 `1fb5c38fb14f6f11c1ac8d26930168f2b7bf0422948e4f79c0fcd3b916bd1309`.

Assignment: R155 implementation lane, handoff revision 1. Parent remains the original Simple-sub/effect-hygiene obligation, source/native correspondence, original A/B and production; all remain OPEN. Baseline: `1dbb738de8af1b186ae56ca347e591ae0a1b3d83`. Frozen input patch SHA-256: `6ffdb7fda9f822a40024498160eedcac4cc6950ebc4b7bf93548e497b296664f`.

Requested model/effort: Luna/high. Observed model/effort and active-time telemetry: UNKNOWN. No descendants. Exact output leases: this handoff and `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155.patch`. Claim class: source evidence / HOLD / NO_PATCH. No compiler, Cargo, test, Lean, patch application, source edit, Git mutation, scratch, cache, environment, checkout or worktree operation was performed.

## Pinned source identity

The frozen input and selected contract hashes matched. The committed baseline blobs were read only through `git show`; their SHA-256 values match the R155 contract:

| Baseline Rust blob | SHA-256 |
| --- | --- |
| `candidate_scheme.rs` | `bc99466ff65d716c28295a0ab3ef2d50b1aef81c437bfcbac6ea4b79450a6ff2` |
| `candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `candidate_receiver.rs` | `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165` |
| `candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |

No live dirty `candidate_scheme.rs` or `candidate_receiver.rs`, nor quarantined runtime path, was read. The input contains one function replacement hunk. Its target working-tree hash from the contract was not independently read or checked.

## Hunk classification and evidence

**The same-session binder already integrated:** the baseline at `candidate_scheme.rs` has the reviewed R152/R153 API `bind_native_formal_entry_permission_use(session, route_index, incidence_index)`. It obtains route, native terms, batch registrations, context origins, canonical effect state and the retained permission from one `InferenceSession`. It verifies the unique registration-labeled origin and exact Lambda occurrence; computation role and raw entry; original Function's negative Effect entry ordinal; unique recipe and source HIR Lambda/parameter; current canonical representative versus the captured graph row; and the mapped native argument-effect ordinal. It then calls the lower `candidate_effect::State` binder. R152 review `tasks/agent-loop/history/effect-permission-session-isolation-20261102-r152-review.md` (SHA-256 `06d4aef333b67986454ce234a7a57c335549394c5b5fb90ab6a1e6f150ac2914`) passed this exact candidate as an unapplied research candidate. R153's separate integration-authority review `tasks/agent-loop/history/effect-permission-session-isolation-20261102-r153-integration.md` (SHA-256 `30b9e143ad6e51e84e60f9c955d334d526bea07b3bc8f00334400f1b624fa1c7`) authorized and reviewed only the exact R152 patch, whose scheme source is already in this baseline.

**Replacement adapter: HOLD.** The hunk deletes the session-owned wrapper and accepts independent `route`, `store`, `effect_state`, `registration`, `registered_formals` and `occurrence` arguments. It retains local equalities for incidence registration/Lambda/use/context and forwards incidence entry/mapped rows to the lower binder. Those equalities do not authenticate that the route, store, effect state, registration table and occurrence belong to one session, nor re-establish the deleted context-origin, source-recipe/HIR and canonical-representative joins. The lower State binder checks the supplied registration against a retained permission and verifies role, entry, owner, scope, parameter, occurrence and nonempty payload; it has no route/session argument and cannot repair the outer ownership gap. No committed caller or independent source-owner evidence justifies these separately supplied identities. Equal numeric registration/row ordinals across sessions remain insufficient.

The existing identity spaces must stay distinct: formal registration labels the permission; packed permission-vector position and native selected/member ordinal are separate coordinates. Raw source entry effect, captured canonical graph row and FreshUse mapped row also remain separate. The candidate's exact incidence fields do not demonstrate identity merely because their numbers or local labels match. I made no claim that `route.use_id`, provider identity and source constructor owner are interchangeable.

No nonempty independently justified change remains against this baseline. **Disposition: `NO_PATCH`.** The exact no-patch marker is in the companion `.patch` lease. It must not be applied. R153's narrow review is not authority for this distinct residual diff.

## Source/native boundary, prior evidence and limits

The inspected baseline path retains Capture/FreshUse incidence provenance and reaches a same-session read-only binder that returns a borrowed `FormalEntryPermissionUse`. This is not an implementation of source → constraints → propagation → consumer/execution: the binder is explicitly provisional, adds no constraints or propagation, and has no consumer here. R152/R153 evidence supports the same-session boundary only for its exact reviewed version. R154's receiver audit is separate and does not restore or authorize this scheme replacement.

No end-to-end behavior was achieved by this audit. No executable falsifier was run. A concrete falsifier for the input adapter is two sessions with colliding local registration, occurrence, row and use ordinals: a caller may pair one session's route/store with another session's effect state/registration table, and the adapter has no common session object to reject that combination. This identifies the ownership hole; it is not a runtime counterexample observed by execution.

Compilation, tests, runtime reachability, source/native theorem correspondence, INITIAL-STATE, CONSUMER, effect hygiene, soundness, principality, termination, original A/B and production remain OPEN. No expectation, diagnostic, source domain or inference behavior was changed. No provisional instrumentation was added.

## Checks, resources and stop

Checks: hash-verified the R155 contract and frozen input; independently hashed all seven pinned committed Rust blobs; read the exact committed scheme/effect binder and reviewed R152/R153/R154 handoff evidence. No tests/builds/Lean or other executable check ran, as forbidden. Actual active time and CPU/RSS are UNKNOWN; assignment ceiling was 600 seconds. No new scratch/generated/disposable path was created. Exact outputs are the source handoff and NO_PATCH marker only. Writes are stopped; no descendant leases remain.

Next related in-envelope step: Luna can adjudicate this HOLD/NO_PATCH result alongside the independent R155 proof map. Any different source edit or integration needs a new exact lease and independent review; this handoff grants neither.
