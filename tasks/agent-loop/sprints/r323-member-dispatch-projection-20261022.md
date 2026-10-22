# Sprint R323 — project exact implementation members for FieldTail dispatch

Status: OPEN_CONTINUATION; source projection and solver consumption are separate owners, and neither end-to-end dispatch nor successful Types inference is reached.
Baseline: current uncommitted worktree on `research/simple-sub-intrusion`; preserve R320-R322 changes.
Authority: unchanged user goal: make original Yulang2 samples pass ordinary inference/execution and close the source/native proof path. No sample edits, expected-output edits, semantic weakening, quantifier changes, source-domain changes, or production promotion.
Dispatch: degraded solo primary because the user forbids subagents. Selector, independent prover, and review are unavailable; no agent is simulated.

## Bounded outcome

Build the smallest source-authenticated route that makes exact implementation override members available as candidate graph templates for a deferred FieldTail, then connect a uniquely selected graph through one FreshUse with shared receiver/result/effect rows. For Types, preserve the exact tuple `Display` target and both exact `Display int` / `Display str` prerequisites. Any incomplete inventory, unsupported target, ambiguous match, missing prerequisite, or reachable negative receiver bound must remain deferred. Preserve the contravariant `[io]` interpretation `[io,'e]`, under which `[state]` is allowed.

If the full consumer cannot be safely constructed in this sprint, identify the narrowest missing source/candidate constructor or solver owner and leave Types open. The bounded outcome is progress on the unchanged parent sample, not proof closure from code or tests. Preserve the corrected rule: contravariant `[io]` means `[io,'e]`, so `[state]` is allowed.

## Evidence and falsifiers

- R321 captured exact role-default `Display.say` in-session with nested `show` FieldTail rows in FreshUse layout; consumer `pair.say` stayed deferred.
- R322 traced the producer and found no solver consumer for FreshUse FieldTail row indices. Exact implementation override identities are inventoried, but their HIR is not projected into candidate schedules and no FieldTail dispatch connects the rows.
- Existing source projection API admits selected parse-owned member keys; candidate schedules already distinguish role-default and implementation member identities. Use those exact identities, never spelling fallback.
- Falsify with foreign/stale source keys, duplicate member schedule, ambiguous or incomplete applicable inventory, missing where evidence, inconsistent row sharing, negative bounds, or any change to sample text/output.

## Exact write leases

- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/module/local_source.rs` (R323 extension: exact qualified public value imports in selected member bodies)
- `crates/yu-hir/src/module/source_impl.rs`
- `crates/yu-hir/src/module/source_role.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/lib.rs`
- `tools/inference-playground/src/lib.rs`
- this contract, `notes/theory/2026-10-22-r323-member-dispatch-projection.md`, and `tasks/agent-loop/current.json`

All other paths are read-only. Entry SHA-256 values:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/shadow.rs` | `346ee2b98b3630257d5564128e02d27ae22a165ec0463ff5faf09dee3d511bf5` |
| `crates/yu-hir/src/module.rs` | `84e8032408bc40d5f69083dba70e4686fe5192006c6378b649815c5a6004b190` |
| `crates/yu-hir/src/module/local_source.rs` | `4aba5d90873e5669f9e58498e88237a923240eafca5fe32e39c9376f6f435350` |
| `crates/yu-hir/src/module/source_impl.rs` | `d46486e9f6c3a9a62f05f46323422a2cc9d4cd23837172457d5a11f4984a929f` |
| `crates/yu-hir/src/module/source_role.rs` | `d16945ae153d25cdadea9e9071cdfc2ab73925b46d92e598a0e18e5d60f4d3e3` |
| `crates/yu-solver/src/candidate_scheme.rs` | `651be259f6a113de2611db190a9de2ef11328d296714579aa48b3dd99968da70` |
| `crates/yu-solver/src/candidate_source.rs` | `052f291acd7f33af9736663ccc38c01cfde0dda7433cff7a0d6fab04767babfb` |
| `crates/yu-solver/src/shadow_apply.rs` | `967ef6fe3642fde7393f17d75349df9600f40da536fe7d288eb6e104e9bd7bcb` |
| `crates/yu-solver/src/lib.rs` | `8ae99bf187bf1c7a8ee69795fa5b7fea752e6c648073c10dc7609a4c0e668910` |
| `tools/inference-playground/src/lib.rs` | `aa8a72b82a3fb29c31482c895a18b044cdb6a27735513b66a99ee41fb00873bd` |

## R323 receipt

Implemented exact source-world member projection, applicable override-body projection, provider deduplication, prefix-application target shapes, and a solver consumer that maps active FieldTail interfaces through one retained FreshUse and admits receiver/result/effect constraints. The unchanged pinned Types readback now captures four exact member graphs: `Display.say`, tuple `Display.show`, and the `int`/`str` prerequisite overrides. The pinned member readback and explicit deferred-boundary tests pass after updating the obsolete two-graph expectation. Types still does not infer successfully: consuming operator-provider FieldTails activates `x.add` from the generic standard-library `+` template while its receiver has no positive shape. That abstract constraint must survive in the operator scheme until the provider is instantiated in a context that supplies receiver evidence. Eagerly selecting it here is incomplete; dropping it would lose a source constraint. The source projection and consumer are implementation evidence only. No independent review, source/native proof, theorem closure, or production admission is claimed.

## Lane and stop boundary

Solo source/proof trace and implementation remain one primary lane; do not self-certify or label it independent review. Preserve exact source owners and apply every construction result back to the unchanged Types consumer. Continue to the bounded dispatch consumer or record the exact next obstruction. Keep source/native A/B, later-bound stability, Console, R149, remaining samples, theorem closure, and production gates OPEN unless separately discharged by their own evidence.

Cap 2400 seconds, no carryover; one heavyweight process at a time. Do not add or run tests in this sprint unless the user asks for verification. Record commits as unavailable if `.git` remains unwritable; never claim an unmade commit.
