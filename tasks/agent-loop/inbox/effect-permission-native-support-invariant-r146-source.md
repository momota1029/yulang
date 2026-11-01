# R146 source handoff — native support invariant

## Frozen assignment receipt

- Sprint: `R146 — native incoming state and allocator invariant`; contract SHA-256 `126a5703a73fff6ee5312f7a52e7c46682755728855edf4d27cdb9b4851615a9`.
- Assignment / handoff: `effect-permission-native-support-invariant-r146-source`, revision 1.
- Parent gate: R145 source application; original Simple-sub A/B and production gates remain OPEN.
- Baseline: `3560df97dab02744da10e897c73c1cf94118f4ee`.
- Requested role/model/effort: Luna/high. Observed model/effort: UNKNOWN in visible runtime metadata. Worker: `/root/r146_native_support_source`; assignment execution is the current-session receipt, with no additional runtime identity exposed.
- Sole leased output: this file. No source, build, test, proof, scratch, cache, environment, checkout, or worktree outputs were created.
- Frozen source blob SHA-256s (computed from `git show BASELINE:path`):
  - `candidate_source.rs`: `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
  - `candidate_context.rs`: `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`
  - `candidate_scheme.rs`: `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814`
  - `candidate_scope.rs`: `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`
  - `candidate_intrusion.rs`: `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
  - `shadow_apply.rs`: `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278`
  - `lib.rs`: `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`
  - reused R145 source handoff: `e543b1cd4c6d98d6fdaf912f228a8cd53e407fe72edf3338b2f1c9fca295ffba`
  - governing compose note `notes/design/2026-10-15-compose-scoped-effect-release.md`: `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679`
- Checks / resource budget: no builds, tests, Rust/Cargo, Lean/Lake, or runtime executions by contract. Source lane stopped within its 600-second limit. No checks were run.

## Result

The committed producer/propagator chain supports the claim that every scope/input coordinate in a transformer or demand entering successful `prepare_candidate_fresh_use` is below the corresponding pre-copy `ScopeInventory` length. I found no reachable production counterexample. This is a source-level inductive reconstruction, not an executable invariant check or proof of the full native theorem.

The earliest owner is the source allocator plus `ScopedFlow` constructors/propagators, rather than a downstream FreshUse map repair. Initial source IDs and every later copied ID are allocated from contiguous append indices; all observed production flow constructors either introduce those source IDs, preserve them, compose their supports without inventing IDs, or map them into a later append interval.

## Producer-to-consumer trace

1. **Initial scope inventory and IDs.** `Plan::computation_scope` allocates `EffectScopeId(scope_regions.len())`, appends the matching source region, and records the ID in that region (`candidate_source.rs:155-170`). For scoped applications, source collection sets `source_input = candidate_calls.calls.len()`, creates `InputRouteId(source_input)`, and records it exactly once in the owning region (`candidate_source.rs:1870-1894`). `ScopeInventory::from_plan` initializes `scope_origins` to `plan.scope_regions.len()` and `input_origins` to the sum of region input counts, with initial IDs `0..count` (`candidate_source.rs:223-245`). Thus source-produced IDs are below their initial inventory lengths; input route assignment and ownership use the same call index.
2. **Initial demand and release.** `candidate_context_seed` constructs demand only for a source call introduction: `output_scope` comes from that occurrence's `computation_scopes`, and `input` is the call index (`candidate_context.rs:3793-3838`). The release path obtains the argument occurrence's computation scope and constructs `ScopeTransformer::release(scope)` (`candidate_context.rs:3824-3833`). Both coordinates therefore come from the same initial Plan namespaces above.
3. **FunctionPort conversion.** A demand-bearing negative function parent is validated against its root, then `ArgumentEffect` converts its input to `stamp_input(demand.input)` and `ResultEffect` converts its scope/input to `protect_body(demand.output_scope, demand.input)`; value ports carry no scope transformer (`candidate_context.rs:3924-3987`). This conversion copies only existing demand coordinates.
4. **Other relation propagation.** Tuple, record and variant ports preserve the parent flow (`candidate_context.rs:3991-4083`). Equality canonicalization, bound payload, and ordinary transport paths copy the current flow; the explicit transport witness path changes a demand root only (`candidate_context.rs:3286-3297, 4188-4203, 4335-4355, 4650-4668, 4729-4775`). They do not create scope/input IDs.
5. **Replay and compose.** Replay rejects a lower demand, composes the lower then upper transformers, and carries the upper demand (`candidate_context.rs:4455-4476`). `ScopeTransformer::then` computes finite unions and per-scope conditions from existing supports; it does not allocate IDs (`candidate_scope.rs:131-176`). The authoritative compose decision requires preserving attribution and independent protection; this code trace alone does not establish that semantic contract or its full source realization (`notes/design/2026-10-15-compose-scoped-effect-release.md`).
6. **FreshUse copy and replay.** `ScopeInventory::owned` deduplicates root/child regions in its closure (`candidate_source.rs:272-295`). `fresh` reads the existing region-owned scope/input lists, chooses each new ID from the current `scope_regions.len()` / `input_regions.len()`, appends it, and records the old-to-new map (`candidate_source.rs:296-357`). `prepare_candidate_fresh_use` calls this before reconstructing bounds (`candidate_scheme.rs:4444-4451`); it remaps each incoming transformer and demand using that one map, with identity fallback for support outside this particular copy domain (`candidate_scheme.rs:4773-4800`). Any fallback coordinate remains below the old inventory length. Any mapped coordinate is in the new append interval, hence above all pre-copy IDs. The shared old-to-new map is injective on the union of copied keys; identity keys lie below the cut and mapped images lie above it. Captured bounds consume the retained per-parent flow and do not allocate a second scope map (`candidate_scheme.rs:4861-4907`). The other production preparation caller is local FreshUse; module calls through the same `freshen_candidate_graph_core` path (`candidate_scheme.rs:4423-4443, 5214-5223`, as also traced in R145).
7. **Failures and rollback.** `ScopeInventory` is not present in `candidate_context::Checkpoint`; effect-algebra rollback restores context-owned records, while the inventory's successful or partially appended ID arrays remain monotone (`candidate_context.rs:2182-2245`, `candidate_intrusion.rs:177-250`). `fresh` reserves the aggregate ID vectors before copying and appends a scope/input ID and its origin/region entry as paired operations; an error can leave earlier appended IDs and can return no completed map (`candidate_source.rs:296-357`). This can consume unused IDs, but the still-published flows are older values and later allocations use larger lengths. I found no path that rolls the inventory back and reuses a coordinate. This does not authenticate complete failure atomicity or use-instance rollback.

## Native correspondence boundary

The source bridge still lacks an authenticated real state argument corresponding to `NativeScopeTransformer.State`, and the source handoff does not show a state-side rename by the FreshUse map. `candidate_context::evaluate_observation` evaluates only the relation's transformer over empty initial input/protection slices (`candidate_context.rs:3280-3284`). Its `shadow_apply` exposure is an opt-in experiment observation (`shadow_apply.rs:1641-1654`), and its only direct internal consumer found by baseline-qualified search is a context test (`candidate_context_tests.rs:6284`). It is therefore not evidence for the real incoming state. This task did not inspect Lean source and does not close the separate state-correspondence packet.

## Reused evidence, exclusions, and TODO

R145's conditional source trace is reused for one-map FreshUse mechanics, identity fallback, callers, and the initial TODO. Its accepted review explicitly left global support/allocator and authentic incoming-state correspondence open. I independently rederived the allocator side against R146's baseline, including source input allocation, relation-flow producers, composition, copies, and rollback. I did not use R145's origin-equality discussion as an injectivity premise. No source-qualified counterexample was found. No R145 unchecked Lean candidate, tests, empty-state observer, or conditional result is treated as theorem closure.

The source trace supports the global below-pre-copy-cut invariant by construction. Keep source/native state correspondence and the full theorem OPEN: the authentic incoming state and whether it is transported under the same map remain owned by the R146 proof/source-state lane. The source producer argument has not received independent review and cannot self-certify.

Mutual TODO for the proof/state lane: identify the authentic incoming native state at the source consumer and establish whether all of its relevant scope/input support is already represented among the source `ScopedFlow` support and transported by the same FreshUse map. Do not identify empty observer input, transformer prefix, demand, or `use_instance` with `State` without evidence. Falsifier: a reachable production consumer state with any relevant coordinate omitted from the captured flow/map or not renamed by that map.

## Boundary, stop, and next step

This handoff is source-native evidence only. No code or expectations changed; no tests or diagnostics were changed. There are no disposable scratch paths. The only new path authored by this worker is this leased handoff. All Rust reads were baseline-qualified immutable Git blob reads; working-tree Rust sources were not inspected. Writer stopped after freezing this revision; there are no descendant workers or generated outputs. Independent review is still required.

Next related in-envelope step: independent reviewer rederives this source invariant from the frozen baseline, then Luna combines it with the proof/state lane's authentic-consumer result. A conditional source argument does not authorize cutover, production repair, or parent theorem closure.
