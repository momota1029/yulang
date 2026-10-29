# R27 Rust preflight review, rejected candidate r1

## Receipt

- Reviewer: `/root/effect_permission_owner_certificate_r27_rust_preflight`
- Result: **REJECT**, limited to pre-execution Rust source review.
- Review window: 2026-10-29 21:14:35–21:16:28 UTC; charged 130/1,000 seconds, 870 seconds remain.
- Effective model and effort: UNKNOWN.
- Scope: read-only. No Git, edits, Cargo/rustc, build, test, runtime, Lean/Lake or descendants.
- No candidate execution is authorized. Lean remains unchecked and the combined R27 contract remains OPEN.

## Authenticated inputs

All supplied pins matched during review:

| Input | SHA-256 |
|---|---|
| `machine.rs` | `24d68fa0f54e9f338188da49a96e72f413238dd70f72537da8040b6c1ee73078` |
| `receiving.rs` | `7a8eeab787f127064d5689b1ee5fbbfc409b4a307905d0f42d538f5d3d628f25` |
| schema r2 | `84187379d1a81b1965c34c027e7532198bebc4c4110eaa1c05808bada6bf6d8c` |
| inputs r3 | `06fcdb4292b3364b9a40b75dcb9b57419ff0bfb50628d422cd5ec69ad0e5c6bc` |
| contract r1 | `2cc9c8ae08a6fcbf98f237e6a1640ceb042a456a6beaadc448fa0a0308b431f0` |
| amendment 02 | `b625cb42fc9f7e365c0df738bb8b7a269775acdd34f9cc4e1d6e8155a6400bad` |
| Rust handoff | `dedc38b32eb43e51edac968f27aaf7fa02b89f2a70b425b9d4a83fe164e910d3` |

Direct dependencies `continuation.rs`, `program.rs`, `main.rs`, the selected fixture and `Cargo.lock` also matched the manifest. Both companion baseline capture hashes matched. Review began with source and governing inputs before consulting the implementer explanation.

## Findings

1. **BLOCKING — the callback test selects a missing definition.**

   `machine.rs:3875–3877` passes the approved callback, whose binding is `answer`, to `machine()`. Its `start()` helper unconditionally calls `definition_named("main").unwrap()` at `3444–3451`. `program.rs:487–495` returns `MissingDefinition` when that binding is absent. The focused test therefore panics before callback execution, companion validation, mutations or receipt generation.

   This violates contract success items 1 and 4 and the fixed callback route in inputs r3. Minimum repair: use the actual definition-selection API to select `answer` for the callback while preserving its approved source and expectation.

2. **Major — replay-to-consumer lineage is historical membership, not a causal join.**

   `machine.rs:2661–2663` labels every earlier replay as consumer lineage. At `3914–3915`, capture association checks only `contains(capture.template_handle)`. `validate_outer_projection` at `3615–3638` does not check a replay coordinate, capture event, template handle or actual connection from that replay to this request.

   Counterexample: template A is replayed and finishes; a later unrelated write reaches a consumer. A remains in history, so membership passes. Removing or changing `lineage_templates` also does not affect the outer validator. The changed-owner mutation at `3984–3998` does not test this missing connection.

   This violates schema r2 `request_consumer.rule` and contract success item 3. Minimum repair: retain the causal association at request/replay owners, validate it with the projections, and mutate an existing causal link while keeping consumer ownership otherwise valid.

3. **Major — the frame snapshot is taken after forwarding consumes relevant boundaries.**

   `machine.rs:2664` snapshots `self.frames` only when the Catch consumer is selected. Forwarding already popped frames, restored owner state and moved boundaries into this request's `suffix` at `2766–2802`; the replay's `OwnerReturn` becomes a saved boundary at `2775–2788`. That request suffix is absent from the certificate.

   The projection at `3533` onward describes the original captured signal template, not the later write's accumulated suffix. Residual stack adjacency therefore does not authenticate the replay-to-write path. Requiring an `owner_return` somewhere in the remaining stack at `3630–3634` or `3922–3923` cannot restore consumed transition evidence.

   This violates schema r2 `frame_projection.rule` and contract success item 3. Minimum repair: capture the relevant boundary projection before forwarding consumes it, or record ordered forwarding transitions with source-derived endpoints and owner restoration; join those records to the saved template and actual consumer. Do not substitute unrelated same-kind frames.

4. **Minor — an observation-only lookup is not test-only.**

   `machine.rs:2253–2257` reads `capture_root_index` unconditionally, although its only use at `2332–2345` is a test-only observation. It enters ordinary builds and creates an unused local. Put the lookup behind `cfg(test)`.

## Correctly addressed and still outstanding

The immutable owner lookup/root validation checks actual template lookup, root equality, final appended position, Owner variant, predecessor edge and containing owner. Five mutation implementations have explicit target/change checks, but none ran; the callback panic prevents reaching them.

Unchecked Lean is not a material dependency for this narrowly separated Rust preflight; it remains material to the combined R27 contract. No theorem, axiom audit, combined-contract completion, source/native closure, parent theorem or production readiness is certified.

After repaired source receives fresh exact-hash ACCEPT and separate primary stage authorization, execution must still establish compilation, unchanged callback/companion results `1`/`23`, actual applicable mutation targets and rejection for all five mutations, and authenticated schema-conforming JSON with replay, complete boundary transitions and receiving observations. Do not fabricate the absent JSON. Callback raw stderr/resource capture remains unavailable.
