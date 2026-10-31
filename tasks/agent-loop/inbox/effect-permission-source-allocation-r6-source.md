# R6 read-only source handoff — EFFECT-PERMISSION-SOURCE-ALLOCATION/20261029-r6

Owner: Luna. This lane used source inspection only; no Cargo, compiler, test,
instrumentation, formatter, or Lean command ran. No source file changed.

## Pinned owners

- `crates/yu-solver/src/candidate_effect.rs`: SHA-256
  `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`.
- `crates/yu-solver/src/lib.rs`: SHA-256
  `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.
- R5 decoder module: SHA-256
  `ea97baf7c98becef27df9e0c416d8d5fb00e9e1b5b63f37021b01598231936dc`.

The manifest pins these source owners and their transitive project dependencies.

## Constructor/helper correspondence

| Source | Successful-path behavior in selected fragment | Remaining boundary |
|---|---|---|
| `candidate_effect.rs:1604–1614` `candidate_formal_pair` | Rejects unsupported row shapes, then delegates to `candidate_formal_value_pair`. | Rejection/error paths are outside a successful-return footprint. |
| `candidate_effect.rs:1617–1691` `candidate_formal_value_pair` | Int/Unit atom branches return collected leaves. Tuple rejects empty tuples and elements with row effects, samples resources, then visits children in index order. Function visits argument value at reversed variance, result value at current variance, then argument and result ports in that order; function terms are built after child/port results. | The selected fragment excludes variables, holes, unsupported atom constructors and tuple guards that fail. Resource/term helpers can fail; conclusions concern successful return only. |
| `candidate_effect.rs:1694–1744` `candidate_formal_effect_port` | Omitted ports and negative nonempty concrete rows without variables each call `fresh_effect_at_level` once. The latter copies the current path, source row and concrete operands, then appends a `FormalPermission` with the exact parameter, occurrence, owner and scope. | The positive-concrete and variable cases are outside this fragment. Allocation happens before later permission-memory reservations; an error after allocation is not claimed to roll the allocator back. |
| `lib.rs:10487–10517` `fresh_effect_at_level` | Reads `u32::try_from(effect_bounds.len())` before reservations. The route-reservation wrapper reserves one slot in `effect_bounds`, `effect_levels`, `effect_metadata`, and `extrusion_effect_marks`. After all reservations succeed, it pushes one entry into each and returns the pre-push ordinal. | A failed reservation can change capacities and return before pushes. The packet proves only successful transitions. Parallel-vector invariants and helper execution remain explicit source-to-transcription obligations. |
| `lib.rs:75–168`, `9088–9125`, `9253–9265` | `F5bReservable` for `Vec` delegates to `try_reserve`; `reserve_f5b` maps reservation errors and has test-only failure injection; the route macro observes capacities and calls `observe_typed_route_capacity`. On successful return those helper steps do not append to `effect_bounds`. | Resource sampling may fail after capacity growth; test-only probe behavior is not executed or needed for the no-test source lane. |
| `lib.rs:10566–10620`, `10774–10830` | Function term helpers use `store.terms`; resource sampling observes resource/term/store snapshots. These paths do not directly call `fresh_effect_at_level`. | Full frame facts for all transitive helpers are mathematical transcription obligations, not established by this table. |

## Ordered footprint and exact cut

For the checked R5 tree, tuple traversal reaches the first Function, then its
argument value and result value, then its argument Effect port and result
Effect port. The nested Tuple is visited in child order and contributes no
additional port for its Int leaf; its second Function contributes the same
four-position local order, with only its two Effect ports allocating. Thus the
selected four calls are omitted argument, negative-concrete result, omitted
argument, negative-concrete result. This agrees with R5's source projection
and `orderedPorts` recurrence.

At the selected cut—return from `candidate_formal_value_pair`—successful
fresh calls append one effect row each and return the successive pre-push
`effect_bounds` lengths. Exact negative-concrete permissions are appended in
the same source order. This does **not** extend to the enclosing
`candidate_formal_annotation`, which later admits links and may propagate
constraints or allocate other rows. In particular, no global native entry
counter or authentic runtime trace is observed; the R5 base 21 remains a
bounded instance premise until a separate native bridge proves it.

No fully general helper frame theorem follows merely from these source reads.
The Lean lane must expose the exact transition model and unresolved Rust
execution correspondence rather than hide it in an assumption called native
execution. No tests or execution receipts are part of this handoff.
