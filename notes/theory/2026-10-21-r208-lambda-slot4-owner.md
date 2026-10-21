# R208 — A completed Lambda slot-4 bound outside the queried route rows

One targeted test passed. Captured stdout SHA-256: `10d6a2e39c5f8a991a8e61d08eb14d1949e7f2f25fc08f2604b293f18b82f90d`; stderr SHA-256: `1f97b3d3e80b42218786e48198dc4a535de6065b00d050cc494b2a1f967b9efe`.

The local Lambda at occurrence 12 has a completed Origin at slot 4, relation 71, for Effect(10) ≤ Effect(31). It joins admission 64 (`OwnerEmission`, processing relation 71) and emission 61. The physical owner is Effect(10), `EffectUpperRow`, index 0; readback matches the same bound and slot. The relation was not among the captured relation IDs reported for the route associated with Apply occurrence 18.

This does not yet establish an omitted source constraint from the same provider route: the queried route is looked up through Apply 18's callee, and R208 did not join that callee's `HirLocalId` to its binding initializer Lambda. Occurrence 12 may belong to the calling relay Lambda rather than the local provider whose Capture is being inspected. Therefore the `captured=false` field is only a relation-ID membership result for this one route query, not a source-qualified frontier counterexample.

The next required identification is the exact Apply 18 callee local binding, its initializer Lambda occurrence and slot 4, then the same route's capture-row ownership/locality for Effect(10) and Effect(31). R183 remains OPEN.
