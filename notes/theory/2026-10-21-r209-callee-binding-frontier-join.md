# R209 — Exact callee Lambda slot-4 join

The targeted test passed once. Captured stdout SHA-256: `54edcee64779392b2bcc81b01ed2a1d638be4b54da775fb9f9bafe947b75fbab`; stderr SHA-256: `1f97b3d3e80b42218786e48198dc4a535de6065b00d050cc494b2a1f967b9efe`.

Apply occurrence 18 resolves through the exact local `HirLocalId` to binding `relay`, whose initializer is the Lambda at occurrence 12. Its slot-4 Origin 38 is relation 71, with completed direct-seed receipt for Effect(10) ≤ Effect(31). The exact OwnerEmission admission 64 and emission 61 match the physical key; the physical owner is Effect(10), upper-row lane index 0.

This source bound is absent from the same `relay` local route's set of captured relation IDs. Its Capture row snapshot contains Effect(31) requested/representative at level 2, boundary 1, `non_generic=false`, `local=true`; no Effect(10) row appears in the route's captured row observations. This is an actual source-emitted mixed-age frontier shape in the R187 fixture: the Lambda slot-4 source owner is not itself an enumerated Capture fiber, while the other endpoint is a local Capture row.

The result is not yet a source-qualified counterexample to R183. The readback does not identify the precise Function child endpoints and fresh-image mapping for this route, nor exclude another authentic shared-anchor or transport path joining the same mapped endpoints. Relation 71 has `sources=None`; the direct Origin receipt, not the relation event set, authenticates its source slot. R210 will inspect the route's actual graph and row map around Effect(10)/Effect(31). R183 stays OPEN.
