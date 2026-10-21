# R206 — Completed Name origins in the R187 Capture route

The one targeted R206 invocation passed. Captured stdout SHA-256: `627b2734ef21dd98adae03f9afd6a5650cc4cb13db0d4f5535b98792ea2a98ee`; stderr SHA-256: `1f97b3d3e80b42218786e48198dc4a535de6065b00d050cc494b2a1f967b9efe`.

The HIR local expression at occurrence 15 is `Name { spelling: "u", resolution: Parameter(HirParameterId { ordinal: 2 }) }`. Its exact Origin rows are:

| Relation | Bound | Origin / source slot | Drain completed |
|---:|---|---|---|
| 56 | Effect(23) −≤ Effect(12) | Origin 31, occurrence 15 slot 1 | true |
| 57 | Effect(12) −≤ Effect(23) | Origin 32, occurrence 15 slot 2 | true |

Both are direct seed receipts (`incoming_relation=None`, no Replay ack, created and selected relation equal their relation) and each bound joins the existing matching OwnerEmission and physical readback. Their relation source-event sets remain empty. The completed Origin records therefore authenticate these two source Name slots more precisely than the event-set field alone.

Relation 62 separately carries event 1 for occurrence 13 slot 0. Relation 53 remains a FreshUse row from antecedent snapshot 10 and source key Effect(22) −≤ Effect(9) to captured key Effect(29) −≤ Effect(9), with the provenance gaps decoded in R204.

This confirms two emitted, completed Name-slot bounds in the fixture's Capture rows. It does not identify the required Lambda slot 4 or establish every original Name/Lambda edge, the same provider/use's complete mapped endpoint path, or R183's universal source-generated frontier law. The next exact readback is the full Capture snapshot-to-Origin join for the relevant source slots, including slot 4.
