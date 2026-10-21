# R205 — Source-Origin rows on the Capture fixture

The R205 targeted R187 readback passed once. Captured stdout SHA-256 is `708b36b6457a37a9f9e784911e5cfa59b3158e93236a56ec536b3352d3185e42`; stderr SHA-256 is `1f97b3d3e80b42218786e48198dc4a535de6065b00d050cc494b2a1f967b9efe`.

## Exact rows

- Relation 56, Effect(23) −≤ Effect(12), has Origin 31 at HIR occurrence 15, local slot 1. Its retained source-drain receipt has `created_seed=selected_relation=RelationId(56)`, no incoming relation or Replay ack, and task Effect(23) ≤ Effect(12). It has no direct source event ID in the relation source set. Its matching OwnerEmission admission 51 is processed on relation 56 and has no source event IDs there either.
- Relation 57, Effect(12) −≤ Effect(23), has Origin 32 at occurrence 15, local slot 2, with the analogous direct seed receipt and task Effect(12) ≤ Effect(23). Its matching OwnerEmission admission 52 is processed on relation 57; the direct event set is empty.
- Relation 62's OwnerEmission admission 55 is processed on relation 62 and carries event 1, mapped to checking occurrence 13, slot 0. No Origin row for relation 62 appeared in the readback.
- Relation 53 is still a FreshUse admission: antecedent snapshot 10, use origin 1, source key Effect(22) −≤ Effect(9), mapped relation 53; the captured physical key is Effect(29) −≤ Effect(9). No Origin row for relation 53 appeared.

The receipt struct's `completed` field remains false in the stored Origin snapshot. Completion is retained separately by `State::record_source_drain_completion` / `source_drain_completed`; R205 did not query that separate set. Therefore R205 establishes source-slot emission records for the two relation-56/57 bounds, but not completed-drain status, exact local source forms, or a full source-to-Capture/FreshUse chain.

## R183 application

This readback advances source generation beyond the R203 event-only view: two captured rows have exact Origin occurrences and local slots even though those relation source sets contain no event IDs. Thus an empty source-event vector is not absence of a source-origin record. Relation 62's event 1 remains a separate occurrence-13/slot-0 route. The rows are fixture-specific and do not prove same-provider preservation or a universal frontier law. The next discriminant is whether the two slot-1/2 drain receipts completed and which exact source expressions own occurrence 15; relation 53's FreshUse antecedent chain remains unresolved.
