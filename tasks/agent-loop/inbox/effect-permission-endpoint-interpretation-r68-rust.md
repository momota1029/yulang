# R68 Rust handoff — checked SemanticFact endpoint interpretation

Sprint `EFFECT-PERMISSION-ENDPOINT-INTERPRETATION/20261031-R68`, contract
revision 1, SHA-256
`d726bf518b1377fabb282a078a067df257b0e0f164d0b05db0fe5c1273cdc5ab`.
Assignment `/root/r68_rust`, handoff revision 2. Revision 2 repairs the
blocking R68 rev1 review finding: selected reads no longer borrow the local
`interpreted_facts` vector created during `internal_root_view`.

## Parent, runtime, and leases

Parent: the unchanged Simple-sub/effect-hygiene obligation and source domain.
This is an owner-local implementation result; it does not close the original
A/B theorem, promote production, or change accepted semantics.

Requested role/model/effort: implementer, `gpt-6-luna` / high. Effective model,
effort, launch receipt, elapsed assignment time, and remaining assignment time
were not exposed in this child runtime and remain UNKNOWN. No descendants.
Exact write leases: `crates/yu-solver/src/candidate_receiver.rs` and this file.

## Inputs and reused evidence

The contract and direct source/proof inputs were rehashed before editing and at
freeze; all frozen input pins matched:

- Sprint contract: `d726bf518b1377fabb282a078a067df257b0e0f164d0b05db0fe5c1273cdc5ab`.
- `candidate_receiver.rs` pre-edit: `f5e7a845cb650b309ff36face7ba44ab2b48e828db67221637c3015f9881658c`.
- `lib.rs`: `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`.
- `candidate_context.rs`: `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`.
- `yu-hir/src/module.rs`: `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`.
- `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`.
- R65 `OccurrenceQualifiedFactReadersR65.lean`:
  `3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b`.
- R66 `OccurrenceQualifiedConsumerR66.lean`:
  `5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1`.
- R67 `BorrowedQualifiedReadReificationR67.lean`:
  `4b40cc5f1e832eaac226235d7c9c8a974bd3c6b895fa2d9fab7051d3271ee4e1`.
- R67 Rust handoff: `8823793be5826d6ae865479a9921f22964c11df3630ece2016bf5c5798d1e72f`.
- R67 proof handoff:
  `ee4bc812c85e76de7ee1aa673e89471e3c6eb5ce57d1787ca94e590059d4850f`.
- R67 review: `9f2dfe25a1566d99fbcaf818588c89a95a5e8a931710cc2b1bce0628198d883b`.
- R67 outcome: `f49d599f73fc8dbe80a7de64a28f13eabfea57d65b7bf28c7dfbd51716df9903`.
- Inference principles: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Effect-hygiene integration: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.

Reused R67's complete owner-ordered semantic-fact and provenance tables,
occurrence/slot coordinates, edge-to-fact resolution, and selected R66
slot-0 Internal / slot-2 Lambda rows. R67 correctly left endpoint projection
open because its records retained Terms without interpreting them. This packet
adds that projection from the actual borrowed Terms and their same owning
`InferenceSession`; it does not reuse or restore any Simple-sub bypass.

## Implementation and source correspondence

`InventoryPackage::reify_qualified_facts` now creates one
`InventoryReifiedFact` per owner `SemanticFact`, in existing fact-table order.
For every fact it retains id, Term handles and four tagged endpoint values:
raw lower with positive polarity, current-session canonical lower, raw upper
with negative polarity, and current-session canonical upper. The
`InventorySemanticEndpoint::{Value, Effect}` tag preserves namespace even
when row ordinals match. Every provenance edge remains a separate row with
its original index, occurrence, slot, fact index and identity, including
repeated FactIds. Each selected R66 occurrence fact owns a copy of the matching
`InventoryReifiedFact` record. That copied record preserves all four endpoint
values, the fact index and identity, and a pointer to the same owner
`SemanticFact`; `source_fact_at` checks the pointer and endpoint Terms before
return. No selected-read field borrows the local reification vector.

The exhaustive decoder reads `TermView` from this same session store. It
preserves primitive leaf and extreme tags; maps effect bottom and empty-effect
leaves in the effect namespace; maps Function, Record, Tuple and Variant views
to value endpoints while preserving their exact Term handles and tuple arity;
and checks live-variable polarity. Component views use checked component-term
position, component and Term round-trips, checked live-component position,
kind and live row. Every raw row and the resulting representative row is
checked against its current value/effect bounds table before use. Allocation
and checked integer conversions retain `SearchLimit`; foreign Terms,
unsupported views, invalid coordinates and row/polarity/kind mismatches return
the existing private `BoundMismatch` gap.

This feeds a complete SemanticFact/provenance interpretation into the R67
qualified lookup and R66 selected-row read view. It remains private candidate
source/native evidence: it does not alter ordinary inference, constraint
generation, propagation, permission routing/consumption, or native execution.
Full source/native correspondence and parent theorem status remain OPEN pending
independent review and the proof composition.

Exact open cross-lane request: `R68-RUST-FACT-ENDPOINT-INTERPRETATION-1`.
Proof owner: `/root/r68_proof`. Use the Rust branch rules and tagged endpoint
coordinates above for the finite Lean interpretation, prove branch/coordinate
and canonicalization equations, then compose with the existing R67 lookup and
R66 selected-read witnesses. Keep source correspondence OPEN if any equation
or constructor match is not established; this request grants no additional
source or proof lease.

## Checks, boundaries, and next step

- Source paths changed: `crates/yu-solver/src/candidate_receiver.rs` and this
  handoff only.
- No builds, Cargo commands, tests, formatter, Lake, cache/target/scratch,
  worktree, environment, configuration, or Git commands were run, as required.
- Manual source review covered the checked decoder, complete fact/provenance
  reifier, selected R66 rows, `SemanticFact`, `TermView`, endpoint
  canonicalizers, component positions/live components and representative
  owner. Compile/runtime behavior remains unchecked.
- R68 rev1 independent review identified a local-`Vec` reference escape from
  `internal_root_view`. The selected interpretation now copies the
  owner-scoped `InventoryReifiedFact` payload; its only retained fact pointer
  targets the same owner `SemanticFact`, verified against the selected edge.
  No build or compiler check was run, so the review repair awaits the assigned
  fresh delta review.
- No disposable scratch or generated paths were created.
- Budget spent/remaining: UNKNOWN; child runtime exposed no timer telemetry.
- Final artifact hash is reported with the frozen submission; it is not embedded
  in this file.

Next related in-envelope step: freeze these revision-2 bytes and have the
assigned fresh reviewer inspect both the local-Vec repair and the mapping
alongside the proof lane's constructor and canonicalization equations. Tests
or this owner-local implementation alone do not close a theorem or authorize
cutover.

Worker state at handoff: STOPPED / WRITES STOPPED; no descendants or other
leased outputs remain active.
