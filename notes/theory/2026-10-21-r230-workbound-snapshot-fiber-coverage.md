# R230 — Same-owner WorkBound snapshot fiber coverage

Status: bounded source/native lemma; no independent review. R71, R72 and the original computation-forwarding theorem remain OPEN.

## Lemma

For one ordinary extrusion `Work::Visit` of a row endpoint and fixed polarity/target, every physical bound entry in the opposite-side row vectors included in that visit's captured lengths is represented by a `Work::Bound` carrying its pre-canonical raw `BoundKey`. Its mapped destination is looked up through the visit's canonical child `Key`. When the WorkBound is processed, every retained relation attached to that exact raw key is transferred to the destination's canonical bound key with an `Extrusion` witness. Equality canonicalization separately attaches each relation to the canonicalized key while retaining the original raw attachment.

This is a same-owner prefix coverage result. It establishes an execution path for all alias-equivalent physical slots already present in that visited owner row. It does not establish that every third-party owner row is visited or that its fibers are independently required by a later consumer.

## Source derivation

1. `merge_candidate_rows` first resolves both inputs to their current representatives. For each polarity it enumerates every opposite-side slot on the source representative, physically appends a copied entry to the destination representative, and calls `candidate_transfer_bound_origins` from the exact source owner/item key to the destination with the item's canonical representative. The old physical source vectors remain intact. It then performs the representative parent write and calls `candidate_context_canonicalize_bounds` before replay. Thus owner merge does not replace a row's physical slots by a set of canonical items.

2. A row `Work::Visit` snapshots the current `direct` and `exact` vector lengths before it starts adding copied constraints. It then enumerates the complete `[0, direct + exact)` prefix. Each iteration reads the original stored item into `bound`, computes the shared `child = Key(canonical(bound), polarity, target)`, and queues `Work::Bound(copy, polarity, child, BoundKey(endpoint, polarity, bound))`. The lookup key is canonical, while the source argument remains the physical entry's raw item. Distinct physical aliases therefore stay distinct source keys but resolve to the same child when their current representative is the same.

3. Processing `Work::Bound` resolves that exact child key in the retained rows/structure maps, appends the copied physical bound, then calls `candidate_transfer_bound_origins(source, BoundKey(canonical(owner), polarity, canonical(copied)), Extrusion)`. `candidate_transfer_bound_origins` walks the complete linked fiber list at `bound_cursor(source)` and creates one evidence-bearing transport for each parent relation. It does not substitute diagnostic origins for executable fibers.

4. `candidate_context_transport_witness_with_evidence` validates `witness.to == to`, snapshots the exact source bound and parent relation, computes the transported scoped state from that parent and witness, creates a child relation with the parent's post-check context and source set, records `Dependency::Transport`, creates a FiberTransform linking antecedent/witness/parent/child, and attaches the child at `to`. It retains relation identity rather than merging fibers by endpoint shape.

5. `candidate_context_canonicalize_bounds` scans the bound-key prefix captured at entry. For each key changed by current representatives, it performs `EqualityCanonicalization` transport to the canonical key. The transport attaches the child at the canonical key and leaves the raw key's earlier relation attachment present. This gives forward raw-to-canonical retention; it does not add the canonical bucket's unrelated fibers back onto each raw key.

Together, these code paths show that all same-owner physical siblings present at the visit snapshot independently contribute their exact raw fibers to a shared canonical destination. A sibling's lineage need not be forged as a fiber of another sibling's raw key: its own physical slot causes its own WorkBound transfer.

## Remaining R71 premises

The lemma does not cover a third-owner row merely because its item canonicalizes to the same child. That physical slot requires a later visit of that owner, and the exact source/scheduler path that makes the visit occur remains the R71 reachable-alias-schedule obligation. It also does not establish whether an external source/native theorem needs every fiber from another owner at a particular consumer; that requires the exact later WorkBound and independently justified consumer lineage. Existing R218–R229 exact-source traces do not supply the target slot-4 alias change.

No code change follows from this result. The earlier R71 `NO_SAFE_CODE_SLICE` remains accurate: no approved production clause violation or missing same-owner transfer was found. R71's general quantifiers, merge/rollback induction, cross-owner reachability, later drain and production gates remain open.
