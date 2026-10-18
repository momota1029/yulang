# R71 owner map: physical bound slots to raw/canonical fibers

Date: 2026-10-19. Sprint `raw-canonical-fiber-coverage-20261019-r71`, revision 1. Contract SHA-256 `a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb`; baseline `f375fd737`. Author `/root`, Luna/high. Outcome class: static source/native ownership map; not a coverage proof or counterexample.

## 1. Entry and selected physical slot

The production roots remain the two `dispatch_live_item` calls covered by R70 (`lib.rs:12572,12585` at the reviewed R70 snapshot), under `shadow-apply-candidate` and a present candidate graph. R70's reviewed conditional lemma describes their local extrusion, while entry well-formedness remains an unproved premise. This map does not claim all source constraints reach these calls.

`candidate_extrude` first canonicalizes the root while constructing its `Key` (`candidate_extrusion.rs:76`). For a deep row, `Work::Visit` reads that representative's current physical `direct_*_rows` or `exact_non_variable_*` vector at the visit-time lengths (`:98–185`). The chosen polarity selects lower on Positive and upper on Negative, separately for Value and Effect bounds. Each selected slot yields two related objects:

- the child `Key` built from `canonical_extrusion(bound)`, polarity and target (`:157`); and
- `Work::Bound(copy, polarity, child_key, BoundKey(endpoint, polarity, bound))` (`:160–165`), whose source key keeps the physical item's current endpoint before that key-builder canonicalization.

Thus physical slot contents, the structural child key and the evidence source key must be tracked separately. The Visit arm consumes the key already built by its caller; it does not perform a generic fresh canonicalization of that key.

## 2. Append and readback ownership

`candidate_insert_bound_with_evidence` canonicalizes both owner and item before selecting the kind/polarity lane and appending to the physical Value/Effect bounds (`candidate_extrusion.rs:499–620`). It first creates the admission under that canonical `BoundKey`, appends the item, then reads the addressed physical slot back and checks it equals the admission key (`:621–675`). The retained emission names the exact `PhysicalBoundSlot` and constructor-after-append readback. A later representative change does not rewrite the already appended vector element.

In scoped mode, `candidate_insert_copied_bound` imports an exact source-key snapshot with `relation=None` and records `MissingBoundRelation`/`MissingOriginAssociation` coverage before emitting bootstrap metadata (`candidate_extrusion.rs:415–430`, `candidate_effect.rs:522–565`). In unscoped mode it emits with the current owner processing. Neither bootstrap is the executable fiber-copy loop: `candidate_transfer_bound_origins` follows the exact source key's contextual relation chain and applies an explicit witness to each relation (`candidate_effect.rs:677–695`). It separately iterates source-key origin metadata and emits with no relation, preserving the association gap (`:696–719`).

## 3. Exact-key evidence index and copy path

Context stores a head by exact `BoundKey`; `bound_cursor` and `bound_entry` enumerate that chain, and `attach` deduplicates relations only within the exact destination key (`candidate_context.rs:3133–3161`). `EvidenceState.snapshot` separately uses exact `(BoundKey, Option<RelationId>)` group lookup, producing explicit missing-group/admission/emission gaps instead of falling back to a canonical neighbor (`:688–710`). A source alias and its representative therefore need a proved transport relation; endpoint equality alone has no lookup behavior.

At `Work::Bound` (`candidate_extrusion.rs:310–320`), the child result is obtained from the canonical child key. The physical copied bound is emitted through the canonicalizing append helper, then `candidate_transfer_bound_origins` receives the stored source key unchanged and a freshly canonicalized destination key. Relation fibers and origin metadata remain separate across this step. Evidence provenance is explicit through `candidate_context_transport_witness_with_evidence` (`candidate_context.rs:4091–4106`); it snapshots the named source relation, creates a transport dependency/fiber transform, and attaches the result under the exact target key.

## 4. Merge and all-owner canonicalization

`merge_candidate_rows` resolves the representatives, reads the copy's physical sides through `candidate_opposite_count` / `candidate_opposite_bound`, and appends each item to the parent with `candidate_insert_copied_bound`; that append canonicalizes owner and item at the time of insertion. It transfers fibers from the exact copy-owner source key to the parent-owner/canonical-item target (`candidate_intrusion.rs:599–664`). Only after these transfers does it write the representative edge and call `candidate_context_canonicalize_bounds` (`:665–692`).

That canonicalizer takes the current length of the global contextual `bound_keys` list, and for every existing key whose owner or item representative changes, transports that relation to the canonicalized `BoundKey` with `EqualityCanonicalization` (`candidate_context.rs:4005–4023`). It does not delete the original raw key. It also traverses keys belonging to third-party owners, not only the merged row. The relation transport is keyed by the exact old row and relation, and the destination relation retains the source/context witness. Repeated merges can therefore leave multiple old keys plus newer canonical keys; equality of their fiber sets is not implied.

The merge loop's `candidate_opposite_bound` canonicalizes the selected item before it forms a merge source key (`candidate_extrusion.rs:705–735`). By contrast, the extrusion Visit's direct vector read forms its Work::Bound source from the stored physical item and canonicalized owner. These two call paths must not be collapsed in a coverage argument. The bridge to establish is whether every physical item was installed under an exact key that survives as a raw key or receives the needed forward canonical transport before the Visit's raw lookup.

## 5. Reachability and proof boundary

The pin set includes the R70 reviewed conditional result, its exact two callers, physical append/readback, evidence index/transport, representative merge and source/scheme owners. It locates the source/fresh-use/admission owners but this map does not prove an all-path constructor induction from them to every selected slot. R70 entry-WF is not imported as discharged. A manually arranged `bounds` vector and unrelated evidence map is not production evidence.

The R71 proof must establish per actual slot whether (a) the exact raw source key contains required fibers, or (b) a constructor/merge transport placed them there. It need not establish `F(raw)=F(canonical)` where equality is unnecessary. Conversely, a canonical destination with more fibers does not by itself prove the raw lookup is complete or incomplete. Preserve legitimate empty fibers, recorded association gaps, and later admissions. The attack lane owns any proposed countertrace and its production-reachability bridge; no counterexample is adjudicated here.

No source/evaluator, soundness, principality, outer-drain, A/B or parent theorem follows. No tests/builds/probes or code changes ran. The contract's 20 direct pins matched baseline and live bytes at activation; the R70 closeout is pushed. Luna owns this output and Git; exact handoff and final hashes are in `tasks/agent-loop/inbox/20261019-r71-implementation.md`.
