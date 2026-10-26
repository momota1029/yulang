# Boundary-query closure: fresh M3 review

Date: 2026-10-26. Assignment/revision:
`20261026-inference-boundary-query-review/r1`. Reviewer:
`/root/boundary_query_review`, fresh nonauthor generic review leaf; registered
specialist role unavailable. Primary-reported baseline: `yulang3`,
`dd7d881ff58ff20cbfbea8db72126dbbecbc3a1a`. The producer's recorded construction
baseline is `f5b947056f23fb50236463d86738bdea579c1514`. No Git command was used;
the review is pinned to the independently recomputed artifact hashes below.

## Verdict

**ACCEPT. No mandatory findings.**

Acceptance covers the frozen finite reference-routing construction, its exact
query-membership and finite-event theorems, the original record discriminators,
and the accompanying claim boundaries. It does not certify arbitrary native
worklist scheduling, source/native extraction, concrete child casts, original
semantic boundary identity, complete Call, or whole-source inference soundness.
The new `NativeRecordPlan` work is outside this review.

The unchanged parent remains `SourceProblem.InferenceSoundness` for every
supported original source, with original scope and one shared witness. The
review does not change the supported language, source semantics or production
authority. The manuscript is a research specification, not new semantic
approval.

## Sources and review method

Read `AGENTS.md`, `AGENTS.pre-sprint.md`, the Lean proof skill and its source and
execution references, the goal-driven sprint contract, design authority,
orchestration/review budget, proof-obligation economy, the October 11 inference
principles, the current native-inference progress record and selected native
continuation receipt. Inspected the original manuscript's record/view section
at lines 356–425 and endpoint/worklist section at lines 479–552, its opening
scope notice, the entire 512-line new Lean module, and the whole theory note and
producer handoff. Inspected the imported `Reach` datatype and path lemmas,
the original record compiler witnesses and survivor theorems, and the actual
`SourceProblem.InferenceSoundness` definition.

The native record correspondence note was read to verify the application seam:
it explicitly leaves semantic adaptation boundary `j`, distinct output-view
elaboration, unchanged-view edge classification and child evidence unresolved.
Its Rust derivation was not independently certified in this review. No Rust
inspection, probe, test or modification was performed here.

The assignment budget was 600 seconds with zero optional checker reruns. Used
only source inspection, deterministic byte hashes/copy comparisons, and parsing
of the already frozen checker logs. **Zero new Lean/Lake calls.** No discrepancy
required an additional bounded checker call. No children were started.

## Mathematical and source correspondence findings

1. **The closure is computed and its bound is proved.** In the Lean module,
   lines 29–58 enumerate every finite port pair and seed reflexivity plus
   admitted wiring. Lines 60–108 define actual composition rounds, additions,
   pending filtering and recursion. `remaining_strict` proves a changed filter
   strictly shortens pending; `additions_new` and `remaining_separate` preserve
   freshness. `close_closed` proves adequacy from `pending.length ≤ fuel`, and
   `routes` instantiates this with exactly the initial pending length. The
   `Runs` receipt and `routes_runs` derive real fresh/decreasing steps. No
   arbitrary fuel, assumed saturation, `LocalLaws` or semantic model appears at
   the application root.

2. **Exactness is against an independent path relation.** `close_sound`
   constructs `BirthLevelSCC.Reach` witnesses, and `routes_exact` proves the
   converse by path induction using seed retention and derived transitive
   closure (lines 153–242). Only ordinary `Reach`, `Reach.trans` and `Reach.mono`
   are reused from `BirthLevelSCC`; no SCC/native incidence condition is
   silently identified with unchanged-view flow. `Edge` is precisely supplied
   wiring membership together with equal endpoint kinds. Source/context
   eligibility remains external, as stated in both source comment and note.

3. **Queries preserve full records.** `Anchor`, `Demand` and `Query` at lines
   255–280 retain heads, producer origin, consumer boundary, context, occurrence
   and tag. Routing filters only finite ports and requires no finite or
   decidable-equality hypothesis on the six opaque payload types. For all
   `n`, payload types, inputs and complete query records, `complete_exact`
   states exactly:

   ```lean
   q ∈ complete i ↔ q ∈ i.direct ∨
     (q.producer ∈ i.anchors ∧ q.consumer ∈ i.demands ∧
       Reach (Edge i.wiring) q.producer.port q.consumer.port)
   ```

   Direct queries remain unchanged, including any invalid direct kind fields;
   their validity is not asserted. `routed_kind` applies only to routed queries.
   The record equality and retention roots do not collapse provenance to
   endpoint equality. Keeping an arbitrary `Tag` does not manufacture Call or
   contextual semantic evidence.

4. **Lower/upper meeting and order claims have the stated scope.**
   `lowerAt_exact` follows an anchor forward; `upperAt_exact` follows a meeting
   port forward to the original demand. `query_at_meeting_port` composes those
   paths, and its other direction can select the consumer's port. This matches
   the manuscript's endpoint formula. `completion_order_independent` assumes
   equal membership of all four input lists and concludes equal completed-query
   membership. It proves neither list order/multiplicity equality nor an
   operational simulation of arbitrary fair insert-edge/lower/upper schedules.
   The note says this explicitly at lines 135–151 and calls the construction a
   proof-side reference procedure at lines 112–115. The manuscript's general
   fair-routing implementation correspondence is therefore not promoted by
   this acceptance.

5. **Growing wiring is handled by a separate, honest finite construction.**
   `insertEvent` appends edge, lower, upper or direct data; `advance` recomputes
   completion after every event. `run_completed` is induction over a finite
   fold, and `run_exact` applies the exact formula to its final input, hence to
   any chosen finite prefix. All ports inhabit one global `Fin n` universe.
   No arbitrary generator termination, finite containment, native history
   lawfulness, incremental currentness or success-to-completion theorem is
   claimed. This is not a fixed initial graph theorem misapplied after growth.

6. **Adaptation does not manufacture identity flow.** `Event.adaptation`
   requires unequal input/output ports and appends only the input demand and
   output anchor. `adaptation_stops_identity` proves literal wiring equality.
   This alone does not eliminate pre-existing inappropriate paths or prove
   output-port freshness; the note explicitly records that remaining
   extraction duty. No theorem treats concrete query success as an identity
   edge or composes concrete adaptation success transitively.

7. **The discriminators use the original record model.** The A/B/C heads are
   the unchanged imported optional-string, empty-record and optional-int
   witnesses. `unchanged_emits_failing_direct_query` both emits the exact A/C
   query across unchanged wiring and invokes the old compiler's failed direct
   comparison. `two_adaptations_do_not_emit_ac` emits A/B and B/C at distinct
   ports while empty wiring excludes A/C. The imported
   `direct_comparison_nontransitive` proves the two constituent compiles
   succeed. Existing `composed_survivors` and
   `accepted_paths_have_different_views` retain non-resurrection and the
   different accepted-path results; the new note accurately says these were
   reused, not reproved. Coincident endpoints remain distinct when any tested
   origin/boundary/context/occurrence/tag changes. The late-edge witness also
   demonstrates an old retained anchor/demand becoming queryable after a new
   edge.

## Frozen evidence and audit coverage

Independently recomputed SHA-256 values:

| Item | SHA-256 |
| --- | --- |
| `BoundaryQueryClosure.lean` | `7dad22c1b94e404be5dc4aaa51203e8d3882fd4c61006eb8b0c5f6f87a30f727` |
| Boundary-query theory note | `9b529696fe010630b2c07755bc1d0cd642459e9472d612a5c5ddcdd73273895a` |
| Producer handoff | `360d954e711a45af663c0a141635fd374919a266e6a82ae6d26a2b89a525a20c` |
| Original manuscript | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |
| Selected continuation receipt | `2caf2e1965d3ca2cc07184a0895c74b116bbf1dfae568635afb9bb4b8a6626b5` |
| `BirthLevelSCC.lean` | `2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `RecordBoundaryPreservation.lean` | `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` |
| Producer `check08.log` | `9af7a6215eba90ac4e185d2111f0ec446bebae28a28b8f6d900f35f3eb471293` |
| Producer `check09.log` | `eae205005c2e84e3f85b2caf61a58f6d08651964516ad24b1b89a0ed7c11e890` |
| Producer `project/AuditBoundaryQueryClosure.lean` | `024aa6654ff274eacbface89329b3ffe1b5f5648d876afe97b39f120239df102` |

The new module and all three project-source dependencies are byte-identical
between the repository and the producer's isolated checked project. The
retained evidence root is
`/workspace/scratch/f98087c7ac1a/inference-boundary-query-closure`.

The inspected project pins Lean 4.35.0, has no external packages and sets
`-j1 -M1024`. Producer records report native Lake `5.0.0-src+eb6cafb` and Lean
`4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, using the exact
installed path
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
The retained wrapper sets `LEAN_NUM_THREADS=1`, uses a 120-second process-group
deadline and preserves failed attempts.

* Build 08: `lake build +YulangClosure.BoundaryQueryClosure`, exit 0,
  **five jobs**, 3.896 seconds. This is the exact module/import build, not a
  fresh whole-repository/default-target integration claim.
* Audit 09: `lake env lean -j1 -M1024 AuditBoundaryQueryClosure.lean`, exit 0,
  1.713 seconds. The auditor selects the exact originating module index,
  rejects project axioms, checks theorem kind and inclusion for all 18 required
  named roots, and prints the type and transitive axiom set for every selected
  declaration, including private/generated constants.
* Independent log parsing found **332 unique begin markers, 332 unique end
  markers, matching ordered names, and 332 matching axiom results**. The audit
  reports **127 theorem constants**; 332 is the broader declaration count.
  Every required named root is present. The complete 18-root printed types were
  inspected against the actual declarations and stated premises.
* Normalizing whitespace in printed axiom sets gives **211 declarations with
  none, 80 with `propext`, and 41 with `propext` plus `Quot.sound`**. No
  `Classical.choice`, `sorryAx`, project axiom or other nonstandard axiom appears.
  These are declaration-wide totals, not theorem-only totals.
* The source search over the new module and its three project dependencies
  found no `sorry`, `admit`, project `axiom`, `native_decide`, checker bypass,
  unsafe implementation replacement or resource-limit override. Standard
  pretty-printing elides proof arguments in some generated `Runs` recursor
  types; no required theorem statement or axiom inventory is omitted.

Producer usage remains nine of 18 focused calls. The retained failures and
successful rebuild/audit are unchanged; this reviewer did not replace logs or
spend the producer's remaining allowance.

## Parent application, remaining owners and cessation

The accepted component supplies exact finite endpoint membership for the
computed reference closure once an owner extracts eligible unchanged-view
wiring and intact original anchor/demand/direct records. Applying it to native
inference still requires the actual insertion/replay/history correspondence,
including admissibility, finite containment, generation/currentness and
diagnostic-completed availability. These duties remain with the native/source
lanes and primary.

The record-plan owner must connect the extracted native skeleton to one
authentic semantic boundary and its resolved child evidence. Routing supplies
neither semantic `j`, child casts, request/resumption contracts nor complete
Call. Full original source reconstruction, contextual meaning, sharing and
generalization remain open at their original owners. The frozen companion
correctly identifies that seam rather than deriving it from endpoint IDs.

Primary may integrate the accepted frozen routing component and this review
under the existing gate. Shared imports/status, final integration verification,
Git and publication remain primary-owned. No mandatory repair or additional
review round is requested.

Only this leased review receipt was written. The optional isolated reviewer
scratch path was unused. No producer file, shared status/import, dependency,
toolchain, Git state or native source was changed. **Writes stopped; no checker,
worker child or background process remains running.**
