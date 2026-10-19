# R138 source/native owner map: helper cut ledger

Status: **PARTIAL SOURCE/NATIVE MAP; R73 and R72 targets remain OPEN.**
Author `/root`, Luna primary. Sprint `helper-cut-ledger-20261020-r138`,
contract rev1 SHA-256
`8bfe31e038f1c7684ac2d9dba95164f13448e150ccb08a874bea22610fc6e04f`.
Baseline `66c7b52b197aa035d6feaf20ff4f84198a92f9cb`.

This map is not a complete constructor ledger, proof of source reachability,
runtime observation, or theorem. It identifies current owners and tests R73's
old source claims against the new baseline. R73 remains unreviewed and
unfinished; its 302-second report against a 300-second cap is preserved and
grants no carryover. Parent computation-forwarding, full source/native
inference and evaluator, Simple-sub A/B, R70/R71 coverage and production gates
remain OPEN; R50 remains NOT ADOPTED.

## Baseline delta since R73

R138 carries the 32 semantic paths from R73 but repins them to current baseline
and live bytes. Thirty-two current path/hash pairs match at R138 baseline; 24
historical hashes are unchanged and eight owners differ from R73. The 7 R73
artifacts are separately pinned. The changes are not proof inputs by mere
hash agreement; these owner-local checks identify their relevance:

| Changed owner | Current delta | Relation to fixed source and required rederivation |
| --- | --- | --- |
| `crates/yu-hir/src/module.rs` | Removes `replace_admission_root`; remaining placeholder predicate/formation path stays separate. | The sample uses admitted definitions and nested local function bodies. Recheck the exact source root and local carrier route; no substitution of a test-only root is permitted. |
| `crates/yu-hir/src/module/local_source.rs` | Adds `Case` / `CaseBinder`; parameterizes local `body` by admitted visibility; accepts `OperatorChain` or `IndentedStatementBlock` for that body. | The fixed source has no `case`; `my` local declarations remain private. Braced nested definition bodies require exact current CST→LocalSource formation evidence; old R73 formation assumptions are not silently reused. |
| `crates/yu-solver/src/candidate_source.rs` | Adds `CaseArms` traversal, binder positions, integer-pattern constraints, arm-body constraints, and CaseBinder handling. | No Case constructor occurs in the fixed source. Rewalk the exact existing Local/Lambda/Name/Apply schedule and component positions. |
| `crates/yu-solver/src/candidate_value_graph.rs` | Adds Case traversal and CatchBinder-valued Case binders. | No Case constructor occurs in the fixed source; unrelated branch does not supply missing R73 entries. |
| `crates/yu-solver/src/candidate_scheme.rs` | Changes only test-gated capture/freshen observations (`requested`, `freshen_candidate_graph`, graph-row index). | Production capture/bound/restoration owners are byte-stable from R73's pin. R73's partial capture list remains unproved; test-only observation is not an execution receipt. |
| `crates/yu-solver/src/candidate_context.rs` | Gates a test-only `completion` binding in a `ReplayChildWait::Ready` match. | No production transition change is visible in this diff; still rederive the ordinary-context relation constructors from current bytes. |
| `crates/yu-solver/src/lib.rs` | Moves `component_term_positions.insert` outside `debug_assert!` in both component constructors. | This is production-relevant: the map now populates in release builds; `component_endpoint` later requires it. Trace all fixed-source component occurrences through this map in the new ledger; R73's old byte-level source recipe is not enough. |
| `crates/yu-solver/src/shadow_apply.rs` | Adds `capture_forest` only to test fixtures. | Tests' constructed state is not production source evidence. Ordinary candidate route is unchanged by this diff. |

The eight current hashes are pinned in the R138 contract. All 39 direct pins
(32 current semantic paths plus 7 R73 artifacts) matched both the baseline Git
tree and live bytes at activation. No tests/builds/compiler/parser/solver runs
were made for this owner map.

## Current constructor and consumer owners

The fixed source is the ordinary `outer(q:[io] int)` specimen in the R138
contract. The source-side owner is `LocalSource::form` in
`yu-hir/src/module/local_source.rs`; the solver candidate then builds a
`ConstraintBatch` from the retained forms. The required event schedule still
needs exact occurrence and component IDs from the proof lane.

1. **Local publication and source action.** `candidate_source.rs` collects
   actions for expressions and local initializers. `Action::Local` consumes a
   previously installed `LocalScheme { root, boundary, capture_region }`.
   `install_candidate_local_term` publishes that owner. The fixed `helper x`
   occurrence must be traced as a local use after helper installation, with
   exact active action index and preceding typed work accounted for.
2. **Capture.** `route_candidate_local_run` starts a route transaction, reads
   the installed scheme, calls `capture_candidate_graph_owned`, then
   `prepare_candidate_fresh_use`, and stores a `LocalUse` with default cursor
   `(next_bound=0, restoration=None, complete=false)`. That cursor says nothing
   about graph size or earlier memo state. `Capture::bound` walks the live
   `bound_cursor` for the exact raw `BoundKey`; it emits a captured record per
   attached relation (or one `None` case), deduplicating by
   `(kind, side, lower, upper, relation)`. Evidence snapshots have a separate
   dedup map. Context payload/demand closure can add graph nodes after bounds
   are discovered. The entire vector order/count, physical multiplicity,
   evidence and fibers remain the proof lane's open ledger.
3. **FreshUse row/evidence mapping.** `prepare_candidate_fresh_use` consults
   the current representative and metadata for each captured row. A local row
   is freshened only when `row.local && level > graph.boundary &&
   !metadata.non_generic`; canonical-row memoization reuses one image for
   repeated representatives. Shared/non-generic rows map to their existing
   representative. This is a construction rule, not an instantiated row map
   for the fixed source.
4. **Transport then physical admission.** `begin_candidate_fresh_bound` maps
   endpoints and, when the captured bound has a relation, first constructs a
   FreshUse transport with the exact `source_bound`, context remap, use origin,
   and scoped-flow premise where enabled; it remaps attached bundles separately.
   It then maps the evidence snapshot and calls
   `candidate_begin_bound_restoration` with `BoundAdmissionCause::FreshUse`.
   In ordinary mode `candidate_bound_origin_with_evidence` takes the
   unscoped branch and invokes `candidate_context_bound` for physical
   admission. Therefore the transport relation and physical admission relation,
   dependencies and witness lineage must remain separate in each ledger event.
5. **Restoration.** `candidate_begin_bound_restoration` requires an idle typed
   worklist, physically inserts/adopts the bound, canonicalizes owner and item,
   then records the initial opposite-bound count. Each subsequent step retires
   at the saved count or rereads the live canonical owner/item and saved
   opposite index, starts a replay child, waits for its completion receipt,
   then advances. Earlier children can mutate representatives and adjacency;
   no endpoint-only snapshot supplies the ordered event history.
6. **Typed drain, Function replay and recapture.** `dispatch_live_item` uses
   typed-pair currentness plus relation/generation state. A retained
   extrusion rewrite can be re-enqueued, after `recapture_candidate_extrusion`
   looks up groups at `by_output[(TypedPairKey, ExtrusionEndpoint)]`; source
   qualification, reuse occurrence, activation and pending parent order are
   distinct from the relation-local completion test. Function port and
   `admit_lambda_fact` owners produce more typed work. Record enqueue/pop order,
   active drain state, acknowledgements and each relation separately.
7. **Later production copy and consumer.** The R72 target requires the actual
   later `Work::Bound` physical slot and an independently source-licensed
   consumer/provider for that same dependency/transform lineage. A Local
   FreshUse is not itself a production `Work::Bound`; a transported fiber,
   candidate Apply, endpoint equality or ancestry does not supply the required
   consumer. `post_check_context` and discharge/residual state are relation
   local. No later source occurrence or qualifying consumer is established by
   this partial map.

## Implementation-lane adjudication

Inspected current capture/use owners in `candidate_scheme.rs` and physical
restoration owner in `candidate_extrusion.rs`, plus relation, recapture and
drain owners in `candidate_context.rs`, `candidate_intrusion.rs`, and `lib.rs`.
The source diffs expose neither a concrete violation of an approved clause nor
a production repair justified by the original source. Result:
**NO_SAFE_CODE_SLICE**. This does not mean the compiler is correct; it means
this packet has not falsified an approved transition. A runtime observer or
instrumentation remains outside R138 and requires a new explicit primary
contract/lease before source edits.

## Remaining owner handoff

The exact missing result remains a complete event-sourced cut at helper Local
and the covered suffix, or the earliest authentic constructor rejection.
Reconcile this map with the proof lane only after both artifacts freeze. If a
changed current constructor invalidates an R73 premise, preserve the exact
break and classify the fixed outcome UNFINISHED unless A or B is independently
established. No parent gate closes from this map.
