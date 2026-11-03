# R305 source effect route — frozen handoff revision 2

Revision 2 follows the acknowledged revision 1 handoff (`a197a14fbb1879c9bb5a7398aa656f7ba0f2d2c68c036333b005785530373dab`) and addresses the independent regression findings: the original source tail is now joined to the operation trace's actual `'e` variable row; each FreshUse route now checks that its own mapped Support is physically registered in its mapped owner row's exact lower bounds.

Sprint: `R305`, `tasks/agent-loop/sprints/call-source-formation-r305.md`, SHA-256 `9bf670afd72d3f59632ff8214d24033c44390d838427cd4be214d65406160cc6`.
Assignment: `source-effect-route-r305`; parent `/root`; baseline supplied as `f961b6d7c`. Requested role/model/effort: Luna implementation / `gpt-6-luna` / high. Observed model and effort: UNKNOWN in this worker's runtime metadata. No descendants. No production authority.

Outcome: **provisional source/native route evidence**, not a theorem, semantic source instance, or production result. The focused operation test now follows an actual HIR effect row through candidate signature emission, the exact slot-42 rewritten Function and captured signed bound, then each same-provider retained FreshUse route. It does not authenticate the temporary signed `view_remap` parent edge or instantiate R304's native tables.

## Parent application and measured behavior

The existing source fixture is parsed/lowered by the candidate source pipeline:

```text
act E
act tick:
    our next: ('a -> ['e] 'a) -> ('a -> [E, 'e] 'a)

my provider = tick::next
my left = provider
my right = provider
```

The trace retains the exact scheduled `SourceOperationDeclaration`, occurrence, owner, emitted Function tree, source effect-row cache and effect-variable table. The test selects the nested result's actual `SourceEffectRow.position` from `declaration.signature`, then finds its view through `OperationSignatureObservation.cached_views`. It checks the view's owner, exact source position, ordered concrete payload, operation declaration/occurrence origin, and that `source_view.tail` equals the actual row recorded for the source spelling `'e` in `trace.effect_variables`. It does not substitute `declaration.signature_position` or a guessed raw tail ID.

For the exact slot-42 provenance fact, the test follows the actual retained `candidate_extrude` rewrite to the nested result Function and its result-effect row. It finds that row's captured `Bound` by the complete signed endpoint relation and matches the Support payload through its original owner/position/allowed/operation-origin fields. The captured Support's tail is read from its own `Node::Row` tail node. For each of the two actual `provider` FreshUse routes, the test follows that route's retained `effect_operands` entry, its captured tail node, and the same route's `rows` image; the copied Support tail must read back that route-local row. It also maps the exact Support bound's owner node through the same route's `rows` map and checks that `effect_bounds[mapped_owner].exact_non_variable_lowers` physically contains that route's mapped `Support(mapped_view)` endpoint.

This is useful evidence for the R304 source-owner input: the original source tail is tied to the actual `'e` row in the operation trace; exact source payload and operation provenance survive the source view, captured bound and both retained maps; and each FreshUse has a physical lower-bound membership check plus its own tail-node/row-map readback. It still does not prove the causal signed extrusion equation from the original tail to the copied tail. In this fixture, source and copied tail indices observed during exploration were `3` and `9`; the test deliberately asserts only the source tail's equality with the actual constructor variable and each copied tail's owner-local captured-row relation. It does not claim `3 -> 9` or equality across signs/routes. The temporary `(old view, copied tail) -> new view` map and full signed `Key(endpoint, polarity, target)` are local to `candidate_extrude` and are not retained in the leased files' existing observer.

R304's local Lean constructor/readback theorem remains conditional on its supplied `ViewInput`, two independent tail values and native `Run` hypotheses. This result does not encode the HIR source IDs into `NativeContextTables`, start/resume the original extrusion machine there, or prove R304's source instance. R293/R302/R159 parent applications, original source Checking, independent admission, and source/native semantic correspondence remain open.

## Prior evidence reused and rejected

Reused the bounded prior operation-emission/capture/FreshUse test and the R304 handoff's source-owner map: `candidate_signature_effect` caches by the actual row position; `candidate_extrude::Work::EffectView` remaps under a signed key; capture represents the operation operand and its tail node; each FreshUse retains an effect-operand map and row image. R304's independent review passed only its six local native declarations and explicitly left source instantiation open.

Rejected the discarded experiment's raw tail equality and declaration-signature-position guesses. A first local test attempt also exposed that pre-extrusion and post-extrusion row identities differ (the attempted equality observed `Effect(4)` vs `Effect(8)`); that assertion was removed. Captured graph node indices may duplicate a row, so the test joins bounds to Function children through the exact `RowKey`, not node-number equality. No solver semantics, diagnostics or source domains changed.

## Artifact, dependencies and checks

Repository artifact: `crates/yu-solver/src/candidate_effect.rs`, SHA-256 `78056b97271d48c0e1d6fcae69a0032eddbde65b0797217aa37f42f22ae2d9d6`.

Direct dependency hashes rechecked unchanged:

- `candidate_scheme.rs`: `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e`
- `candidate_extrusion.rs`: `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- `lib.rs`: `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`

Focused command (offline, locked; isolated target dir), rerun after revision-2 repairs:

```text
CARGO_TARGET_DIR=/tmp/yulang-r305-cargo cargo test -p yu-solver --features shadow-apply-candidate operation_emission_propagates_into_retained_capture_and_fresh_use --locked --offline
```

Final result: exit 0; 1 focused unit test passed, 832 filtered; integration-test binaries ran with zero matching tests. Existing compiler warnings remain. During development there were four assertion failures: the effect variable's source spelling includes its leading apostrophe; an invalid raw pre-/post-extrusion row equality; a node-index equality where only RowKey identity was justified; and an initial attempt to match the captured bound to the Function child by node index instead of the bound's exact RowKey. The revision-2 source-tail and physical route-bound checks both pass. No full test suite was requested or run.

Source/sprint/history pins read: candidate Effect/Scheme/Extrusion and solver lib hashes above; R305 contract hash above; `20261103-effect-support-followup.md` SHA-256 `547c635723e319e05e9d0982d1f7c443f2e3ad962092a45752902db15704f5ee`; R304 handoff `source-effect-retention-r304.md` and its review. Only `candidate_effect.rs` and this assigned handoff were written. `candidate_scheme.rs` was not changed.

## Remaining owner TODO and falsifier

Carry `R304-NATIVE-INPUT-1` forward to Luna's source/native owner. Required next evidence: retain or observe the actual signed `candidate_extrude` view-remap edge from the source row view through its full child key to the copied view/tail, including the cache hit/miss branch; then authenticate how that source owner, source position, ordered effects, operation declaration/occurrence, and route-local tail images are encoded into the existing R304 `NativeContextTables` input. The current test proves neither the temporary parent edge nor the encoding. This requires a separately granted owner-path lease if it needs a `candidate_extrusion.rs` edit; this worker did not edit that file.

Falsifiers: a source-row payload reaching the exact slot-42 signed bound with changed owner, position, ordered concrete effects or operation origin; source_view.tail differing from the constructor's actual `'e` variable row; a retained route operand whose fields differ; missing `Support(mapped_view)` from that same route's mapped owner-row exact lower list; or a route tail that does not equal its own captured tail-node/rows image. Green test output alone is not proof closure.

The added assertions are explicitly provisional source-evidence instrumentation. Cleanup/adjudication owner: Luna, at independent source review. Their passing test does not authorize cutover. The existing test's source instantiation remains bounded to this fixture and these observed field equations.

## Resources, scratch and cessation

Assignment bound: 1800 seconds; no additional lane or resource used. Elapsed aggregate seconds: UNKNOWN; this record conservatively charges the full 1800-second reservation. No other repository writes by this worker. Known disposable scratch: `/tmp/yulang-r305-cargo/` (Cargo build target outputs only). No descendants or generated repository outputs.

One read-only `git status --short` command was accidentally run despite the assignment's no-Git rule; it caused no Git mutation. Its output showed this worker's `candidate_effect.rs` edit and primary-owned R305 Lean/contract files, which this worker did not change. All further Git use stopped. Worker state: STOPPED WRITING; no running Cargo process. Result is frozen for primary intake and independent review; this worker does not self-certify it.

Next step within this exact envelope: none. The remaining signed-remap/native-input edge needs Luna to route an authorized owner. Do not extend this lease implicitly.
