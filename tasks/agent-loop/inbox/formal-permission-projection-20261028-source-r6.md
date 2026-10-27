# Formal permission projection r6: production caller reachability

Status: FROZEN revision 1 on submission; producer-authored, UNREVIEWED. Outcome class: source-native-evidence (static source evidence only; native bridge unverified), with a conditional lifecycle derivation. No counterexample or theorem closure. Universal r2 B, r2 C/D, the original endpoint-image obligation, parent A/B, full inference/executor soundness, source/native and production gates remain OPEN. R1 Lean verification remains unchecked.

## Objective and dependencies

Assignment `/root/formal_permission_projection_source_r6`, session `GOAL-REPLAN-EVENTPROOF-20261028`; no descendants or coauthors. Primary-supplied baseline `3cc8a897fe08980576b1582952a95acab55f09d2`; no Git resolution attempted. R6 contract SHA-256 `63c7079d33b639e43792a69f543f79eea1c1d9ef5cffce1f6126a4a392c28620`. Requested registered researcher/defaults; observed model/effort UNKNOWN.

Method: bounded static caller/callee tracing of the nine admitted owners, plus authentication and the frozen r5 contract/handoff/review. Apply the yulang-proofs distinction between source evidence and assumed transition laws. No executable oracle, test, probe, mutation, random seed or enumeration range applies. Ordinary Rust/std semantics and successful necessary allocations are shared assumptions; this is not an independent semantic oracle or independent review.

Governing meaning remains annotation-policy §§1, 1.1, 1.2 and 4, with §6 retracted, and top-level inference principles §§4–5: partial private state may be abandoned, but an incorrect typing or inconsistent result must not be published. Composed polarity, source-local permission, actual inflow and subtraction residual remain separate. No selected language meaning was changed.

All nine source/policy SHA-256 pins matched, with no dependency changes:

| Owner | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |

Frozen r5 contract `a8c163667df7d2fbbedde50d211a5db41fd188db033d986836fd028ef250524d`, handoff `a013997ca7529c36627254cf2a283e2142ec416cffd46c76df6cfa230d9e1ab0`, and independent review `823a377c9c2c3935fcde27bfbbc37df65ffddecdb09956839aaa5558ab83314a` also matched. Their accepted conditional checkpoint equation and limitations are retained. Earlier r2–r4 files were not independently reopened/authenticated in r6.

## Reachable source construction and private lifetime

1. The production source collector emits these actions while visiting `LocalSourceForm::Lambda` (`candidate_source.rs:1283–1340`). A record pattern emits `RecordParameter` with the actual field binder positions and defaults (`:1295–1311`); a unit pattern emits `UnitParameter`, rejecting a simultaneous annotation (`:1315–1319`); an annotated formal emits `FormalAnnotation` with its actual parameter position, lambda occurrence and retained annotation scope (`:1323–1339`). An effects-bearing annotation can first emit sibling `FormalEntry`. These branches are before the file's `#[cfg(test)]` module at `:2512`; they are not merely hand-assembled test actions. Upstream HIR/source realization remains outside this result.

2. For a definition, `execute_candidate_graph_plan` runs `execute_candidate_source_root` for SCC members before capturing them (`candidate_scheme.rs:2872–2876`). Root execution resolves its definition position and enters `execute_candidate_source_schedule` (`candidate_source.rs:2354–2367`). The driver reads the retained schedule and clones exactly its next action (`:2420–2438`), invokes `execute_candidate_action` (`:2453`), then advances the cursor only on success. Dispatch directly calls the three publishers and the `FormalEntry` sibling (`:2459–2463`). Expressions, loose actions and member schedules use the same driver (`:2329–2352`); `lib.rs:10639–10658` reaches loose/expression schedules after the SCC plan.

3. The visible source schedule entry is **not wrapped in an outer route transaction**. `begin_candidate_source` installs a source frame in the current graph (`candidate_source.rs:2369–2380`), not an intrusion undo. `execute` calls the SCC/source drivers directly (`lib.rs:10637–10666`), and `execute_scc_plan` directly returns the graph-plan result (`:17069–17079`). Thus r5's active-undo premise is not supplied by this caller skeleton. Publication's optional undo branches are meaningful for transaction callers, but universal begin-dominates-formal-publication cannot be inferred from these production entries.

4. This does not establish a defect. `try_new_candidate` constructs a private session then calls `start_candidate_graph` once (`lib.rs:10435–10440`). The latter builds a fresh graph, initializes its algebra, reserves graph/local slots and assigns `Some(state)` only after its fallible setup (`candidate_scheme.rs:2263–2285`). Source initialization earlier in `try_new` establishes levels/native formal roots (`lib.rs:10401–10402`; `candidate_source.rs:2292–2327`). The admitted-union search found this explicit graph assignment and the later move into frozen data; it did not find a production reinitialization call besides the constructor. This is bounded evidence, not a universal no-replacement theorem over unadmitted implementations.

5. `execute_candidate_source_schedule` clears the source frame after a driver error and propagates that error with `?` (`candidate_source.rs:2362–2365`). Source actions propagate publisher failures with `?`; no success conversion appears here. Graph-plan member execution also propagates `?`, and `execute_scc_plan` returns that error after clearing accounting scratch. `run_candidate(mut self)` uses `execute()?`, field-tail execution `?`, then consumes itself in `finish_candidate` (`lib.rs:10673–10680`). A failed execution therefore yields no solved result from this consuming path.

6. The public candidate observation solve path supplies stronger ownership evidence: `shadow_apply.rs:1833` creates the local session. The normal branch propagates `session.execute()` errors and field-tail errors, then consumes it in `finish_candidate` (`:1920–1933`). The readback branch returns errors, including deferred selection, rather than producing `Self` (`:1847–1919`). Readback snapshots contain counters/receiver observations; they do not return the session or a `CandidateGraphExport`. Only after obtaining `solved` does the function return `Ok(Self { solved })` (`:2004`). On these visible paths a partially initialized/published graph can remain internally mutated when an error occurs, but that failed attempt cannot become this successful observation.

Conditional lifecycle conclusion: for the shown solve entries, provided invoked callbacks neither replace the private candidate graph nor independently leak an export/solved owner, each directly scheduled formal action may use the private-attempt alternative in r6. A failure propagates before solved-owner construction. Full restoration is unnecessary for that alternative. The callback/no-escape premise is explicit; this packet does not claim a complete transitive audit of every source action or receiver/call implementation.

## Route transactions and the two rollback error exits

The source action dispatcher routes module uses through `route_candidate_open_use` or `route_incoming`, and local uses through `route_candidate_local` (`candidate_source.rs:2490–2500`). These are individual route actions, not wrappers around the complete source schedule.

- Open uses validate active roots/uses then call `route_internal` (`candidate_scheme.rs:4102–4108`); `route_internal` calls `with_route_transaction` (`lib.rs:18207–18209`). Incoming uses call the same wrapper (`:18959–18974`). Local routing begins a transaction and uses `finish_route_transaction_with_candidate_accounting` (`candidate_scheme.rs:4903–4910`). Its paused/scripted variants are test-only; production requires no pause budget.
- Begin obtains `state.intrusion.begin()` from the current graph (`lib.rs:9424`), installs its journal at `:9477`, then invokes the operation (`:9485–9503`). Under unchanged graph/journal identity the accepted r5 equation applies: checkpoint permission length and new domain-key list, matching publication journal, matching rollback removal, commit retention. These are conditional equations; the shown source schedule does not itself make every formal action transactional.
- On operation error, `finish_route_transaction_with_candidate_accounting` calls `rollback_route_transaction()?` (`lib.rs:9535`). Therefore either rollback error at `:9684` or `:9702` immediately returns an error from the wrapper; it cannot be turned into `Ok(value)` by that wrapper. Both exits occur after store rollback and intrusion/domain cleanup (`:9678–9681`) and before all row restoration. The result can contain a different error than the triggering operation, which is permitted here.
- `route_internal` directly returns that result. Incoming routing performs resource bookkeeping, but its sample-failure branch returns `sample_result.and(result)` and its tail returns either an error or the original `result` (`lib.rs:19025–19058`); it never changes an error result into success. `route_candidate_local_run` restores accounting flags/scratch then returns `result` (`candidate_scheme.rs:4966–4976`). The action dispatcher propagates these route errors, so the shown schedule/solve chain disposes the failed private attempt as above. No exact recovery theorem is needed for this chain.
- Local-use capture occurs inside the local route transaction (`candidate_scheme.rs:4940–4953`); operation steps put their temporarily owned frame back before applying `result?` (`:4959–4969`). The commit owner releases undo and commits completed local use before store commit (`lib.rs:9506–9532`). The r5 commit derivation remains conditional on same graph/journal identity. Retained test resume entrypoints do not demonstrate a production retry after a failed route.

## Capture publication and successful export

Definition source execution precedes SCC graph capture. Each member graph is staged before publication (`candidate_scheme.rs:2892–2909`); after ownership/accounting checks, the plan stores it in `state.graphs[position]` (`:2929–2951`). A resource sample follows publication, so graph-slot publication alone does not imply successful solve. Its error still propagates through the private solve chain. Another member or recapture may have already changed a private slot before a later error; that is likewise not an exported-result witness.

Capture constructs `negative_formal_roots` from the **current** algebra's `formal_domains`, reads each term in the same session store, and inserts only negative function/tuple endpoints already present in the capture endpoint map (`candidate_scheme.rs:2787–2799`). Capture returns its owned graph only after its final fallible sample (`:2824–2827`). This identifies the exact association lookup but does not prove endpoint-map correctness or original-image preservation under canonicalization.

Successful finalization moves `self.candidate_graph` into `FrozenInferenceData` (`lib.rs:20058–20064`), rather than reconstructing a graph from unrelated storage. Public export rejects nonempty solver errors and unauthenticated definition roots; it resolves `root_scheme_positions[root]`, takes that solved state's `graphs[position]` and returns a borrow of that state and graph (`shadow_apply.rs:2029–2054`). Permission projection filters permissions by the same definition owner, requires the current parameter domain and that exact graph's negative root, then traverses the retained permission path (`:2643–2665` and following). Missing associations/roots return `ArtifactMismatch`, not an out-of-image endpoint.

The original quantifier is unchanged: every successful projected endpoint must belong to the image of the originating construction in the original capture, with its occurrence/path identity preserved. This packet proves neither that quantified statement nor its negation. B concerns the originating lifecycle/association; C concerns canonicalization/store association; D requires successful capture/export. An internal published slot, offset reuse, unavailable root, missing active undo or rollback error alone supplies none of the required successful out-of-image endpoint witness.

## Remaining premise, boundary and recommended next action

The bounded derivation reduces r5's missing caller premise: visible production source scheduling uses a private attempt; route abort errors propagate to failed solve rather than successful export. Universal B remains open because this was not a complete transitive ownership/no-replacement audit across all invoked action/dispatch implementations. C's exact remaining equation is that capture endpoint interning/canonicalization maps each originating formal domain/path to its original captured image, retaining term-store identity through graph capture and later projection. D's successful-export consumer is located, but universal successful shape/path correspondence remains unproved.

No new unadmitted owner was opened or searched. The known next callback boundary is `crates/yu-solver/src/candidate_receiver.rs`: the graph plan's field-tail execution calls `candidate_receiver_positive_shape` at `candidate_scheme.rs:3530,3541`. Before claiming a complete successful-solve lifecycle, its operations must preserve the same private graph/permission-domain ownership or fail without publishing a solved owner. That path is declared as a module in admitted `lib.rs:215`; its bytes and implementations are UNKNOWN in this packet. STOP at this boundary; naming it is not permission to inspect it. Primary should first independently review this frozen caller/disposal derivation, then select either that exact callback-ownership packet or the separate C capture-canonicalization proof packet. No Lean or production promotion follows.

## Commands, coverage and resources

Commands: bounded `sed` reads and `rg -n` searches of the admitted owners; `sha256sum` of the nine owner pins and frozen r5/r6 records. All listed SHA checks matched. Some large combined tool outputs were truncated; later focused reads covered the cited central caller, abort, capture and export passages. No exhaustive source search or complete callback proof is claimed. Upstream HIR realization, unadmitted callbacks, all native transport, complete Call, all successful permission paths, and Lean verification are unverified. No source file changed.

One sequential lightweight shell process at a time; no Cargo, Lean/Lake, tests, probes, network, Git or descendants. CPU/RSS were not instrumented; static reads/hashes only, no heavyweight process. Wall-time bounded by the assigned 200-second packet; exact elapsed receipt unavailable. All writes stopped after this revision. Sole changed/new path is the exact leased handoff below. No independent review of this output claimed.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r6.md`.
- Baseline SHA: `3cc8a897fe08980576b1582952a95acab55f09d2` (primary-supplied).
- Changed dependency hashes: none; all direct pins authenticated as above.
- Claim/review status: qualified conditional static source evidence; UNREVIEWED; B/C/D and all parent/native/production gates OPEN.
- Checks already run: source reads/searches and SHA-256 pin authentication only; no executable checks authorized or run.
- Proposed research-checkpoint message: `research: trace formal permission production scheduling and failed-attempt disposal`.
- Shared-record deltas intentionally left to primary/curator: freeze this revision/hash, set worker STOPPED, request fresh non-author compiler_referee review, record private-attempt caller evidence and remaining transitive callback/C/D premises without gate promotion. No shared file edited.

STOP. Frozen revision 1; no unresolved descendant leases.
