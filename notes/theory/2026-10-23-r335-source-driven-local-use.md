# R335 — Source-driven local-use reachability

## Outcome

`NO_SAFE_CODE_SLICE` for the R334 follow-up question. In the ordinary
`shadow-apply-candidate` lifecycle, every source schedule that can execute an
`Action::Local` finishes before `execute_candidate_field_tails` can refresh a
FieldTail capture. The successful refresh is the end of field-tail dispatch;
the only production continuation is candidate finalization. No source schedule
reopens between refresh and finalization, so a source program cannot perform a
later local use of that exact refreshed capture and then carry it through the
source-instance/frontier readback, member selection, and candidate publication.

This closes only that bounded reachability question. It does not close the
source/native, Simple-sub A/B, receiving, principality, catalog, or production
gates.

## Frozen source baseline

- Commit: `17e57af2c4605d7084c7d76792b115674776bbe2`
- `candidate_scheme.rs`: `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5`
- `candidate_source.rs`: `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b`
- solver `lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- `shadow_apply.rs`: `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d`
- `runtime/dispatch.rs`: `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873`
- playground `lib.rs`: `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4`

The audited files still match these hashes. R335 changed no source code.

## Source and lifecycle trace

1. `candidate_source.rs:2168-2173` appends each source owner's `WhereClause`
   actions to its schedule after the body actions. The action driver executes a
   `Local` action through `route_candidate_local`
   (`candidate_source.rs:2450-2465`). That route activates the obligation
   descriptors retained by the completed local route
   (`candidate_scheme.rs:4867-4896`). It is a source-schedule action, not a
   field-tail dispatch action.

2. During candidate graph planning, each definition root schedule runs before
   its graph is captured (`candidate_scheme.rs:2872-2905`). After the
   definition plan, every candidate member schedule runs and its completed
   graph is captured into `member_graphs`
   (`candidate_scheme.rs:2973-3027`). The production call-site census has no
   other root or member schedule caller outside this graph-plan path. Operator
   provider expression schedules also run inside that graph plan
   (`candidate_scheme.rs:2829-2842`, `3129-3142`).

3. `InferenceSession::execute` completes the SCC/source graph plan, then runs
   loose and expression schedules, accounts the store, and returns
   (`lib.rs:10637-10664`). The production source-schedule helpers are called
   from this execution path. `run_candidate` then orders the phases as
   `execute` → `execute_candidate_field_tails` → `finish_candidate`
   (`lib.rs:10672-10691`).

4. Field-tail processing drains active obligations into a local pending list,
   reads the current obligation through
   `candidate_field_tail_receiver_readbacks`, selects a unique member, and
   freshens that member's already captured `MemberGraph`
   (`candidate_scheme.rs:3433-3494`, `3504-3525`, `3588-3645`). This phase does
   not call `execute_candidate_source_root`, `execute_candidate_member`, or
   `route_candidate_local`; it dispatches captured graph data. The helper
   `candidate_field_tail_has_source_instance` is reached from receiver
   readback (`lib.rs:12227-12252`), so a readback is evidence consumption, not
   a source-schedule re-entry.

5. The success exit is restricted to no deferred active item, or to deferred
   template descriptors whose `template_owners` are nonempty. Only then does
   it refresh captured definition/local FieldTail state and return
   (`candidate_scheme.rs:3740-3780`). The refresh updates local capture fields
   and removes those residual descriptors from active state
   (`candidate_scheme.rs:3930-3991`). An unresolved concrete item instead
   returns `DeferredSelectionUnavailable` before the successful refresh exit
   (`candidate_scheme.rs:3782-3808`).

6. The deferred-readback wrapper takes its pre-dispatch receiver snapshot
   before calling field-tail dispatch (`shadow_apply.rs:1848-1877`). After a
   successful dispatch it checks for unresolved active selection; if the check
   remains true, it may take a diagnostic readback but immediately returns
   `DeferredSelectionUnavailable` (`shadow_apply.rs:1892-1902`). It cannot
   reach `finish_candidate` on that branch. If the check is false, it proceeds
   directly to `finish_candidate` (`shadow_apply.rs:1904-1906`). The ordinary
   wrapper uses the same `execute` → field-tail → finish order
   (`shadow_apply.rs:1921-1932`). `finish_candidate` itself rejects unresolved
   active FieldTail selection before producing `CandidateSolvedResult`
   (`lib.rs:10680-10691`). The receiver readback iterates only the active
   `source_field_tail_obligations` map (`lib.rs:12227-12235`); the successful
   refresh removes its residual records from that map. A diagnostic readback
   on the unresolved wrapper branch therefore cannot turn the refreshed local
   capture back into a source use.

Therefore neither production driver has a source action between a successful
FieldTail refresh and candidate finalization. A post-refresh diagnostic
readback can occur only on the wrapper's unresolved branch, which returns an
error before publication; it does not reactivate a local capture. The
helper-level activation calls in the R333 test do not change this lifecycle.

## Evidence limits

- This is a structural call-order result for the audited candidate lifecycle,
  not evidence that the original Yulang2 playground catalog works.
- It does not establish that every retained local descriptor is semantically
  correct or that any parent theorem is closed.
- No authentic source fixture was added because the proposed later source use
  is absent from the production phase order. No source code changed and no
  tests were run for this read-only trace.
- R334's narrower observation remains valid: its test directly invoked helper
  activation after refresh and did not demonstrate a source-driven later use.

## Independent review handoff

The source trace above was frozen at SHA-256
`37c234a8f2d3afbf4e3ceb19e26846ed112fb8b284fd4e6b2de0f51c52d4adec` and
received a fresh static review from `/root/r335_source_trace_review` in the
current session. All five bounded claims passed. The reviewer found no
blocking, major or minor compiler finding in the ordinary candidate lifecycle.

The reviewer also inspected the separate `candidate_receiver.rs` action
executor. It belongs to `solve_receiving_residual_experiment` /
`execute_receiving_assembly`; that unpublished experiment does not invoke this
field-tail refresh phase or publish a `CandidateSolvedResult`, so it is not a
counterexample to this lifecycle claim.

The reviewer confirmed the source hashes listed above, ran no tests and made
no writes. The source trace remains limited to ordinary candidate phase order;
this receipt does not certify descriptor correctness, source/native
correspondence or any parent gate.
