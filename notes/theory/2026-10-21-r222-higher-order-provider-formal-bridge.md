# R222 — Higher-order provider-to-formal bridge

## Question and disposition

This probe asks whether the authentic `repeat loop` provider argument is
source/native-related to the callback formal `f` whose first `f z` application
owns a later `Work::Bound`. The exact higher-order source is the accepted R221
fixture in `crates/yu-solver/src/shadow_apply/local_source_observation.rs`.

Disposition: **source-native evidence; bridge not established**. The observer
locates both ends and confirms the callback formal's own native registered
root, but exposes no occurrence-specific edge from the actual `loop` provider
to that formal root or to the callback WorkBound lineage. This is a gap in the
available records, not evidence that no semantic relationship exists.

## Evidence

- Ordinary `CandidateInference::solve(hir)` admits the exact source with no
  solver errors or candidate conflicts. The provider Call is occurrence 26;
  its source callee is `repeat`, its actual argument is `loop`, and its
  `formal_registration()` is `None`. Its `pending_construction` suppliers are
  `OriginalGenCall0`, `ArgumentReifyAndWholeCarrier`, and
  `ReceiverDispatchAndCompleteResultFutureInterfaces`.
- The callback call at Apply occurrence 19 has a source callee `f`, registered
  formal `f`, and lexical parameter use at occurrence 20. Its native registered
  root is positive Value variable 31, matching the callback consumer's native
  callee view. The callback formal Name has no retained `fresh_use` route
  (`None`, zero rows); the actual `loop` and `repeat` Name uses expose 20 and
  16 rows respectively.
- The callback `Work::Bound` is occurrence 24, with processing relation 146.
  Its exact source group includes Apply occurrence 19. Its raw lookup is
  `BoundKey(Effect(21), Positive, Effect(31))`, transported to owner Effect(46).
- The loop Lambda slot-4 source bound remains
  `BoundKey(Effect(5), Negative, Effect(41))`; its checked Local `FreshUse`
  image is `BoundKey(Effect(73), Negative, Effect(69))`. The repeat Local route
  maps callback formal item Effect(31) to Effect(57). Complete alias history
  keeps source items 41 and 31 separate; no WorkBound selects item 41 or 69.
- The source-call fact endpoints and recursively expanded function-term
  structure have no directed or undirected path between the provider argument
  native term (Term 452) and callback formal callee term (Term 258). The two
  source calls expose distinct fact roots. No `Replay` or transport witness
  in these existing records joins the provider's actual argument to the
  callback formal's registered root.
- Complete forest event replay still matches the final forest snapshot; all
  extrusion starts have matching finishes. This validates the bounded trace,
  not the missing provider/formal correspondence.

The earliest unavailable edge is the local-call application bridge at
`repeat loop` occurrence 26: the retained `CandidateSourceCall` has no formal
registration for the callee's higher-order parameter, while the public source
and native observations do not expose the actual-to-formal transfer. An
occurrence-specific constructor/consumer witness for that transfer is needed
before the callback WorkBound can be attributed to the loop slot-4 lineage.

## Verification and scope

- `cargo test -p yu-solver --features shadow-apply-candidate r222_higher_order_provider_formal_bridge -- --nocapture` — passed (1 focused test).
- The ordinary `yu-playground` suite and sprint tooling checks are recorded at
  integration; they are smoke/static evidence, not theorem closure.
- No production behavior or inference semantics changed. No independent review
  is claimed. R71 and R72 remain OPEN; this result does not prove or refute the
  original computation-forwarding preservation theorem.

## Next evidence target

Trace the local binding application constructor for `repeat loop` from the
actual `loop` source Name and its Local FreshUse rows through the callee's
argument-function component to the registered `f` parameter root, then join
that exact path to the callback WorkBound relation. Keep source occurrence,
polarity, effect rows, and all transfer witnesses explicit. If that constructor
still does not retain the edge, record the precise missing source/native
artifact before changing implementation.
