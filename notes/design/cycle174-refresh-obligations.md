# Cycle 174: history transport across actual refresh and reobservation

## Verified result and its exact scope

`GeneralDictionaryAgreedHistoryObstruction174` proves eight theorems, checked
with Lean 4.35.0 `--trust=0`; the eight-name axiom audit contains only
`propext` and `Quot.sound`.

Write `Extension h c` for `GeneralDictionaryOrdinaryTrace.Extension h c`.
It means an **exact context equation**:

```
exists reserved atoms allocated,
  c = <{ h.state with
           reserved := h.state.reserved ++ reserved,
           ordinary := h.state.ordinary ++ atoms,
           allocated := h.state.allocated ++ allocated }, h.interpretation>
```

Thus the source carrier, normalized view, nominal descriptors, seed,
constructors and interpretation do not change. In particular:

* For every contexts `h,c` and source identity `s`, `Extension h c` implies
  `Known c.state s <-> Known h.state s` (`extension_known`).
* Define `PointIndex c n := exists slot : Fin c.state.base.slots,
  slot.val = n and PointAt c.state slot`. For every `h,c,n`, an ordinary
  extension preserves this predicate in both directions (`extension_point`).
  The slot index here is a representation index, not a source identity.

Two consequences are verified, not conjectured:

1. For every `h,b,a,s`, `Extension h b`, `not Known b.state s`, and
   `Known a.state s` imply `not Extension h a`.
2. For every role set, journal state `b`, context `h`, and
   `revision : Revision b`, `Extension h b.context` and `Improves revision`
   imply `not Extension h revision.result.context`.

The actual administrative refresh rule supplies exactly the new-Known
premises in (1). The reobserve rule supplies exactly `Improves` in (2).
Both operations retain the packet list. Therefore the two operational
corollaries `recorded_refresh_failure` and `recorded_revision_failure` quantify
**every** tracked state, **every** old `RecordedExtensions` proof, **any one**
packet belonging to its journal, and **every** such improving operation:
`RecordedExtensions` fails in the resulting tracked state. The corollaries do
not require a model, registry check, or reachability premise; they are stronger
shape statements. They do not assert existence of a reachable improving step.
An empty packet journal is an explicit exception to this argument.

This is NOT an Evidence/B4 counterexample. It shows that preserving this exact
sufficient condition is the wrong next proof goal for a nonempty journal that
undergoes real observation progress. `Remaining.history` in Composition174 is
still a valid sufficient premise, but has this severe scope limitation.

## Where the semantic proof actually needs work

`SharedRecordedEvidence.stored_instance` already obtains, for every current
model `m`, an `Instance registry packet.context m ...` in the historical
inspection context. The journal's `Models` predicate retains each packet's
`Holds`; actual step model transport preserves the same supplied `m`.
Neither operation loses this historical result.

The unresolved conclusion is an Instance at the **current** context, with the
same root, declaration key, and complete ordered child list. Its definition in
`GeneralDictionaryRecursiveEvidence` includes all of:

* current `arguments context root = some bounds`;
* `Finished (report context declaration bounds)`;
* current `RequestReady`;
* exact children computed from current report bindings and allocation;
* current Metadata and BranchModels in the specified model.

Journal-model equivalence does not state equal inspection reports or equal
child emission. Refresh `Refines` transports old nominal descriptors through
an embedding, allows carrier/view change, and retains models backwards; it
is not the exact Extension equation. Reobservation fixes the carrier/view but
can replace existing nominal parameter intervals. `Revision.domain` preserves
only whether a descriptor exists, not its arguments. `Certified.raw/exact`
constrains models, not report equality. In particular reobservation does not
supply the `Refines.nominals` equality required by FinishedEvidence.

## Next lemma candidates (not claimed proved here)

1. **Actual/shared fixed-carrier fixed-view refresh adapter.** For every
   source-formed tracked `b`, recorded packet `p`, old
   `Extension p.context b.current.context`, fixed-carrier Observation `next`,
   `next.view = b.current.context.state.view`, Refresh certificate for that
   observation, and every model of the regenerated journal, prove the current
   Instance for `p`. The semantic core already exists as
   `GeneralDictionaryFinishedEvidence.instance_refinement` (and the feedback
   `recorded_refresh` adapter). Lift it through actual -> shared formation and
   `SharedRecordedEvidence.current_instance`; do not claim Extension survives.
   For repeated refreshes, use an inductively constructed restricted replay
   relation, as `GeneralDictionaryFinishedTrace` does, rather than demanding
   Extension from the original packet again.

2. **Actual reobservation adapter with a concrete finite report condition.**
   For every `b, revision, p`, construct the Observation with unchanged view
   and `revision.entries`. Given old packet-to-current Extension, formation,
   membership, Certified revision, and
   `InspectionTransport.PreservesAt registry b.current.context next
   p.site.occurrence`, prove the same current Instance in each model of
   revision.result. `instance_of_reports` supplies the transport. Then seek
   an operational proof of this report condition for the recorded node;
   `InspectionLocality` offers a sufficient unchanged-descriptor footprint.
   No claim is made that Certified + Improves alone imply that footprint or
   PreservesAt. Adding Instance/Evidence itself as the edge guard would not
   solve the semantic obligation.

3. **Carrier/view-changing refresh transport.** For every actual Refresh
   certificate and old packet instance in a final journal model, establish a
   source-identity-compatible argument lookup, report/capture transport along
   `refines.base.embed`, readiness, and *exact* allocated child occurrence
   equality. This needs more than `Refinements.assignment_transport` and
   `fits_transport`, which already handle the model interpretation. A
   source-renaming law for a complete report and a commutation law for
   `Allocation.children` are concrete missing interfaces. Whether unrestricted
   certificates suffice for these stronger equalities remains open; do not
   infer it from model equivalence or claim a counterexample without one.

No frozen cycle174 source was modified during this investigation. The added
obstruction module strengthens the report's limitation, not its B4 field count.

## Same-cycle follow-up

The single-refresh portion of candidate 1 is now implemented in
`GeneralDictionaryAgreedRefresh174`: actual formation, current-model Instance
transport, final-context child Evidence to parent Evidence, and an ordinary
initial trace followed by an actual improving refresh. Extension is required
only **before** the refresh. Repeated refresh replay, arbitrary reobserve,
carrier/view-changing refresh and the general B4 history field remain open.

## Later same-cycle correction to follow-up status

The restricted repeated-refresh replay mentioned as still open above is now
implemented in `GeneralDictionaryAgreedRefiningTrace174`: arbitrary finite
interleavings of actual ordinary rules and actual improving fixed-carrier,
fixed-view refreshes derive a current-instance invariant from empty journal.
New installations are included. Stable selected-node evidence at such endpoints
uses this derived invariant, without post-refresh ordinary Extension.
General descriptor reobserve and carrier/view-changing refresh remain excluded;
the unrestricted B4 field is still open. See `cycle174-refining-trace.md`.
