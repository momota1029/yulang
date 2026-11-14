# Cycle 174: current recorded instances through mixed actual histories

Implemented in `GeneralDictionaryAgreedRefiningTrace174.lean`: 14 named
theorems, Lean 4.35.0 `--trust=0` build and audit PASS. Audited dependencies
are a subset of `propext`, `Classical.choice`, `Quot.sound`.

## Restricted operational relation

`At` has only two constructors:

* Existing `AgreedEvidence174.OrdinaryAt`, which is the actual enqueue,
  entailed-equate, full actual packet-guard installation, and guarded merge.
* Existing actual administrative refresh with a fixed-carrier Observation,
  unchanged normalized view, actual Refresh certificate, and an actual
  previously-unknown / newly-known source identity.

`Step` requires the focus to be Generated from the root. `at_actual`,
`step_actual`, and `steps_actual` embed every edge and finite path in the actual
relation. No edge accepts Instance, Evidence, RecordedCurrent, a final
Extension, or a purported transport theorem as an input guard. Reobservation
and changes to the source carrier or normalized view are excluded.

## Why not merely reuse the old feedback trace theorem?

`GeneralDictionaryFinishedTrace` already has the correct model-fixed transport
idea for a finite feedback path, but the requested result also quantifies over
packets installed at arbitrary intermediate points. Its `recorded_trace_instance`
starts with a packet already recorded before that path and a supplied old
Extension. The new module lifts the semantic transport core
`FinishedEvidence.instance_refinement` directly into the actual subrelation,
and proves the evolving journal invariant separately, including installations.
This avoids passing a semantic invariant as an operational assumption.

## Inductively constructed invariant

`RecordedCurrent registry state` means:

```
forall packet in state.current.packets,
forall model, Models state.current model ->
  Instance registry state.current.context model
    packet.site.occurrence packet.declaration.id packet.children
```

For old packets, actual step-model preservation gives the same final assignment
as an old journal model. Ordinary instance transport or fixed-view finished
inspection transport then yields the current instance. At a new installation,
actual SourceFormed -> shared SourceFormed supplies recorded evidence, and the
new packet's private context is exactly its ordinary extension. No extension
from earlier packets to the final context is required.

The empty initial journal establishes the invariant without a semantic input
assumption. `initial_trace_recorded` proves it for EVERY finite restricted
mixed path from an InitialSource, with arbitrarily many supported refreshes
and intervening installations. `initial_trace_evidence` combines it with
explicit child Evidence in the SAME final context and SAME final model.

The selected-node corollaries additionally take the displayed stability,
selection and policy premise (`defer=true` or absence of gap at that focus).
Available's enabled branch uses the existing stable-packet theorem; its
recorded branch uses the derived invariant. Thus no packet-membership inference
from Committed is needed, and no final RecordedExtensions premise remains.

## Boundaries of the result

This replaces the known-incompatible exact Extension invariant in a genuine
restricted execution fragment. It does not prove every actual step belongs to
that fragment, construct an arbitrary terminating run, produce child
dictionaries, eliminate the complete-policy gap, or close general B4
EvidenceNode/whereAccessible/canonicalLocalOrder. It does not change the
Cycle174 general field counts. Source Instance remains the existing
inspection-mediated judgment. The arbitrary descriptor-reobservation and
carrier/view-changing transport obligations remain open.

First elaboration failed only because the indexed `refresh` case exposes seven,
not eight, pattern variables. The corrected source builds successfully; the
failed log is not a claimed successful gate. No existing proof module was edited.
