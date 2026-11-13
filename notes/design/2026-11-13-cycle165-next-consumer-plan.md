# Cycle165: captured parent, fresh-slot refresh, next producer obligations

## Verified checkpoint

The unchanged checked proposal113 now has an actual Shared parent installation.
`GeneralDictionarySharedCapturedModel` assigns old sources0/1/2 to
list(list int)/list int/int and patches only fresh producer endpoints lo/hi to
list int. It proves actual private state models, projection constraints and
materialization, hence the complete parent `BranchModels` witness.
`GeneralDictionarySharedCapturedGuards` derives inherited capture usability and
input coherence for **all** parent packet models, not just that witness.
`GeneralDictionarySharedCapturedInstallable` proves the current selected outcome,
source-head decision support, and Installable. `...Installation.step` is an
actual Shared transition with a nonempty resulting journal model set.

After that parent install, both emitted children are raw RootPending. Semantic
nominal tests at lo/hi do not themselves register new base slots. The consumer
source2 is still unknown. `revision_producer_pending` proves that every existing
`ReobservationSteps.Revision` preserves this producer pending state, since the
revision relation preserves the Known domain. This is a limitation of that
particular rule, not an impossibility for ordinary Refresh.

`GeneralDictionarySharedCapturedRefresh` completes the required ordinary
Refresh: an injective source/row embedding3→5 with IDs [0,1,2,lo,hi], retained
old descriptors0→1 and1→2, and new point descriptors list(2) at slots3/4.
The certificate's `exact` field is proved for **every** old journal model.
`endpoint_equation` derives lo/hi ≃ list(source2) from the parent's shape tests
and actual variable uses. It never assumes source2=int. New-slot support comes
from the already reserved allocation keys. `shared_prefix` is now a real
two-step Shared trace (parent install, refresh), model-equivalent across the
refresh and inhabited. Producer raw readiness is proved; consumer remains
pending.

## Next producer checkpoint, not yet an installation

`GeneralDictionarySharedCapturedProducer.candidate` uses producer declaration40,
the existing emitted producer site, the refreshed context, and exact bounds
[(3,4)]. Its report has **two** captures of name0 at point(2,2), with distinct
lo/hi argument origins. Thus allocation must perform the repeated-capture
lower-union/upper-intersection merge, not bypass it as a singleton.

The module proves a full finite `candidate.Holds model` witness. The private
merge constraints use genuinely fresh capture endpoints; their separation from
the old lo/hi endpoints follows from invocation identity and allocation
injectivity. Union/intersection idempotence discharges the repeated point
capture constraints. Projection sharing and the scalar-int named-output schema
are checked separately. No Prepared/Survivor/Installable or producer transition
is claimed.

`output_int` and `captured_int` are explicitly conditional: **if** the producer
packet holds, its associated output makes target=int; with the refreshed parent
journal, target≃source2 then gives source2=int. These are not assertions that
all models of the current two-step prefix already satisfy source2=int.

## Bounded next action

1. Complete producer Fresh, metadata/linkage, current Prepared/Unique/Joint and
   merge-closure obligations against the refreshed journal, using the already
   proved concrete branch witness. Do not reuse a source-only selected outcome
   without checking current packets/sites.
2. Use the separately verified `GeneralDictionarySharedCapturedInputReady`
   lo_ready/hi_ready certificates for current Shared DecisionGuard. Fresh heads
   are justified through trusted parent **input** facts and coherent readbacks,
   not original-source `source_ready` and not unsettled named outputs.
3. Verify the leaf producer's complete Shared PacketGuard and actual install.
   Only then use output_int/captured_int as journal consequences.
4. Construct a later model-preserving scalar refresh at existing source2, with
   its required support/readback certificate, before claiming consumer readiness.
   Finally prove the actual consumer action/evidence, not merely its emitted ID.

## Verification for this workstream

Focused Lean4.35.0 compilation and --trust=0 checks pass for all new modules.
Dedicated Cycle165Captured{Branch,Installable,Installation,Refresh,Producer}
audits print only propext, Classical.choice, and Quot.sound. No sorry,
native_decide, custom axiom, or full-project build was used. The final root-cycle
report records the immutable combined replay and publication hashes.
