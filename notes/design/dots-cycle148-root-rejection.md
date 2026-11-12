# Cycle148: current emission is not selected in the revision fixture

`GeneralDictionarySupportRootRejection.lean` settles the root's actual support
frontier in all three inspected snapshots:

- original cycle147 revised `finish`: rejected, never selected;
- cycle148 point-closed `pointFinish`: rejected, never selected;
- cycle148 explicitly refreshed `after`: rejected, never selected.

The root's point descriptor says source0 is nominal(source2). The historical
packet already forces source2 equivalent to nominal(source2) in every journal
model. Hence source0 and source2 are equivalent. Observing the actual nominal
argument at source0 therefore creates a self-argument edge at source0 under the
existing feedback K2 definition. The concrete journal model makes this a
nonvacuous cycle. The original snapshot does not need to wait for source2's
Known descriptor: its historical packet already entails the self-equation.

The module proves actual `Local ... .rejected` judgments and, using existing
local functionality, excludes every `Local ... (.selected key children)` at
the root. Thus the historical generated-child gap is an obstruction to naive
syntactic current-emission transport, **not** a counterexample to the general
V5 GeneratedChildren obligation. In particular, the original gap fails both
Stable and actual-selected premises; those failures are now proved rather
than merely unestablished.

No global Stable claim is made for the last refreshed snapshot, and no general
V5 obligation is discharged. All existing transition and semantic definitions
remain unchanged. Focused Lean4.35.0 --trust=0 succeeds without warnings; twelve
key exports were individually audited and use only propext, Classical.choice,
and Quot.sound. No full build was run.
