# Cycle152: a real named-output recursive dictionary

`GeneralDictionaryObservedInitialExample` preserves cycle151's declaration
`Wrap (List a) where Display a; out = Int` in a source with identities 0,1 and
seed1. `ObservedInitialSelected` proves actual supported selection;
`ObservedInitialInstallation` constructs the real guarded support Step.
Initial is **not Stable**, because this step is enabled and not committed.

The singleton registry does not contain Display Int. `ObservedInitialReadback`
therefore proves absence of any child Instance/Evidence in any context/model.
That is a registry-completeness diagnostic, not a general V5 counterexample.

The separate `ObservedCompleteExample` adds the existing checked scalar
`intDisplay` declaration. It does not modify the original failed example.
Its parent still requests exactly `[app 2 [] -> source1]` in actual mode, and
still emits exactly one actual where-child. `ObservedCompleteEvidence`
constructs the child's scalar Shape and whole two-node dictionary for **every**
source Models assignment. No Joint, Evidence or BranchModels is assumed.

`ObservedCompleteSelected` repeats actual parent selection with the extended
registry; the scalar declaration has role0 and cannot compete for the role1
root. `ObservedCompleteInstallation` proves an actual guarded install and
Reachable of its result. `ObservedCompleteFinalEvidence` shows all final Models
are exactly the original source Models, transports the full dictionary in the
same arbitrary final model, and bundles Reachable, an inhabited final journal,
nonempty parent output, one actual child and full Evidence. These are auxiliary
soundness facts, not execution completeness, principality or a general bridge.

The later `ObservedCompleteClosure` and `ObservedCompleteStable` now exclude
every enqueue/install/merge/refresh/equate/reobserve update and prove actual
Stable at the reached state. Cross root/child merge is impossible by different
roles, all further installations are semantically committed, and fresh source
observations are excluded with explicit separating models. `PointClosed` handles
reobserve. This is not an inference from mere root selection.

`ObservedCompleteClassification` independently constructs final Prepared,
Survivor, unique Local and source-supported decisions for parent and child;
actual B4 Classify is the successful two-node tree. Its final bundle combines
Reachable, inhabited Models, Stable, Classify, nonempty named output, one child,
and Evidence in all final models.

`ObservedCompleteCoverage` proves the actual ordinary trace and the recursive
ObservedStableCoverage obligations; no such inputs are assumed for the fixture.
The parent uses historical packet membership (including its named output),
while the unrecorded scalar child uses structural coverage and a proved
singleton alias class. Thus this instantiation does NOT establish unrecorded
named-output coverage in arbitrary states. General V5 remains 8/14 open.
All targets are already observed scalar slots, not fresh or non-scalar outputs.

Yulang2 x-oracle X13-X16 was consulted for identity/interval context only;
this exact named-output recursive program has not been run on Yulang2.
