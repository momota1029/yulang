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

At this checkpoint there is **no claim of Stable for the installed state** and
no general V5 evidenceNode closure. A further stability proof would need to
exclude every enqueue/install/merge/refresh/equate/reobserve update. Merely
having selected and installed the root does not establish this.

Yulang2 x-oracle X13-X16 was consulted for identity/interval context only;
this exact named-output recursive program has not been run on Yulang2.
