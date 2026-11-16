# Cycle222: semantic support across administrative transitions

Target: the finite semantic dependency invariant needed by EvidenceNode's unresolved amalgamation bridge. This is not a proof of EvidenceNode.

The new module is independent of all cycle220 additions. It imports DefaultKernel208, DefaultTrace208 and Default214ActualJournal from the existing published baseline. No language semantics, selected predicate, transition, or target is changed.

For arbitrary total-journal states, `equate_models_iff` proves equality feedback preserves Models when the equality is entailed by all old journal models. `equate_depends` therefore retains any independently established finite semantic pool, even when the equation mentions names outside that pool.

An attempted blanket statement for arbitrary Administrative transitions was rejected during development: enqueue extends erased raw sites and can expose named requests to old live effects. The verified `enqueue_models_iff` keeps this exact residual: new Models iff old Models AND all registered effects are Live in the new core. `enqueue_depends` uses the old pool plus the finite live-class support `enqueueDelta`; it does not discard those requirements. This is not a closed counterexample to EvidenceNode.

For an actual reachable state and a generated focus, the existing `DefaultTrace208.generated_registered` proves the occurrence is already registered, contradicting enqueue's novelty guard. The new `reachable_administrative_models_iff` handles all four Administrative constructors: enqueue is impossible; certified refresh/reobserve use existing equivalences; entailed equality uses the new total-journal equivalence. `reachable_administrative_depends` retains the exact same semantic dependency pool through any such step.

This closes the administrative cases of the proposed semantic-support induction. Install and merge still need separate semantic delta/provenance arguments. No theorem here supplies protected Overlap, common packet/effect witnesses, ChoiceCompatible, or unconditional EvidenceNode. Constructor injectivity and conclusion-shaped assumptions are not introduced.

The correction to the initial plan was made before publication; no sorry or attempted blanket equivalence is retained. The source contains six theorems and one finite-support definition. A new audit inspects every declaration owned by the module, not just printed theorem names.

Yulang2: no new execution or new behavioral definition. These are transport theorems for already specified transitions, not a claim of fresh Yulang2 conformance.
