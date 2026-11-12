# Cycle149 finite associated materialization

Generalize the prior singleton associated-output theorem to arbitrary finite
root demand output lists and arbitrary finite associated equation lists.
Every requested output target is the already constrained nominal head source;
every actually looked-up associated right hand side translates to the inspected nominal query.
The declaration remains checked and terminal; finite binder sharing remains
arbitrary. Derive generated materialization, rather than assuming it.

Proof plan: schema model validity restricts along test/variable membership;
finite folds of copies of a schema inherit validity including cross-copy
coherence. Extract requests from actual rootRequests and apply the checked
terminal elimination of emitted where clauses. Combine this with the existing
source/coherence/merge characterization of BranchModels. This is a helper for
the same-model V5 boundary, not a proof that all selected foci have this shape.
No singleton or nonempty output restriction. Unknown requested output names
remain a separate RootDefined obligation, and are not certified by this lemma.
