# Cycle201: same-model structural head realization

The next missing component can be proved for an existing finite nominal tree
head, without any total packet semantics or unnamed-output restriction. Reuse
GeneralNominalTreeFacts.private_models rather than substitute an existential
Prepared witness. Existing TreeBranchShape adds variable clauses and no root
outputs; those extra restrictions are not needed for this head-only theorem.

HeadTree stores the existing tree, its injective binder names, exact inputNames,
inspection query and packet bounds. It contains no Models, Holds, Instance,
Evidence, baseline, or completion premise. For each assignment satisfying the
packet context state, the existing structural tree proof yields the actual
private HeadModels in that SAME assignment. With a current Frame, journal Models
supplies the context-state validity. Combine this with cycle201 input-variable
assembly to remove the common HeadModels assumption: only the common current
journal/effect model is supplied, and the structural tree supplies its head part.
Named root scalar outputs remain allowed. V7 selected evidence still needs
choice compatibility and one common effect model; this work does not assert
that selection alone supplies either. A current-model version need not demand
global existential completion at empty-model snapshots.
