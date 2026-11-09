# Cycle29: ordered diagnostic representation

Draft, 2026-11-09. Scope: existing finite source diagnostic carrier.

Data: fixed registry/root, shared choice table, observation, existing Tree with ordered candidate/child lists. Independent equivalence: at every route and registered declaration the conjunction of table membership and Candidate holds on one side iff the other. Execution: unchanged diagnostic builder with its internal Paterson depth.

Goal: for all tables a,b and observations s,t with that named equivalence, build/diagnose produce literally equal Trees. This preserves the existing builder's order and multiplicity, not only route membership. Then prove that every Valid/Stable table has a searched canonical representative with exactly the same diagnostic Tree. Reordering or duplicating table entries cannot change that Tree.

This is representation invariance, not spec6.3's full declaration-order invariance: registry/child-source enumeration remain fixed. Missing occurrence indices in the existing route carrier are not recovered. No semantic dictionary interpreter, final classification, solution existence, or driver convergence is supplied. In particular this does not identify two different stable choice sets.

Implemented strengthening: atom-membership-equivalent states with an explicit common model yield equal int materialization, hence equal endpoints and full ordered trees. Consistency is named, not inferred.

Boundary checked in a separate Lean module: two slots x,y; state A has x=y and y=int, state B has x=int and y=int. Their model sets agree for every assignment and have a concrete all-int model. The direct detector leaves x unknown in A and materializes x as int in B. Therefore arbitrary model-equivalent normalization cannot replace the atom-membership premise without changing the detector or its specification. This is a decoder limitation, not a new language decision.

Executable local repair: `CommonRoleDiagnosticEvidenceTransfer.normalize s i j base` scans for both variable edges i≤j and j≤i and both scalar bounds j≤base and base≤j. Only if all four are present does it append the implied direct scalar pair for i. The checker is proved equivalent to independent Transferable evidence. Every assignment is preserved in both directions, without a consistency assumption; successful int materialization additionally uses an explicit model to rule out conflicting direct witnesses. The concrete chain example is repaired computationally. This is one checked transfer, not a full saturation engine or complete semantic decoder.
