# Actual-mode schema replay

Cycle160 Evidence-side auxiliary. No definitions owned by source/candidate/Step change.

Root associated requests are all `.actual`; structural schema recursion preserves
mode and nominal recursion resets to `.actual`. Prove all variable uses in these
schemas remain actual. For such a schema, one-way old→current replay only needs
`Fits oldInput value → Fits currentInput value`, not endpoint equivalence.
Outputs still use semantic equivalence and new capture origins must be retained
among old origins. Current tests/uses are subsets of old ones.

The allocation lemma uses the existing exact characterization of merged captures:
if each current occurrence was an old occurrence, old actual Fits implies current
actual Fits. Both merge models and nonempty sets are explicit. A singleton-current
specialization will require only old merge constraints. This is a soundness
component, not automatic provenance or general EvidenceNode.

## Scope elimination
The companion ActualSchemaScope module proves that the real pattern translator
never introduces a variable name absent from the original pattern, including
record sorting, variant plain-name joins, nominal argument traversal and deferred
branches. Combined with schema traversal and Declaration.Scoped, every generated
root-output variable is an input or output name. For singleton inputNames,
non-output entries therefore equal the declared binder; no schema-level scope
hypothesis is necessary. This is independent of endpoint values or point bounds.
