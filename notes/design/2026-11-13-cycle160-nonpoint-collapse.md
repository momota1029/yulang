# Nonpoint collapse bridge (cycle160)

For the existing depth-two `SemanticCollapse.Shape`, drop the point-leaf
restriction from current private propagation/selfChecks. A current self-check
is either reflexive or the retained first leaf check, already present in the
historical private state. No new semantic rule is introduced.

For actual-mode variables, a value fitting the old intersection fits each
old occurrence, hence the retained first occurrence. This one-way implication
does not imply endpoint equivalence, and lower/upper-mode schemas are excluded
from the schema replay extension. The terminal branch wrapper will combine
this with the separately proved actual-only schema invariant.

Proof obligations: old private Models + current snapshot Models imply current
private Models; old capture Fits implies retained capture Fits; old projection
semantics already imply new projection semantics by existing current_projection.
The eventual full branch theorem still requires Shape, one binder, terminal
requirements and current base model. It is not general EvidenceNode.
