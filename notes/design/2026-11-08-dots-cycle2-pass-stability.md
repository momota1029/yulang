# Semantic stability of the fixed structural recursive pass

The existing structural producer and update function do not depend on the
ordinary state; state gating can suppress descent only when the prepared state
has no models. For an individual final model, such suppression is impossible.

Define Good(root, assignment) independently: every structurally reachable request
has compatible generated capture obligations. Prove the actual recursive pass's
final model condition iff the initial state is modeled and Good holds. This
state-independent characterization yields semantic idempotence of a second pass.

This is not syntactic stabilization (duplicate atoms may keep accumulating),
trace equality, or a theorem about the future state-narrowing source producer.
