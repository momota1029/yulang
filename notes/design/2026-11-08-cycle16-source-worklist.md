# Cycle16: fixed-state actual-source worklist (Draft)

Scope: int-only unary capture-bearing source adapter, arbitrary checked registry,
root and ordinary state. This is NOT the state-changing saturation theorem.
Data: computed source closure from cycle15; nodes are its membership subtype.
Actual edges use first-hit production at the given state and source extraction.
Independent reachability: root and one actual source-child step. Executable:
finite Horn worklist, each node inserted once, computed capacity, no external fuel.
Target: for all registry/root/state/node, worklist membership iff reachability;
Nodup, finite capacity, closure under actual children, no extra reachable node.
The missing state-changing bridge remains: invalidate/revisit a parent after new
ordinary evidence, account for newly enabled candidates, prove finite new facts.
This fixed-state kernel is a reusable component, not B4 or dictionary selection.
Yulang2 x-oracle X13–X16 does not establish this scheduler; no runtime claim.
