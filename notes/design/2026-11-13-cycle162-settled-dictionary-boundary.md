# I26 settled support and dictionary selection

This package uses Astra's new settled boundary unchanged. It separates semantic
Evidence (same predicate as the Value boundary) from selected/completed dictionary
classification (now additionally guarded). No implication from new Stable to old
Stable is used. No general V5 evidenceNode is claimed.

Prove: selected Local iff old Value selected Local and settled DecisionGuard;
settled-pending excludes selected Local, selected Classify and completed selected
readback, including a pending child of a selected parent. Map new reachable
states to old Value reachability so existing history lemmas remain usable.
Positive converse must explicitly supply the new DecisionGuard, not infer it
from ordinary model Evidence or old Value selection.

## Selected-descendant exactness follow-up

The parent's GuardedClassification supplies the forward transfer from an old
selected dictionary under GuardClosure. For the converse, align each OLD selected
child list with a NEW classified parent's child list using old Local functionality
and the one-way projection. Every finite old-child path then retains a selected
new classification, hence a root DecisionGuard. This establishes an exact
old-classified AND GuardClosure criterion, not a guard for unrelated demands or
a semantic Evidence theorem. The module depends on the parent's projection and
guarded classification modules; it does not modify their definitions.

## Conditional full-tree Evidence

The general new-boundary node rule still needs Joint. For a finite selected
classification, recursively lift this rule to Evidence, demanding actual settled
Stable and selected-key Joint only along the new selected-child graph. NodeClosure
is explicit and includes the root; inherited child closure follows by path
concatenation. Reachability is shared for the whole final tracked state and removes
merge closure through the parent's new rule. No child Evidence is assumed in the
full-tree theorem. Models are final-context models, never all original models.
This is conditional soundness, not a completed unconditional boundary EvidenceNode.
