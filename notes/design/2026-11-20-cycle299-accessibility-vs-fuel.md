# Fuel and selected-edge accessibility

No arbitrary rank is necessary for the declarative existence proof: map each
faithful table edge to the independently defined source `Child` relation and
pull back its accessibility proof. For a closed read table, a known row
admits a result at some finite fuel iff the table's backward child relation
is accessible at that row. Success is monotone in fuel. To lift the forward
direction, every member of the **whole ordered** child list must have
succeeded; to lift the converse use finite maxima over child fuels. The
proposition about existence is not an executable time bound. Implement a
separate bounded rank witness finder/checker with unknown when no finite
test suffices. Include self-loop and missing-row controls, both different
from a semantically rejected source. Do not reinterpret accessibility of
selected edges as raw kernel termination.

A closed finite table with an explicit complete domain admits a computable
bound `domain.length` for any accessible lookup, without an a priori rank.
Induct by erasing the immediate ancestor from remaining permissible indices:
an accessible relation excludes any return to that ancestor, so one
index can be removed per edge. Select the smallest successful fuel within
the bound to get a strictly decreasing numeric rank. The check does not
prove that the provided domain covers the original B4 source; coverage and
faithfulness carry separate hypotheses.

A successful faithful read proves accessibility of the **actual source
where relation** at the decoded root, not merely the encoded table.
Every semantic child of a selected row must also be one of that row's
exact ordered children by independence and functionality of `Local`.
Induction on fuel then certifies all subtrees. Conversely, source
accessibility pulls back to a closed table, so it gives a dictionary
result for a known initial row. In a finite covered table, both
directions combine with the explicit size cap. This is a per-root
post-snapshot result, independent of raw Step accessibility.

For a faithful closed table with a known root and a complete finite index
domain, the bounded dictionary reader is now exact against any independent
`B4TargetV8.Classify ... (.selected d)` derivation. The reverse direction
uses its finite ordered derivation only in the proof of completeness, not
in the implementation. A bounded failure under these hypotheses means
no finite *selected* derivation; it is not a diagnostic of rejection,
ambiguity, or an unexplained table which fails those hypotheses.
