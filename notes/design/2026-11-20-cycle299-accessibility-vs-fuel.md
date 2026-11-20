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
