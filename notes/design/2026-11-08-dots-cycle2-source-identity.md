# Cycle 2 source identity bridge (partial)

Data: a finite list of source-node names records endpoint occurrences. Each
occurrence keeps its own ordinary slot; repeated source names generate two
ordinary inequalities between their slots. Names are explicit identities, not
structural equality of Ty values.

Independent judgment: an assignment is coherent when every pair of occurrences
with equal source-node names has Common.Equivalent type components. Executable
atoms enumerate all equal-name pairs. Prove their exact equivalence to coherence,
then append to a grammar-checked state and use the actual ordinary solver.

Boundary: this does not derive source names from parser/graph nodes or establish
closure of a dynamic request graph. It does not identify effects, only types.
A source valuation pulled back to occurrences satisfies these equations. Appending
fresh occurrences preserves all old source identities.
