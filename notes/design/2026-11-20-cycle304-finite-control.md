# C304: finite control view without equating raw journals

The closed deferred-ladder proof classifies reachable raw states by two
observable ingredients: the length of the raw row table, and whether the
terminal source identity has any known normalized/nominal head. Compute
the latter by scanning the finite slots. Do not infer it from success
of a candidate or from an index in the historical packet list.

The quotient for arbitrary depth has states `(k, unobserved/observed)`.
Before promotion it can install at a non-leaf row or promote in place;
after promotion the sole abstract edge is the next list install. At the
known leaf there is no raw or abstract step. Every abstract edge from a
raw reachable representative lifts to a real kernel step, but not to
every raw representative of the target class. Infinite redundant-equation
branches remain distinct concrete states. The executable successor list
enumerates control edges, not raw refresh targets.

This view is a deliberately small I-54 source-fragment compiler; the
general classifier still needs the independent semantics described in the
diagnostic projection note, including feasible merged-class slices.
