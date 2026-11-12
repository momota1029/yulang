# Finite-arity closed observation certificates

Remove only the binary-branching cap from ClosedRequests.Tree. New Tree has scalar and nominal constructors; a nominal node carries arbitrary finite n, n exact source slots, n child queries and n recursively certified children. Recorded descriptor arguments must be precisely List.ofFn of point type intervals. This retains no-variable/no-row/no-fresh-target restrictions and never opens nominal bodies.

Intended result: schema variables=[] and unknown=false; every actual indexed nominal test has an observation witness and Holds in every source model, hence generated Models for finite request batches. Old scalar/nullary/unary/binary Tree embeds. Arbitrary arity must retain exact index-to-source correspondence, not just arity equality. Structural coverage for arbitrary reachable states is not claimed.
