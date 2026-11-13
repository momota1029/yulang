Bounded diagnostic design (cycle174)

A generic `runFuel protocol fuel request` structurally recurses only on fuel.
Zero returns a placeholder pending tree; this fallback has no language-semantic
meaning and is never asserted exact without a sufficient-fuel certificate.
Positive fuel observes the fixed protocol frontier and recursively maps all
selected children. With FrontierExact and strict natural edge rank, rank(root)
< fuel proves a complete Resolves derivation. The concrete role-DAG certificate
provides that rank, while computedHeight <= roleNodes.length provides uniform
fuel roleNodes.length+1. At the ground final state's exact frontier, existing
executor exactness identifies the finite recursion tree with its diagnostic.
This bounds diagnostic child depth, not saturation Steps, and does not make
classical frontiers or final-state selection computable.
