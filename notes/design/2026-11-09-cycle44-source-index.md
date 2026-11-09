# Cycle44: named source identity to finite dynamic Index feedback

Data: arbitrary finite `table : List Nat` maps occurrence slots to source identifiers;
`requests : List (Nat × Nat)` gives named receiver/output obligations. These are
inputs, not extracted by a verified parser. The fragment is checked Index(box str).

Independent `Derived table s requests i`: seed ordinary string evidence, propagation
across occurrences of the same source, or a named Index request. Compiled finite
edges enumerate slot pairs matching a source identity or a named request.

Goal for all tables, states, requests, and slots: computed saturation membership iff
Derived. Output first conjoins the existing source-identity equations, then records
reachable string equations; output models iff initial models, coherent source
identities, and all Derived string facts. No consistency existence is asserted.
Alias transitions are source equality consequences, not executions of Index.
The existing actual Index producer can interpret only the request transitions.
General source parsing, arbitrary roles, and general B4 remain outside this bridge.
