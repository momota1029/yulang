# Cycle 1: candidate-local ordinary propagation

Status: Draft implementation boundary, instruction I-1, base c6bdf6b3c.

The first cycle closes a finite ordinary-slot boundary, not full source
`resolve_exact`. For each visible scalar head, generate equality constraints
between the request slot and that head, retain the entire old state, and run
the existing ordinary solver BEFORE collecting candidates. Candidate-local
constraints never become the shared state merely because one candidate
remains. Associated equalities are distinct incoming shared constraints.

Data: scalar candidate (key, base head); request ordinary slot; grammar-checked
ordinary State. Independent Fits judgment quantifies a single assignment
satisfying all old atoms and both directions of the head equality. Execution
filters candidates using the actual ordinary solver. Target: for every state,
slot, candidate list and candidate, membership in execution iff original
membership and Fits. This is candidate feasibility, not final role selection,
K2, source lowering, or saturation.

Example goal: an initially unconstrained slot admits int and str candidates;
adding an independently supplied associated equality to int removes str.
This tests shared-state filtering, but is NOT the full Parent/Left/Right
source example until associated declaration generation and lowering are joined.

Allocator work separately addresses exact source identity in finite tables.
Nominal semantic adequacy and total source graph lowering remain explicit.
