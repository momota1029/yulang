# Cycle188 — initial common model and centered variable inspection

Status: Draft implementation plan. Target: the remaining common-model input to
cycle187's head extension, toward WF/V6 EvidenceNode. No boundary semantics change.

For every initial point-root state and current candidate Frame, Prepared supplies
a HeadModels witness at the exact located bounds. Its source-model component also
satisfies the initial state. This removes the separately assumed common assignment
at initial states, not at arbitrary reachable states.

For arbitrary finite variable-only queries, with point bounds and source centers
at those bounds, cross-capture constraints imply all centered projection clauses,
including repeated variable names. Prove this from actual inspection output,
not by assuming ProjectionModels. Then compose the initial witness with the
finite conservative head extension. Structural/nominal recursion and new outputs
remain separate; no general EvidenceNode closure is claimed.

Yulang2 oracle: fresh work/dots-audit x-oracle, X13 and C3-PARENT historical
observations read. No new runtime claim or language design choice is made.

Checkpoint: actual initial Survivor constructs its own Frame and exact children;
VariableQueries at that Frame now yields HeadEquations with current/branch/
centered constraints, without assuming a simultaneous model. General recursive
point-origin enrichment is next: raw nominal origins must be transported, not
replaced by the false assertion that all nested intervals are points.
