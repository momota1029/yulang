# Draft: candidate-guarded source/equation carrier

Scope: int-only capture-bearing source templates, fixed associated receivers.
The cycle23 first-hit support failure is an implementation boundary, not a language
rejection. spec 6.3 requires delaying final choice until sibling stabilization.

Data: a state-independent finite list of (source node, candidate declaration,
associated request). An explicit Boolean branch mask is supplied per source and
candidate. No policy for choosing this mask is introduced. At an observation state,
a candidate guard requires the mask and its own singleton-declaration producer to
match; no earlier competing hit can hide it. Reach uses these candidate edges.

Executable: finite Horn closure of those edges; filter retained equation records by
reachable source and active candidate. Independent judgment: paths of enabled
singleton candidate productions, and associated declaration derivations.

Goal, for every checked registry, source root, mask, observation, annotation map,
associated environment/wellformedness, seed and assignment: collected constraints
have exactly the seed models satisfying all active guarded annotation equations.
Mask and observation are explicit inputs, not successful-run certificates. This is
not a choice policy, feedback fixpoint, language typing, existence, uniqueness, or
B4 theorem. Taking a mask that enables incompatible alternatives must NOT be
interpreted as unconditional language conjunction. Disabled records remain in the
carrier and can be reactivated after observation changes.

Read-only review: the mask is keyed by source node and candidate, not full
ancestor path. Correlations between merged ancestor alternatives are not retained.
This is deliberately a metadata carrier theorem, not branch-local language semantics.
