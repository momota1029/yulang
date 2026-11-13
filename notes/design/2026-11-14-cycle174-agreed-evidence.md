# Cycle174: policy-parametric Actual evidence

Draft, I-28/I-29. The center-bearing representation is Astra-owned; this cycle
uses the newly integrated ActualAgreed boundary without changing its definitions.
No claim is made that defer=true is language semantics: missing-sharing deferral
is an implementation restriction, and defer=false needs explicit gap freedom.

Goals: transfer ground initial-source termination and finite tree executor to
this Local; connect Available packets to current dictionary Evidence. Recorded
packets retain old contexts, so any ordinary-context extension obligation stays
explicit rather than becoming an Evidence assumption. General accessibility and
order independence are not assumed solved. New files only; frozen Audit/README
unchanged, imports appended, standalone audits.

## Implementation and scope review (cycle174)

The fresh integration is `52cab5b90a716a99dbc55e9413b311bf7179272f`.
The ground boundary keeps Astra's agreed Local while restricting Initial to
InitialSource, PointSource and GroundRoots. The noncomputable ground executor
is finite by the existing ground_progress theorem; it does not assert finite
resolution of recursive dictionaries. For the latter, define RoleStratified as
strict decrease on **every actual declared where-clause role edge**, then derive
where-accessibility for arbitrary current states from emitted clause metadata.
No model, readback function, or desired accessibility conclusion is assumed.

The independent executable producer computes truncated longest path heights
on the finite declared role graph and checks each edge against this candidate.
`check registry fuel = true` is exactly RoleStratified at the computed height.
`height_stabilizes` uses any existing rank only in its completeness proof;
`exists_check_iff` says some search fuel succeeds iff some role rank exists.
The check does not use that supplied rank. Search fuel is not an evaluator fuel.
No termination of unbounded certificate search is claimed outside this fragment.
A false check does not reject the Yulang program: fuel can be insufficient and
same-role structural recursion is intentionally outside the role-DAG fragment.

The checked certificate connects to `run_resolves_iff` and `completed_iff`
for any checked registry, policy, and ground-reachable state. This is exactness
against the current agreed Local, not language coverage or I-29's future
center-bearing representation. A diagnostic tree can have pending children;
no successful completed dictionary is promised. The diagnostic remains
noncomputable even though the declaration certificate checker is executable.

Available packet evidence is connected to the current ordinary context through
the full actual guard. Recorded packet evidence needs an extension from the
saved context to the current context. A genuinely operational no-refresh trace
fragment (enqueue/equate/fullguard install/merge) derives that extension from
empty initial journal, rather than assuming Evidence. Descriptor refresh and
reobserve are excluded; the actual chosen executor is not proved to stay in
this fragment. Recursive dictionary evidence shares a single current model
through all children and is conditional on a successful classification.

For the unrestricted ground boundary, pending policy supplies 11 of 14 bridge
fields; complete policy supplies 10. The per-registry role-DAG theorem does not
supply the unrestricted whereAccessible field. Remaining.history and GapFree
are deliberately sufficient conditions over a larger general agreed-reachable
universe, not a claim to have identified the weakest necessary obligations.

The nonleaf wrapOnly registry checks the declared role graph only. It has no
implementation for its child role, so it is not a completed-child-dictionary
success example. No new semantics decision was made.
