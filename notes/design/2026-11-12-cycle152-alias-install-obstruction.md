# Cycle152: what different current alias keys actually block

Fresh I25, cycle151 report and the disjoint-output residual were read. This is
an investigation of general `evidenceNode`, not a new transition definition.

`Checked` requires unique declaration IDs, not disjoint heads.
`MergeGuard` carries same inputs and recovery support; it does not require
selected keys to agree. Consequently these definitions do not immediately rule
out the cycle151 proposed disjoint-output selection conflict.

The new small theorem only rules out **installation at the conflicting focus**:
actual support selections with distinct keys at related sites imply every
packet for that focus fails `FeedbackSteps.Installable`. That follows because
Installable includes Joint. It does NOT prove Stable: administrative enqueue,
refresh, equate, reobserve and merges still require separate exclusion. Nor does
it exhibit the hypotheses or disprove any V5 bridge.

A related simplification: `RecursiveEvidence.Instance` does not include Linked
or Fresh, whereas candidate Prepared does. Thus a proposed future child with
an unregistered output source is not automatically ruled out as Evidence; its
failure of Linked can block enqueue while Evidence is still a separate proof
obligation. This is a definition inspection, not an existence theorem.

The bounded next construction should first establish the checked declarations,
real parent installation + merge + certified refresh, and both actual Local
selections. Only then attempt global Stable and same-model child Evidence plus
parent non-Evidence. Do not replace the shared model by per-candidate witnesses.
Existing source IDs for private output binders are occurrence-indexed, so the
old same-binder sketch remains invalid. General V5 remains 8/14 unresolved.
