# I-19: inspection-pending repair and local totality

Status: implementation plan, 2026-11-11. Scope: B4 target schema, not a
new language rule. Existing V2 definitions remain untouched.

The new V3 Local and Classify add inspectionPending after root pending and
both K2 reasons, before empty-candidate rejection. Empty rejection requires
both not RootPending and not InspectionPending. Root/candidate K2 requires
not RootPending but is deliberately not guarded by InspectionPending.
The lossless tree result, Completed projection and all five target quantifiers
are retained. The twelve B4Bridges obligations migrate without being discharged.

First prove functionality for arbitrary Vocabulary and SourceBoundary. Then
prove totality under excluded middle and the concrete local coherence fact
that one surviving key supplies exactly one child list. This coherence is NOT
a SourceBoundary assumption or an additional B4 bridge field.

There is an independent obstruction to I-19's unrestricted totality wording:
SourceBoundary.Survivor is an arbitrary relation. It can assert two child lists
for the same key, with all four flags false. Unique then fails, ambiguity by
distinct keys fails, and neither pending nor rejection holds. Prove this
countermodel and record a question before changing the target's meaning.
The actual future general candidate judgment should derive child coherence
from capture/allocation and canonical source identities, not assume it from
excluded middle. This affects frontierLocal, not the correctness of the new
inspection-pending guard.

Yulang2 comparison: read work/dots-audit ROLE-MORE-001/002/003/004/005.
Old candidate and advertised-where behavior is not a source of new semantics.
I-19 and the approved B4 draft determine the priority order; no new runtime
experiment is claimed. Known receiver plus unresolved inspection remains
pending unless K2 rejects it, as the draft explicitly requires.

## Verified first subgoal

The six V3 modules now pass a focused 411-job build, all 50 theorem declarations
pass trust-zero axiom inspection, and the diff gate passes. The stable
inspection-pending fixture also demonstrates an additional V2 behavior: with
no current survivors, V2 wrongly classifies it rejected; V3 correctly waits.
The explicit conflicting-child counterexample is proved, not speculative.

## Next subgoal: lossless source evidence readback

I-18 item 5 needs an adapter from source-indexed Evidence to the key-only B4
payload. Define independent recursive PayloadEvidence over a source occurrence
and key dictionary, then prove it equivalent to existence of an indexed Evidence
witness with exact erasure. This must retain every child, multiplicity and order.
Under explicit deterministic local children, prove that a fixed source root and
payload have at most one valid indexed witness. The arbitrary erasure operation
remains non-injective; no source identities are reconstructed without evidence.
These are prerequisites of evidenceNode/dictionaryRefl, not a source semantics
or a discharged general-source B4Bridges field.

The source readback and uniqueness subgoal is proved. A second adapter now
lifts actual Recorded inequalities at every dictionary node to equations in
every model of the shared State. The same source-indexed witness works for all
models; it is not chosen independently per child or assignment. A non-vacuous
fixture has source IDs100/101/102, two equal erased leaf payloads, and repeated
output equations. Its package constructor proves exact child determinism.
The general Packages relation must still be derived from declarations/captures.
Ordered child determinism and unordered PermutationInvariant semantics are
different interfaces; the uniqueness theorem does not silently conflate them.
