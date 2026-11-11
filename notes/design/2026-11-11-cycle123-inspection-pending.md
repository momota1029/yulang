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

## Next subgoal: runtime-payload sibling comparison

The B4 payload erases source IDs. Define its least structural equivalence under
sibling permutation, retaining selected keys and full recursive shape. Prove
source dictionary equivalence maps to this payload relation, and independent
payload evidence transports only when the concrete local relation is proven
permutation-invariant. Keep this condition separate from ordered-child uniqueness.
This supplies a concrete key-payload comparison candidate for item5; it does not
assume capture/allocation, source dictionary semantics, or final-state order
independence. The pending/rejected/ambiguous diagnostic tags are not collapsed.

The payload comparison and semantic-order adapters are now proved. The Unordered
package view retains a permutation witness for complete source occurrences and
the same located equations. It is permutation-invariant and idempotent. Exact
package child determinism becomes uniqueness up to permutation, not equality.
A distinct-key non-vacuous regression rejects reversed payloads in the canonical
ordered judgment, accepts them with corresponding source transport in the
unordered judgment, and proves the unordered judgment is not child-functional.
No role instances are fabricated: the concrete package relation is still the
separate missing declaration/capture bridge.

## Next subgoal: unique semantic dictionaries up to source-preserving order

For a local instance relation, expose the exact premise: at the same source
occurrence, two valid selected instances have the same implementation key and
child lists differing only by permutation. Prove by finite evidence induction
that any two valid source dictionaries at that root are DictionaryEquivalent.
Do not infer this premise for arbitrary role instances with overlapping impls.
Derive the premise for the Unordered view of key-and-child-deterministic exact
packages, then transport it to erased payload comparison. This connects the
comparison relation to genuinely unique local selection while retaining the
unimplemented general candidate-to-package premise.

## Next subgoal: connect deterministic child plans to actual declarations

Use actual GeneralDeclarations.Checked registry IDs, canonicalEmit, a fixed
per-key resolved capture/allocation frame, and an explicit stable source-ID map.
Define a dictionary emission plan for a visible declaration of the root role.
Prove same-key child determinism from checked unique declaration IDs, and exact
plan transport under actual registry/where reordering at a fixed frame. Do not
call this Plan a Survivor: head matching, candidate feasibility, source allocation
freshness and declaration equation semantics remain absent. The frame is data
that candidate inspection must derive, not a new arbitrary semantic oracle.

The semantic uniqueness theorem is proved by finite source-evidence induction.
It aligns children by their retained source occurrences, not by erased key
coincidence. Under local selected-key/children uniqueness up to permutation,
any two source dictionaries at the same root are DictionaryEquivalent. Actual
package constructor inversion supplies this premise for the distinct-key fixture.

The actual declaration plan bridge is also proved. Checked registry IDs imply
same-key declaration identity, hence deterministic complete canonical children
at a fixed frame. Plan is invariant under actual visible/where reordering. The
finite executable lookup returns some demands iff the independent Plan judgment,
and none iff no such plan exists. Real Wrap/Container named-output regressions,
a missing key, a wrong-role key, and reversed visible order all pass. The lookup
does not test head matching, ordinary feasibility or K2, and does not build the
resolved frame; it must not be reported as general candidate resolution.

The precise nonempty-survivor inspection-pending hole is additionally verified:
V2 has no Local derivation at that stable fixture, whereas V3 has exactly the
pending tree. Inspection-complete emptiness still rejects. The I-19 case repair
is complete; unrestricted abstract totality is still disproved as documented.

## Final coupling: actual plan lookup and stored equation evidence

Replace the arbitrary package child relation with the actual checked-registry
Plan. Keep only the declaration-to-term relation explicit, indexed by occurrence,
key and Located terms. Same-key child determinism then follows from the actual
registry, without an extra arbitrary Packages determinism hypothesis. A node
whose executable lookup returns the complete children, whose located atoms are
Recorded, and whose children carry stored evidence has equation evidence in
every shared-state model. This closes that adapter, not declaration-term adequacy,
head matching, candidate selection, frame derivation or general role Evidence.
