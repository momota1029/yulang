# Cycle194 final classification (Draft)

Objective: certify final parent and child V6 classification for the existing actual
WF Display(List Int) fixture, after cycle193's genuine installation. Reconstruct
the current-context parent plan, prove current uniqueness and no output conflict,
then assemble the recursive Classify judgment. Investigate actual Stable separately;
a recursive Evidence certificate is not itself a stability argument. No definitions
or semantics change. General reachable-state EvidenceNode remains open.

## Verified outcome

The exact WF final parent Local and recursive V6 Classify are now proved. Actual
Stable is separately proved by exhausting all actions: generated nodes are precisely
root or child; each possible enabled installation is already committed; source-model
variation prevents reserved unknowns from becoming known under exact refresh;
context completeness blocks new equality; existing point descriptors block revision;
raw and centered merge closure blocks alias updates. The old support fixture's raw
journal is not definitionally equal to the new shared-origin journal, so stability
was proved directly rather than asserted by a cast.

A separate general finite Build classification lemma has the named unproved
SelectionsPersist contract. This requires actual enabled local selection to remain
selected after arbitrary ordinary traces; it does not assume recursive Classify or
Evidence. Later siblings are accounted for at a common final state. No global proof
of this transport contract, general EvidenceNode, or canonical executor equality
is claimed. The concrete Stable/Classify theorem does NOT depend on this contract.

## General semantic node factorization

The older `InstallableEvidence190.generated_evidence` already proves the
Stable+Installable route, so it is not duplicated. A second general step factors
out the actual semantic requirements: a current head Frame, RequestReady, and
packet.Holds in the *given full state model* suffice for the independent Instance
and parent Evidence. It needs neither Installable nor commitment of child edges,
choice compatibility, value support or an extension-model witness. A current
recorded packet discharges its branch predicate via Models. The uncovered bridge
is obtaining a current Frame/RequestReady packet for every stable selected node;
no such universal producer is asserted.

## General actual-journal readback

`GeneralNominalOrdinaryJournal194` recovers per-packet Instance from any ordinary
actual WF trace starting with an empty journal. The induction handles fresh
installation and every retained packet separately, then transports through each
ordinary extension. Consequently every syntactic recorded tree is sound at one
common final model. Finite coverage plus Child accessibility constructs a uniform
dictionary independently of the model. Coverage/accessibility are explicit open
structural requirements, and descriptor-changing refresh is not included. This
result does not require Build, final Installable, or the SelectionsPersist contract.

## Next structural step: recorded-child accessibility

Before implementation: each actual Packet's emitted child identity is strictly
above its parent identity (`packet_child_above`). For an arbitrary finite journal,
use max(recorded parent identities)+1 minus demand identity as a natural rank.
Every Child edge bounds its parent by that maximum and strictly increases identity,
so it strictly decreases this truncated rank even when the child is unrecorded.
This should prove unconditional accessibility for JournalTree.Child, removing Acc
from ordinary-journal readback without claiming coverage or general completion.

Structural result verified: `GeneralNominalJournalAccessibility194.accessible`
proves Acc unconditionally for every actual finite journal and root. The new
coverage-only `uniform_dictionary` removes the independent Acc assumption.
This does not establish coverage for stable states or semantic transport through
nonordinary descriptor refresh. The previous conditional modules remain unchanged.

## Selected payload alignment, design before implementation

Use a current head Survivor only for pending/linked/fresh structural fields. An
independent Instance in the same model supplies its declaration, finished head
inspection and private/projection truth. This constructs a Survivor for the
recorded key without treating Instance as Classify. Local Unique should identify
its key and full ordered children. Then recurse on the finite selected Classify
payload, propagating syntactic journal Reach through each recorded packet.
Coverage and actual ordinary execution remain explicit, but child Evidence and
packet/key agreement are derived rather than assumed.

Selected alignment verified in `GeneralNominalSelectedJournal194`: independent
same-model Instance plus a head Survivor produces its own head Survivor; actual
Local Unique identifies recorded key and ordered children. Mutual recursion on
the finite Classify payload derives Evidence for exactly the selected payload.
The final `selected_sound` needs only actual ordinary initial execution, final
syntactic journal coverage and selected Classify, then holds in every final model.
No child Evidence, key agreement, Stable, Build or Acc premise is added.
This is conditional actual-selection soundness, not universal coverage/completion.

## Final local node and coverage boundary

Before implementation: specialize the proven same-model selected Instance alignment
to one recorded root packet, composing supplied same-model child Evidence. Global
coverage is unnecessary for this local node rule. Separately test the already
stable concrete nonleaf finish: it records only the parent, whereas its generated
terminal child is semantically committed and reused. Proving missing child packet
and not-Covered would show exactly why Stable cannot supply this readback route's
coverage assumption; this is not a contradiction in the language.

Final local result verified: `GeneralNominalRecordedNode194.evidence_node` uses
only one recorded focus packet, actual ordinary history, current Local.selected
and same-model children Evidence. Concrete `stable_not_covered` proves the WF
finish is Stable yet not journal Covered: its actual reached child has no packet,
being semantically committed and reused. Thus removing Coverage by claiming
Stable implies it would be false. The general remaining route must account for
unrecorded committed nodes, not silently replace reuse with record-on-commit.
