# Cycle195: finite readback catalogue including unrecorded reuse

Status: proof design, existing WF/V6 semantics unchanged.

The previous concrete final state is stable but its terminal committed child is
not recorded in the actual packet journal. Total actual-journal coverage is
therefore too strong for readback. We do not change Step, Stable, or Evidence.

Use a finite *readback-only* catalogue consisting of the actual recorded packets
and a finite list of current plans. Each additional plan has a current Frame,
RequestReady and semantic Committed certificate. No Installable, transition,
recursive Evidence, or completed dictionary is supplied by that certificate.
The catalogue is not a reachable state and is never used as the final model.
All semantic conclusions use the unchanged original final state and its models.

For arbitrary roles, registry, ordinary trace from an empty journal, final state,
and finite reusable-plan list, prove every catalogue packet is an Instance in
every original final model. A syntactic coverage predicate over this finite
catalogue constructs a finite tree by the strict increase of packet child IDs.
Then prove actual Classify.selected payload soundness, not merely existence of
some dictionary. Prove the old concrete parent/child example satisfies this
new coverage using only its one unrecorded child plan, while actual coverage fails.

Remaining contracts: no claim every reachable stable state has a finite complete
catalogue; current Frame/readiness/commitment are not inferred from selection;
descriptor-changing refresh transport is not inferred from ordinary execution.
This is a soundness bridge improvement, not full general EvidenceNode closure.
