import Yulang.GeneralMixedIndexedEvidence305
import Yulang.GeneralNominalVersionedInstallStep232

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedIndexedCommit305
open GeneralNominalCenteredHeadMatPlanData (Same occurrence)
open GeneralMixedIndexedPlanSemantics305 (classes_forward)
open GeneralDeferredLadderTransport302 (held_of_reindex children_eq)
open GeneralDeferredLadderOperationalView304 (View)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalReportContext305 (EquivalentContexts model_iff)
open GeneralNominalCenters (Plan)
variable {roles : Roles.RoleDecls} {a b : State roles} {p q : Plan roles}

theorem symm_same (same : Same p q) : Same q p :=
  ⟨same.registry.symm,same.declaration.symm,same.input.symm,same.seed.symm,same.constructors.symm,
    same.interpretation.symm,same.report.symm⟩

theorem committed_forward (raw : View a b) (same : Same p q)
    (contexts : EquivalentContexts p.packet.context q.packet.context)
    (old : Committed a p) : Committed b q := by
  constructor
  · intro m now
    obtain ⟨packet,classes⟩ := old.1 m ((raw.models m).mpr now)
    refine ⟨held_of_reindex same m packet ((model_iff contexts m).mp packet.1),?_⟩
    exact occurrence same ▸ classes_forward raw same m classes
  · intro child member
    have prior := old.2 child ((children_eq same).symm ▸ member)
    rw [raw.edges,occurrence same] at prior
    exact prior

end Yulang.GeneralMixedIndexedCommit305
