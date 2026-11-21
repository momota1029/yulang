import Yulang.GeneralVersionedEndpointWholeRhs315

set_option backward.isDefEq.respectTransparency false
/-! Final recursive cut: new numeric owners are already discharged.
For the remaining evidenced-child revisits, one shared head assignment
must equate the old/current whole endpoint RHSs. No separate class-output
certificate or raw equivalence of every operand is needed. -/
namespace Yulang.GeneralVersionedRevisitCut315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedRecursiveBridge310 (PendingCase CurrentCandidate)
open GeneralVersionedChildDemandCut315 (ChildDemand ForeignKeys)
open GeneralVersionedChildEndpointCut315 (EndpointModel)
open GeneralVersionedEndpointWholeRhs315 (AgreeRhs)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)
open GeneralVersionedHistoryEvidence310 (Compiled)

def RevisitRhs (roles : Roles.RoleDecls) : Prop :=
  ∀ r s (root focus : Occurrence roles) key kids e,
    PendingCase r s root focus key kids → CurrentCandidate r s focus key kids e →
    ∀ model, ChildDemand r s model kids →
    ∀ old ∈ s.plans, old.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity →
      ∃ m, Models s m ∧ HeadModels e.plan.packet m ∧ SchemaHolds e.plan e.plan.headSchema m ∧ AgreeRhs e.plan old m

theorem role_cut {roles : Roles.RoleDecls} : RevisitRhs roles ↔ EndpointModel roles := by
  constructor
  · intro transport r s root focus key kids e pending candidate m children
    have revisit := transport r s root focus key kids e pending candidate m children
    obtain ⟨checked,path,_,_,selected,inhabited,_⟩ := pending
    have picked : Local r s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids) := by
      rw [candidate.2.2.1,candidate.2.2.2.1]
      exact selected
    classical
    have operational : ∃ n, GeneralNominalVersionedMixedMaterialization237.Residual s e n := by
      by_cases q : ∃ prior ∈ s.plans, prior.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity
      · obtain ⟨old,history,same⟩ := q
        exact (GeneralVersionedEndpointWholeRhs315.joint_with_rhs checked path picked
          candidate.1 candidate.2.1 history same).mpr (revisit old history same)
      · exact GeneralVersionedNewOwnerInstall314.joint checked path
          (fun old seen same => q ⟨old,seen,same⟩) picked candidate.1 candidate.2.1 inhabited
    obtain ⟨n,residual⟩ := operational
    exact ⟨n,GeneralVersionedEndpointEquationCut315.ready_of_residual residual⟩
  · intro model r s root focus key kids e pending candidate m children old history same
    obtain ⟨n,ready⟩ := model r s root focus key kids e pending candidate m children
    obtain ⟨checked,path,_,_,selected,_,_⟩ := pending
    have picked : Local r s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids) := by
      rw [candidate.2.2.1,candidate.2.2.2.1]
      exact selected
    have frame : Frame (Compiled r) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
      candidate.1 ▸ candidate.2.1 ▸ e.frame
    exact ⟨n,ready.1,ready.2.1,ready.2.2.1,
      (GeneralVersionedEndpointWholeRhs315.endpoint_iff checked path picked frame history same ready.1).mp ready.2.2.2.2⟩

theorem evidenceNode {roles : Roles.RoleDecls} (aliases : ForeignKeys roles) (endpoint : RevisitRhs roles) :
    B4SkeletonV8.EvidenceNode (boundary roles) :=
  GeneralVersionedChildEndpointCut315.evidenceNode aliases (role_cut.mp endpoint)

end Yulang.GeneralVersionedRevisitCut315
