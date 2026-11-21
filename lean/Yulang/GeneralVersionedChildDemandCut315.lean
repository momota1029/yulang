import Yulang.GeneralVersionedRecursiveCut314

set_option backward.isDefEq.respectTransparency false
/-! Only non-replay states with actual ordered child evidence in the
queried model need a new installation witness in the EvidenceNode proof.
No obligation is generated for a merely selected head with dead children. -/
namespace Yulang.GeneralVersionedChildDemandCut315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedEvidence231 (Evidence Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedRecursiveBridge310 (PendingCase CurrentCandidate ReplayFrame)
open GeneralVersionedRemainingWrites314 (ForeignChoice ReusedRows)
open GeneralVersionedEndpointReduction314 (Readback)
open GeneralNominalSaturationState (Generated)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalCommonBridge (Assignment)

def ChildDemand (r : Registry) (s : State roles) (m : Assignment)
    (children : List (Occurrence roles)) : Prop :=
  ∃ dictionaries, Models s m ∧ All₂ (Evidence (Compiled r) s.core m) children dictionaries

def ForeignKeys (roles : Roles.RoleDecls) : Prop :=
  ∀ r s (root focus : Occurrence roles) k kids e,
    PendingCase r s root focus k kids → CurrentCandidate r s focus k kids e →
    ∀ m, ChildDemand r s m kids → ForeignChoice s e.plan.packet

def EndpointReads (roles : Roles.RoleDecls) : Prop :=
  ∀ r s (root focus : Occurrence roles) k kids e,
    PendingCase r s root focus k kids → CurrentCandidate r s focus k kids e →
    ∀ m, ChildDemand r s m kids → Readback s e

theorem installable {s : State roles} {e : Effect roles} {model : Assignment}
    (aliases : ForeignKeys roles) (whereReads : EndpointReads roles)
    (pending : PendingCase r s root focus k kids)
    (candidate : CurrentCandidate r s focus k kids e)
    (childDemand : ChildDemand r s model kids) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled r) s e := by
  have a := aliases r s root focus k kids e pending candidate model childDemand
  have b := whereReads r s root focus k kids e pending candidate model childDemand
  obtain ⟨checked,path,_,_,selected,inhabited,_⟩ := pending
  have picked : Local r s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids) := by
    rw [candidate.2.2.1,candidate.2.2.2.1]
    exact selected
  exact GeneralVersionedEndpointReduction314.installable checked path picked candidate.1 candidate.2.1 inhabited a b

theorem node_and_edges {s : State roles} {root focus : Occurrence roles}
    (aliases : ForeignKeys roles) (whereReads : EndpointReads roles)
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (picked : Local registry s focus (.selected key kids))
    (stable : (boundary roles).Stable registry s focus)
    (reached : focus = root ∨ Generated s.core.erased.current root focus)
    (model : Assignment) (valid : Models s model)
    (ordered : All₂ (Evidence (Compiled registry) s.core model) kids dictionaries) :
    Evidence (Compiled registry) s.core model focus (.node key dictionaries) ∧
      ∀ child ∈ kids, Generated s.core.erased.current root child := by
  classical
  by_cases replay : ReplayFrame registry s focus key kids
  · obtain ⟨old,member,rs,ats,allocated,frame,order⟩ := replay
    obtain ⟨tree,edges⟩ := GeneralVersionedHistoryEvidence310.from_recorded_extension checked actual member
      rs ats allocated frame order valid ordered
    exact ⟨tree,edges reached⟩
  · obtain ⟨e,g,snapshot,o,k,c⟩ := GeneralNominalVersionedMixedSelectedEffect235.source_effect checked actual picked
    have enabled := installable aliases whereReads
      ⟨checked,actual,reached,stable,picked,⟨model,valid⟩,replay⟩
      (e := e) ⟨g,snapshot,o,k,c⟩ ⟨dictionaries,valid,ordered⟩
    have mixed := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp picked
    exact ⟨GeneralNominalVersionedMixedStableEvidence235.selected_node stable enabled o mixed valid ordered,
      fun _ h => GeneralNominalVersionedMixedStableEvidence235.selected_generated_children stable enabled o mixed reached h⟩

theorem evidenceNode {roles : Roles.RoleDecls} (aliases : ForeignKeys roles) (whereReads : EndpointReads roles) :
    B4SkeletonV8.EvidenceNode (boundary roles) := by
  intro r checked s root actual model valid focus key kids ds reached stable _ picked ordered
  exact (node_and_edges aliases whereReads checked actual picked stable reached model valid ordered).1

theorem old_foreign {roles : Roles.RoleDecls}
    (existsOnAll : GeneralVersionedRecursiveCut314.ForeignKeys roles) : ForeignKeys roles :=
  fun r s root focus k kids e pending candidate _ _ => existsOnAll r s root focus k kids e pending candidate

theorem old_endpoint {roles : Roles.RoleDecls}
    (existsOnAll : GeneralVersionedRecursiveCut314.EndpointReads roles) : EndpointReads roles :=
  fun r s root focus k kids e pending candidate _ _ => existsOnAll r s root focus k kids e pending candidate

end Yulang.GeneralVersionedChildDemandCut315
