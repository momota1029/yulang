import Yulang.GeneralVersionedEndpointEquationCut315

set_option backward.isDefEq.respectTransparency false
/-! Exact existential endpoint interface with the real child premise.
Only the small residual table remains: the local rule already produces a
common model for the live journal, current head and current class outputs. -/
namespace Yulang.GeneralVersionedChildEndpointCut315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedEvidence231 (Evidence Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedRecursiveBridge310 (PendingCase CurrentCandidate ReplayFrame)
open GeneralVersionedRemainingWrites314 (ForeignChoice)
open GeneralVersionedChildDemandCut315 (ChildDemand ForeignKeys)
open GeneralVersionedEndpointEquationCut315 (ReadyModel)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)
open GeneralNominalVersionedJournalFrame236 (sources)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalCommonBridge (Assignment)

def BaseReady (s : State roles) (e : Effect roles) (m : Assignment) : Prop :=
  Models s m ∧ HeadModels e.plan.packet m ∧ SchemaHolds e.plan e.plan.headSchema m ∧ e.Live s.core m

theorem base_ready {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids))
    (rg : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m) : ∃ m, BaseReady s e m := by
  have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    rg ▸ snapshot ▸ e.frame
  obtain ⟨prior,priorValid⟩ := inhabited
  have head := GeneralVersionedHistoricalHead314.head checked actual selected frame ⟨prior,priorValid⟩
  obtain ⟨first,valid,headOK,classes⟩ :=
    GeneralVersionedSelectedJointHead312.effects_for_frame checked actual selected frame head
  have raw := (GeneralVersionedSelectedJointHead312.report_for_frame frame valid headOK).2
  have ledger := GeneralVersionedAggregateClassNow314.ledger checked actual selected frame valid
  have covered := GeneralNominalVersionedMixedSeedLedger237.covered
    (GeneralNominalVersionedMixedSeedLedger237.reachable actual) frame.context_eq ledger
  obtain ⟨models,headModel,schema,_,live⟩ := GeneralNominalVersionedSupportedCurrentHead237.selective_head
    (sources s) e.plan (GeneralNominalVersionedModelSupport237.current s)
    (GeneralNominalVersionedTraceSiteSupport237.current s) frame covered valid raw.1 raw.2.1 raw.2.2 headOK.2.2 classes
  exact ⟨_,models,headModel,schema,live⟩

def EndpointModel (roles : Roles.RoleDecls) : Prop :=
  ∀ r s (root focus : Occurrence roles) key kids e,
    PendingCase r s root focus key kids → CurrentCandidate r s focus key kids e →
    ∀ m, ChildDemand r s m kids → ∃ n, ReadyModel s e n

theorem from_operand_producer {roles : Roles.RoleDecls}
    (stronger : GeneralVersionedChildDemandCut315.EndpointReads roles) : EndpointModel roles := by
  intro r s root focus key kids e pending candidate m child
  have exactRead := stronger r s root focus key kids e pending candidate m child
  obtain ⟨checked,path,_,_,selected,inhabited,_⟩ := pending
  have picked : Local r s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids) := by
    rw [candidate.2.2.1,candidate.2.2.2.1]
    exact selected
  obtain ⟨model,residual⟩ := GeneralVersionedRemainingWrites314.joint checked path picked
    candidate.1 candidate.2.1 inhabited
    (GeneralVersionedEndpointReduction314.reused checked path picked
      (candidate.1 ▸ candidate.2.1 ▸ e.frame) exactRead)
  exact ⟨model,GeneralVersionedEndpointEquationCut315.ready_of_residual residual⟩

theorem installable {s : State roles} {e : Effect roles} {model : Assignment}
    (aliases : ForeignKeys roles) (endpointModel : EndpointModel roles)
    (pending : PendingCase r s root focus k kids) (candidate : CurrentCandidate r s focus k kids e)
    (children : ChildDemand r s model kids) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled r) s e := by
  have keys := aliases r s root focus k kids e pending candidate model children
  obtain ⟨other,ready⟩ := endpointModel r s root focus k kids e pending candidate model children
  obtain ⟨checked,path,_,_,selected,_,_⟩ := pending
  have picked : Local r s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids) := by
    rw [candidate.2.2.1,candidate.2.2.2.1]
    exact selected
  exact (GeneralNominalVersionedMixedMaterialization237.source_installable_iff checked path picked candidate.1 candidate.2.1).mpr
    ⟨(GeneralVersionedRemainingWrites314.choice checked path picked ready.1).mpr keys,
      GeneralVersionedEndpointEquationCut315.from_ready checked path picked candidate.1 candidate.2.1 ready⟩

theorem node_and_edges {s : State roles} {root focus : Occurrence roles}
    (aliases : ForeignKeys roles) (endpointModel : EndpointModel roles)
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
    have enabled := installable aliases endpointModel
      ⟨checked,actual,reached,stable,picked,⟨model,valid⟩,replay⟩
      (e := e) ⟨g,snapshot,o,k,c⟩ ⟨dictionaries,valid,ordered⟩
    have mixed := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp picked
    exact ⟨GeneralNominalVersionedMixedStableEvidence235.selected_node stable enabled o mixed valid ordered,
      fun _ h => GeneralNominalVersionedMixedStableEvidence235.selected_generated_children stable enabled o mixed reached h⟩

theorem evidenceNode {roles : Roles.RoleDecls} (aliases : ForeignKeys roles) (whereModel : EndpointModel roles) :
    B4SkeletonV8.EvidenceNode (boundary roles) := by
  intro r checked s root actual model valid focus key kids ds reached stable _ picked ordered
  exact (node_and_edges aliases whereModel checked actual picked stable reached model valid ordered).1

end Yulang.GeneralVersionedChildEndpointCut315
