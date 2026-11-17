import Yulang.GeneralDictionaryMixedGround218RootCommitted235
import Yulang.GeneralNominalVersionedMixedSelectedFrame235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218FinalEvidence235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (plan childSite)
open GeneralDictionaryGroundCopy218Reinstall (newChild)
open GeneralDictionaryGroundCopy218SaturatedParent (contextFor)
open GeneralDictionaryMixedGround218PointStable235 (Sites)
open GeneralNominalCenters GeneralSourceDictionaries GeneralNominalVersionedJournal232
variable {state : State roles}

theorem old_infeasible (sites : Sites state) (recorded : plan ∈ state.plans)
    (framed : GeneralNominalVersionedEvidence231.Frame registry state.core childSite.occurrence key candidate)
    (given : GeneralNominalCommonBridge.Assignment) (valid : Models state given)
    (shared : GeneralDictionaryHeadSharing220.Holds candidate given) : False := by
  have input := GeneralDictionaryMixedGround218PointStable235.frame_old_input sites framed
  have declaration := GeneralDictionaryGroundCopy218Obstruction.role_leaf framed.visible framed.role_eq
  have queries : GeneralNominalInspection.queries candidate.packet.context.state candidate.packet.context.interpretation
      candidate.packet.declaration = [.variables [0],.variables [0]] := by
    rw [declaration]
    exact GeneralDictionaryGroundCopy218Obstruction.leaf_queries _
  have one : (⟨0,.source (GeneralDictionaryTopLevelSharing217.firstCenter candidate.input),.actual⟩ : GeneralNominalMaterialization.Use) ∈ candidate.headSchema.variables := by
    simp [Plan.headSchema,queries,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
      GeneralNominalMaterialization.Schema.append,GeneralDictionaryTopLevelSharing217.firstCenter]
  have two : (⟨0,.source (GeneralDictionaryTopLevelSharing217.secondCenter candidate.input),.actual⟩ : GeneralNominalMaterialization.Use) ∈ candidate.headSchema.variables := by
    simp [Plan.headSchema,queries,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
      GeneralNominalMaterialization.Schema.append,GeneralDictionaryTopLevelSharing217.secondCenter]
  have same := (GeneralDictionaryHeadSharing220.holds_iff candidate given).mp shared _ one _ two rfl
  rw [input] at same
  exact GeneralDictionaryMixedGround218Obstruction234.centers_different given (valid.2.1 plan recorded) same

theorem old_not_selected
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root state)
    (sites : Sites state) (recorded : plan ∈ state.plans) (inhabited : ∃ model, Models state model) :
    ¬ GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry state childSite.occurrence (.selected key children) := by
  intro selected
  obtain ⟨candidate,framed,kids⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
  have chosen := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected
  have conflict : GeneralNominalVersionedDiagnostic232.SharingConflict registry state childSite.occurrence := by
    refine ⟨key,children,GeneralNominalVersionedMixedCurrentEvidence235.selected_unique chosen,
      GeneralNominalVersionedMixedCurrentCandidate235.selected_safe chosen,inhabited,⟨candidate,framed⟩,?_⟩
    rintro ⟨model,valid,other,frame,shared⟩
    exact old_infeasible sites recorded frame model valid shared
  exact B4TargetV8.conflict_not_selected conflict chosen

theorem evidenceAt
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root state)
    (sites : Sites state) (recorded : plan ∈ state.plans) (allocated reserved atoms)
    (current : state.core.erased.current.context = contextFor allocated reserved atoms) :
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry state root := by
  intro model valid demand key children dictionaries reached stable childrenStable selected evidence
  have generated : GeneralNominalSaturationState.Generated state.core.erased.current root demand := by
    rcases reached with rfl | generated
    · exact .root
    · exact generated
  have location := GeneralDictionaryMixedGround218PointStable235.generated_only sites generated
  rcases location with rfl | rfl | rfl
  · obtain ⟨candidate,framed,kids⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
    apply GeneralNominalVersionedEvidence231.evidence_node ?_ evidence
    refine ⟨candidate,framed,kids.symm,?_,?_⟩
    · exact GeneralDictionaryMixedGround218RootCommitted235.frame_holds sites allocated reserved atoms current framed model valid
    · intro output member; cases member
  · exact False.elim (old_not_selected path sites recorded ⟨model,valid⟩ selected)
  · have safe := GeneralNominalVersionedMixedCurrentCandidate235.selected_safe
      (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)
    exact False.elim (safe.1 (GeneralDictionaryMixedGround218PointStable235.new_pending allocated reserved atoms
      (congrArg GeneralNominalCandidates.Context.state current)))

theorem generated_children {child : Occurrence roles}
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root state)
    (sites : Sites state) (recorded : plan ∈ state.plans) (allocated reserved atoms)
    (current : state.core.erased.current.context = contextFor allocated reserved atoms)
    (inhabited : ∃ model, Models state model)
    (reached : demand = root ∨ GeneralNominalSaturationState.Generated state.core.erased.current root demand)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry state demand (.selected key children))
    (member : child ∈ children) : GeneralNominalSaturationState.Generated state.core.erased.current root child := by
  have generated : GeneralNominalSaturationState.Generated state.core.erased.current root demand := by
    rcases reached with rfl | generated
    · exact .root
    · exact generated
  rcases GeneralDictionaryMixedGround218PointStable235.generated_only sites generated with rfl | rfl | rfl
  · obtain ⟨candidate,framed,kids⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
    have committed := GeneralDictionaryMixedGround218RootCommitted235.frame_committed sites allocated reserved atoms current framed
    have edge := committed.2 child (kids.symm ▸ member)
    rw [framed.occurrence_eq] at edge
    exact .child .root edge
  · exact False.elim (old_not_selected path sites recorded inhabited selected)
  · have safe := GeneralNominalVersionedMixedCurrentCandidate235.selected_safe
      (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)
    exact False.elim (safe.1 (GeneralDictionaryMixedGround218PointStable235.new_pending allocated reserved atoms
      (congrArg GeneralNominalCandidates.Context.state current)))
end Yulang.GeneralDictionaryMixedGround218FinalEvidence235

