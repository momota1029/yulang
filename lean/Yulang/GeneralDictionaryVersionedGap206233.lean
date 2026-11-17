import Yulang.GeneralDictionaryDefaultGap206State
import Yulang.GeneralDictionaryDefaultGap206Counterexample
import Yulang.GeneralNominalVersionedSourceBoundary232
import Yulang.GeneralNominalVersionedConservative231
import Yulang.GeneralNominalVersionedFrameFunctional232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedGap206233
open GeneralDictionaryDefaultGap206Source
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev current := lift start

theorem initial : (GeneralNominalVersionedSourceBoundary232.boundary roles).Initial registry root current :=
  ⟨start,GeneralDictionaryDefaultGap206State.alloc_initial,rfl⟩

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) registry root current :=
  ⟨current,initial,.refl⟩

theorem current_model : Models current model := (lift_models start model).mpr inhabited

theorem ordinary (assignment : Assignment) : GeneralNominalVersionedPlans231.Ordinary packet assignment := by
  unfold GeneralNominalVersionedPlans231.Ordinary
  rw [bindings_empty]
  refine ⟨?_,?_,?_⟩
  · simp [GeneralNominalAllocation.Compatible]
  · simp [GeneralNominalVersionedAllocation231.merges,Declaration.inputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · change PresenceNormalForm.All CommonNominalFullCarrier.model assignment
      (GeneralNominalRecursiveInspection.selfChecks snapshot (GeneralNominalRecursiveCandidates.report context declaration [(1,1)]))
    rw [report_exact]
    simp [GeneralNominalRecursiveInspection.selfChecks,PresenceNormalForm.All]
    exact subtype_refl _

theorem head_models (assignment : Assignment) (valid : GeneralNominalState.Models snapshot assignment) :
    GeneralNominalVersionedPlans231.HeadModels packet assignment := by
  refine ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr ⟨valid,ordinary assignment⟩,?_⟩
  change GeneralNominalRecursiveInspection.ProjectionModels snapshot
    (GeneralNominalRecursiveCandidates.report context declaration [(1,1)]) assignment
  rw [report_exact]
  simp [GeneralNominalRecursiveInspection.ProjectionModels]

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snapshot registry root.identity packet.bindings := by
  rw [bindings_empty]
  intro key member
  simp [GeneralNominalVersionedAllocation231.keys,GeneralNominalVersionedAllocation231.declarationKeys,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at member

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry context root declaration := by
  refine ⟨source.metadata,⟨source.linked.1,by intro output member; cases member⟩,[(1,1)],rfl,?_,?_,model,head_models model source_model⟩
  · exact fresh
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry current.core root 37 plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,rfl,prepared⟩

theorem children_empty : GeneralNominalVersionedFrame231.children packet = [] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem emitted_empty : GeneralNominalVersionedPlans231.emittedSchema plan = ⟨[],false⟩ := by
  unfold GeneralNominalVersionedPlans231.emittedSchema GeneralNominalVersionedPlans231.emittedRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem packet_holds (assignment : Assignment) (valid : Models current assignment) :
    GeneralNominalVersionedPlans231.Holds plan assignment := by
  refine ⟨valid.1.1,⟨ordinary assignment,(head_models assignment valid.1.1).2,
    point_root_holds _ _ (fun _ => rfl) _,?_,?_,?_,?_⟩,?_⟩
  · intro name needed
    rcases needed with named | needed
    · simp [Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at named
    · obtain ⟨clause,member,_⟩ := needed; cases member
  · rw [GeneralDictionaryDefaultGap206Local.head_schema]
    constructor
    · intro test member
      cases List.mem_singleton.mp member
      refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      exact GeneralDictionaryDefaultGap206Source.scalar assignment valid.1.1
    · intro entry member; cases member
  · rw [emitted_empty]; intro equation member; cases member
  · intro clause member; cases member
  · unfold GeneralNominalVersionedPlans231.Outputs
    rw [emitted_empty]; intro equation member; cases member

end Yulang.GeneralDictionaryVersionedGap206233
