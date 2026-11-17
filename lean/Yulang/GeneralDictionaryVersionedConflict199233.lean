import Yulang.GeneralDictionaryMatPriorConflict199
import Yulang.GeneralDictionaryMatPriorConflictLocal199
import Yulang.GeneralNominalVersionedSourceBoundary232
import Yulang.GeneralNominalVersionedConservative231
import Yulang.GeneralNominalVersionedFrameFunctional232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedConflict199233
open GeneralDictionaryMatPriorConflictSource199
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev current := lift start

theorem initial : (GeneralNominalVersionedSourceBoundary232.boundary roles).Initial registry root current :=
  ⟨start,GeneralDictionaryMatPriorConflictSource199.initial_source,rfl⟩

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


theorem head_equations (assignment : Assignment) (valid : GeneralNominalState.Models snapshot assignment) :
    GeneralNominalVersionedDiagnostic232.HeadEquations plan assignment := by
  refine ⟨point_root_holds _ _ (fun _ => rfl) _,?_,?_⟩
  · intro name member
    simp [Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at member
  · rw [GeneralDictionaryMatPriorConflictLocal199.head_schema]
    constructor
    · intro test member
      cases List.mem_singleton.mp member
      refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      exact GeneralNominalCenteredTerminalForkSource.scalar assignment valid 1 (by decide +kernel)
    · intro entry member; cases member

theorem emitted_schema : GeneralNominalVersionedPlans231.emittedSchema plan =
    ⟨[⟨2,.actual,.nominal 0 [.primitive (.scalar .int) []]⟩],false⟩ := by
  unfold GeneralNominalVersionedPlans231.emittedSchema GeneralNominalVersionedPlans231.emittedRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem no_packet (assignment : Assignment) : ¬ GeneralNominalVersionedPlans231.Holds plan assignment := by
  intro held
  have out := held.2.2
  unfold GeneralNominalVersionedPlans231.Outputs at out
  rw [emitted_schema] at out
  have equation := out _ (List.mem_singleton_self _)
  have scalar := GeneralNominalCenteredTerminalForkSource.scalar assignment held.1 2 (by decide +kernel)
  exact GeneralNominalPeelingOrigins.base_not_nominal .int 0 _ (subtype_trans scalar.2 equation.1)

end Yulang.GeneralDictionaryVersionedConflict199233
