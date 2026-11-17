import Yulang.GeneralDictionaryVersionLoopFrame237
import Yulang.GeneralNominalVersionedTerminal232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionLoopFull237
open GeneralDictionaryVersionLoopSource237 GeneralDictionaryVersionLoopPacket237
open GeneralDictionaryVersionLoopFrame237
open GeneralNominalCenters GeneralDeclarations CommonNominalFullCarrier
theorem head_schema : plan.headSchema =
    { tests := [(.source 3,.nominal 5 2)]
      variables := [⟨0,origin0,.actual⟩,⟨0,origin1,.actual⟩] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,List.ofFn_succ,plan,rootSite,origin0,origin1]

theorem binder_exact : plan.binder 0 = actual := by decide +kernel

theorem head_holds : GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema model := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source 3⟩,?_⟩
    intro value seen
    cases seen
    exact ⟨[.inl F,.inl F],rfl,subtype_refl _,subtype_refl _⟩
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    all_goals first | cases List.mem_singleton.mp member | skip
    all_goals
      simp only [ite_true]
      refine ⟨?_,⟨_,.source _⟩,?_⟩
      · first | exact ⟨_,seen0⟩ | exact ⟨_,seen1⟩
      · intro x y seenX seenY
        cases seenY
        rw [GeneralNominalVersionedFrame231.binder_eq,binder_exact,actual_value]
        first | exact observed_value 0 (by decide) seenX | exact observed_value 1 (by decide) seenX


theorem emitted_empty : GeneralNominalVersionedPlans231.emittedSchema plan = ⟨[],false⟩ := by
 unfold GeneralNominalVersionedPlans231.emittedSchema GeneralNominalVersionedPlans231.emittedRequests
 simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
   GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
 rfl

theorem packet_holds : GeneralNominalVersionedPlans231.Holds plan model := by
 have head : GeneralNominalVersionedPlans231.HeadModels packet model := head_model
 have ordinary := ((GeneralNominalVersionedPlans231.private_models_iff packet model).mp head.1).2
 refine ⟨source_model,⟨ordinary,head.2,?_,?_,head_holds,?_,?_⟩,?_⟩
 · intro index; exact ⟨subtype_refl _,subtype_refl _⟩
 · intro name needed
   have same : name=0 := by
     rcases needed with named | ⟨clause,member,_⟩
     · simpa [Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
         GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
         GeneralDeclarationPatterns.Pattern.variables] using named
     · cases member
   subst name
   rw [GeneralNominalVersionedFrame231.binder_eq,binder_exact,actual_value]
   change GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs 0) F
   rw [bindings_exact]
   change Subtype (model lo).1 F ∧ Subtype F (model hi).1
   rw [lower_value,upper_value]
   exact ⟨subtype_refl _,subtype_refl _⟩
 · intro equation member _; rw [emitted_empty] at member; cases member
 · intro clause member; cases member
 · intro equation member; rw [emitted_empty] at member; cases member

theorem classes (assignment) : GeneralNominalVersionedEffects231.ClassEffects initial.core root plan assignment := by
 apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
 constructor <;> intro output member <;> simp [requests_empty] at member

theorem installation_models : GeneralNominalVersionedInstall232.InstallationModels initial effect model := by
 refine ⟨initial_model,packet_holds,⟨head_model,classes _⟩,?_,?_,?_⟩
 · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
     (fun _ => GeneralNominalVersionedTerminal232.requests_iff children_empty)).mpr (classes _)
 · intro prior member; cases member
 · intro prior member; cases member

theorem installed_model : GeneralNominalVersionedJournal232.Models installed model :=
 (GeneralNominalVersionedInstall232.install_models rfl).mpr installation_models
end Yulang.GeneralDictionaryVersionLoopFull237
