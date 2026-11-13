import Yulang.GeneralDictionarySemanticCollapseExample
import Yulang.GeneralDictionaryCaptureMultiplicity

/-! Non-vacuous private allocation for the reachable collapse witness. -/
namespace Yulang.GeneralDictionarySemanticCollapseAllocationExample
open CommonNominalFullCarrier GeneralNominalAllocation
open GeneralDictionarySemanticCollapseExample

theorem fresh_value (registry : GeneralDeclarations.Registry) (invocation : Nat)
 (key : GeneralNominalIdentities.Origin) :
 (model (GeneralNominalAllocation.source source registry invocation key)).1 = leafValue := by
 have h0 := source_initial_fresh source registry invocation key 0 (by decide +kernel)
 have h1 := source_initial_fresh source registry invocation key 1 (by decide +kernel)
 have h2 := source_initial_fresh source registry invocation key 2 (by decide +kernel)
 simp only [h0,h1,h2,or_self]
 rfl

theorem old_propagation (registry : GeneralDeclarations.Registry) (invocation : Nat)
 (declaration : GeneralDeclarations.Declaration) (names : declaration.inputNames = [7]) :
 GeneralNominalState.Models (propagate source registry invocation declaration [(7,3,3),(7,3,3)]) model := by
 apply (propagate_models ..).mpr
 refine ⟨source_models,?_,?_⟩
 · intro first hf last hl same
   simp at hf hl
   subst first; subst last
   exact subtype_refl _
 · simp only [merges,names,List.flatMap_cons,List.flatMap_nil,List.append_nil]
   simp only [occurrences,List.filter_cons,beq_self_eq_true,List.filter_nil,List.map_cons,List.map_nil,ite_true]
   rw [PresenceNormalForm.all_append]
   constructor
   · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
     simp only [capture,occurrences,List.filter_cons,beq_self_eq_true,List.filter_nil,List.map_cons,List.map_nil,ite_true]
     change Equivalent (model (GeneralNominalAllocation.source source registry invocation (origin invocation declaration.id 0 7 0))).1 (.union leafValue leafValue)
     rw [fresh_value]
     exact ⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
       (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩
   · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
     simp only [capture,occurrences,List.filter_cons,beq_self_eq_true,List.filter_nil,List.map_cons,List.map_nil,ite_true]
     change Equivalent (model (GeneralNominalAllocation.source source registry invocation (origin invocation declaration.id 1 7 0))).1 (.inter leafValue leafValue)
     rw [fresh_value]
     exact ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
       (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩

theorem current_propagation (registry : GeneralDeclarations.Registry) (invocation : Nat)
 (declaration : GeneralDeclarations.Declaration) (names : declaration.inputNames = [7]) :
 GeneralNominalState.Models (propagate revision.snapshot registry invocation declaration [(7,3,3)]) model :=
 GeneralDictionaryCaptureMultiplicity.collapse_propagation source revision.snapshot registry invocation
 declaration 7 (3,3) model names (old_propagation registry invocation declaration names) revised_models

theorem endpoints (registry : GeneralDeclarations.Registry) (invocation : Nat)
 (declaration : GeneralDeclarations.Declaration) (names : declaration.inputNames = [7]) :
 let captured := (capture source registry invocation declaration.id [(7,3,3),(7,3,3)]).inputs 7
 Equivalent (model captured.1).1 (model 3).1 ∧ Equivalent (model captured.2).1 (model 3).1 :=
 GeneralDictionaryCaptureMultiplicity.collapse_endpoints source revision.snapshot registry invocation
 declaration 7 (3,3) model names (old_propagation registry invocation declaration names) revised_models

theorem capture_ids_differ (registry : GeneralDeclarations.Registry) (invocation key : Nat) :
 (capture source registry invocation key [(7,3,3),(7,3,3)]).inputs 7 ≠
 (capture revision.snapshot registry invocation key [(7,3,3)]).inputs 7 := by
 have h := GeneralDictionaryCaptureMultiplicity.duplicate_sources_differ source registry invocation key 7 (3,3)
    (by decide +kernel)
 change (capture source registry invocation key [(7,3,3),(7,3,3)]).inputs 7 ≠ (3,3)
 exact h

end Yulang.GeneralDictionarySemanticCollapseAllocationExample
