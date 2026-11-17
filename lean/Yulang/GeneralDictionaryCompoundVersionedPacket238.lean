import Yulang.GeneralDictionaryCompoundVersionedModel238
set_option maxRecDepth 2048
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundVersionedPacket238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundPacket238 (plan packet actual)
open GeneralDictionaryCompoundVersionedModel238
open GeneralNominalVersionedPlans231
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries GeneralDeclarationPatterns
open CommonNominalFullCarrier

theorem ordinary : Ordinary packet extended :=
  ⟨old_packet.2.1.1.1,new_merges,old_packet.2.1.1.2.2⟩

theorem head_holds : SchemaHolds plan plan.headSchema extended := by
  have old := old_packet.2.1.2.2.2.2.1
  refine ⟨old.1,?_⟩
  intro entry member
  have mode := GeneralNominalHeadSchemaNames186.head_actual plan entry member
  simpa only [mode,ite_true,GeneralNominalVersionedFrame231.binder_eq] using old.2 entry member

theorem input_fits (name : Nat)
    (needed : name ∈ declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed packet name) :
    GeneralNominalCaptureMerges.Fits extended
      ((GeneralNominalVersionedFrame231.capture packet).inputs name)
      (extended (GeneralNominalVersionedFrame231.binder plan name)).1 := by
  have same : name = 0 := by
    rcases needed with named | needed
    · simpa [Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.Pattern.variables] using named
    · obtain ⟨clause,member,needed⟩ := needed
      cases List.mem_singleton.mp member
      simpa [variablesArgs,Pattern.variables,normalizeArgs,normalize] using needed
  subst name
  rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryCompoundPacket238.binder_exact]
  change GeneralNominalCaptureMerges.Fits extended
    ((GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs 0) (extended actual).1
  rw [GeneralDictionaryCompoundPacket238.bindings_exact]
  change Subtype (extended (names 0)).1 (extended actual).1 ∧
    Subtype (extended actual).1 (extended (names 1)).1
  rw [fresh_value 0,fresh_value 1,old_value actual (by simp [pool])]
  unfold baseModel
  rw [GeneralDictionaryCompoundModel238.old_value actual (by simp [GeneralDictionaryCompoundModel238.pool]),GeneralDictionaryCompoundPacket238.actual_value]
  exact ⟨GeneralDictionaryOptionalOutput229.below_width,subtype_refl _⟩


theorem emitted_capture_independent (first last : GeneralDeclarationDemands.Capture)
    (allocate : (clause : Clause) → GeneralDeclarationDemands.Allocation roles clause) :
    (GeneralCanonicalChildOrder.canonicalEmit root.identity declaration declaration_checked first allocate).flatMap
      GeneralNominalCenteredHeadMatSchemas.emissionRequests =
    (GeneralCanonicalChildOrder.canonicalEmit root.identity declaration declaration_checked last allocate).flatMap
      GeneralNominalCenteredHeadMatSchemas.emissionRequests := by
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  rfl

theorem emitted_schema : emittedSchema plan = GeneralNominalCenteredHeadMatPlans.emittedSchema plan := by
  unfold emittedSchema emittedRequests GeneralNominalCenteredHeadMatPlans.emittedSchema
    GeneralNominalCenteredHeadMatSchemas.requests
  exact congrArg (GeneralNominalCenteredHeadMatSchemas.generated registry.constructors context.interpretation)
    (congrArg (fun requests => GeneralNominalMaterialization.rootRequests declaration root ++ requests)
      (emitted_capture_independent _ _ _))

theorem variables_lower : variables plan extended .lower 0 = (extended (names 0)).1 := by
  unfold variables
  simp [show (0 ∉ declaration.outputNames) from by decide +kernel]
  congr 2
  decide +kernel

theorem variables_upper : variables plan extended .upper 0 = (extended (names 1)).1 := by
  unfold variables
  simp [show (0 ∉ declaration.outputNames) from by decide +kernel]
  congr 2
  decide +kernel

theorem variables_actual : variables plan extended .actual 0 = (extended actual).1 := by
  unfold variables
  simp [show (0 ∉ declaration.outputNames) from by decide +kernel]
  rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryCompoundPacket238.binder_exact]

theorem child_value (index : Fin 3) :
    (extended (GeneralDictionaryCompoundModel238.names index)).1 = GeneralDictionaryCompoundModel238.values index := by
  have member : GeneralDictionaryCompoundModel238.names index ∈ pool := by
    have h := index.isLt
    have cases3 : index = 0 ∨ index = 1 ∨ index = 2 := by
      have h' : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 := by omega
      rcases h' with h' | h' | h'
      · exact Or.inl (Fin.ext h')
      · exact Or.inr (Or.inl (Fin.ext h'))
      · exact Or.inr (Or.inr (Fin.ext h'))
    rcases cases3 with rfl | rfl | rfl <;> simp [pool]
  rw [old_value _ member]
  exact GeneralDictionaryCompoundModel238.fresh_value index

theorem outputs : Outputs plan extended := by
  unfold Outputs
  rw [emitted_schema,GeneralDictionaryCompoundTotal238.emitted_schema]
  intro equation member
  rcases List.mem_cons.mp member with rfl | member
  · change Equivalent (extended 4).1 GeneralDictionaryOptionalOutput229.value
    rw [old_value 4 (by simp [pool])]
    unfold baseModel
    rw [GeneralDictionaryCompoundModel238.old_value 4 (by simp [GeneralDictionaryCompoundModel238.pool])]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rcases List.mem_cons.mp member with rfl | member
    · simp only [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatExpressions.value,variables_lower]
      rw [child_value 0,fresh_value 0]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp member
      simp only [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatExpressions.value,variables_upper]
      rw [child_value 1,fresh_value 1]
      exact ⟨subtype_refl _,subtype_refl _⟩

theorem child_schema (signature : child.Signature roles) :
    childSchema plan child signature = GeneralNominalCenteredHeadMatPlans.childSchema plan child signature := childSchema_eq ..

theorem child_holds (signature : child.Signature roles) :
    (GeneralNominalVersionedFrame231.childSite plan child signature).Holds extended ∧
    (childSchema plan child signature).Holds (variables plan extended) extended := by
  constructor
  · intro index
    have same : index = 0 := Fin.ext (by have h := index.isLt; change index.val < 1 at h; exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h))
    subst index
    change Subtype (extended (GeneralDictionaryCompoundModel238.names 0)).1 (extended (GeneralDictionaryCompoundModel238.names 2)).1 ∧
      Subtype (extended (GeneralDictionaryCompoundModel238.names 2)).1 (extended (GeneralDictionaryCompoundModel238.names 1)).1
    rw [child_value 0,child_value 1,child_value 2]
    exact ⟨(common_variant_iff ..).mpr GeneralDictionaryOptionalOutput229.below_width,subtype_refl _⟩
  · rw [child_schema,GeneralDictionaryCompoundTotal238.child_schema]
    intro equation member
    cases List.mem_singleton.mp member
    simp only [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatExpressions.value,variables_actual]
    rw [child_value 2,old_value actual (by simp [pool])]
    unfold baseModel
    rw [GeneralDictionaryCompoundModel238.old_value actual (by simp [GeneralDictionaryCompoundModel238.pool]),GeneralDictionaryCompoundPacket238.actual_value]
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem packet_holds : Holds plan extended := by
  refine ⟨source_model,⟨ordinary,old_packet.2.1.2.1,old_packet.2.1.2.2.1,
    input_fits,head_holds,?_,?_⟩,outputs⟩
  · intro equation member _; exact outputs equation member
  · intro clause member signature
    cases List.mem_singleton.mp member
    exact child_holds signature

theorem head_model : HeadModels packet extended := head_models packet_holds

end Yulang.GeneralDictionaryCompoundVersionedPacket238
