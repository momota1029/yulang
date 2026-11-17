import Yulang.GeneralDictionaryVersionedBothModel233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedBothPacket233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229 (plan packet actual)
open GeneralDictionaryVersionedBothModel233
open GeneralNominalVersionedPlans231
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open CommonNominalFullCarrier

theorem ordinary : Ordinary packet extended :=
  ⟨old_packet.2.1.1.1,new_merges,old_packet.2.1.1.2.2⟩

theorem head_holds : SchemaHolds plan plan.headSchema extended := by
  have old := old_packet.2.1.2.2.2.2.1
  refine ⟨old.1,?_⟩
  intro entry member
  have mode := GeneralNominalHeadSchemaNames186.head_actual plan entry member
  simpa only [mode,ite_true,GeneralNominalVersionedFrame231.binder_eq] using old.2 entry member

theorem emitted_schema : emittedSchema plan =
    ⟨[⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩],false⟩ := by
  unfold emittedSchema emittedRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem outputs : Outputs plan extended := by
  unfold Outputs
  rw [emitted_schema]
  intro equation member
  cases List.mem_singleton.mp member
  change Equivalent (extended 4).1 GeneralDictionaryOptionalOutput229.value
  rw [old_value 4 (by simp [pool])]
  exact ⟨subtype_refl _,subtype_refl _⟩

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
    · obtain ⟨clause,member,_⟩ := needed; cases member
  subst name
  rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryOptionalInstall229.binder_exact]
  change GeneralNominalCaptureMerges.Fits extended
    ((GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs 0) (extended actual).1
  rw [GeneralDictionaryOptionalInstall229.bindings_exact]
  change Subtype (extended (names 0)).1 (extended actual).1 ∧
    Subtype (extended actual).1 (extended (names 1)).1
  rw [fresh_value 0,fresh_value 1,old_value actual (by simp [pool]),GeneralDictionaryOptionalInstall229.actual_value]
  exact ⟨GeneralDictionaryOptionalOutput229.below_width,subtype_refl _⟩

theorem packet_holds : Holds plan extended := by
  refine ⟨source_model,⟨ordinary,old_packet.2.1.2.1,old_packet.2.1.2.2.1,
    input_fits,head_holds,?_,?_⟩,outputs⟩
  · intro equation member _; exact outputs equation member
  · intro clause member; cases member

theorem head_model : HeadModels packet extended := head_models packet_holds

theorem source_preserved (name : Nat) (member : name ∈ [0,1,2,3,4]) :
    extended name = GeneralDictionaryOptionalInstall229.model name :=
  old_value name (List.mem_append_left [GeneralDictionaryOptionalInstall229.lo,
    GeneralDictionaryOptionalInstall229.hi,actual] member)

end Yulang.GeneralDictionaryVersionedBothPacket233
