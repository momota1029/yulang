import Yulang.GeneralDictionaryVersionedInitialPacket233
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedInitialTransport233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229 (plan packet lo hi actual)
open GeneralDictionaryVersionedInitialModel233 (names)
open GeneralNominalVersionedPlans231
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCommonBridge (Assignment)
variable {model : Assignment}

theorem packet_holds
    (old : GeneralNominalCenteredHeadMatStepPackets.Holds plan model)
    (lower : (model (names 0)).1 = (model lo).1)
    (upper : (model (names 1)).1 = (model hi).1) : Holds plan model := by
  have merges := old.2.1.1.2.1
  have newMerges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalVersionedAllocation231.merges snapshot registry root.identity declaration packet.bindings) := by
    rw [GeneralDictionaryOptionalInstall229.bindings_exact] at merges ⊢
    have pair := ((PresenceNormalForm.all_append ..).mp merges).1
    change PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.equations lo (.union (.var 4) (.var 4)) ++
        GeneralNominalAllocation.equations hi (.inter (.var 2) (.var 2))) at pair
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact] at pair
    have next : PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.equations (names 0) (.union (.var 4) (.var 4)) ++
          GeneralNominalAllocation.equations (names 1) (.inter (.var 2) (.var 2))) := by
      rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
        GeneralNominalCaptureMerges.equations_exact]
      change CommonNominalFullCarrier.Equivalent (model (names 0)).1 _ ∧
        CommonNominalFullCarrier.Equivalent (model (names 1)).1 _
      rw [lower,upper]
      exact pair
    exact (PresenceNormalForm.all_append ..).mpr ⟨next,next⟩
  have inputs : ∀ name, name ∈ declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed packet name →
      GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture packet).inputs name)
        (model (GeneralNominalVersionedFrame231.binder plan name)).1 := by
    intro name needed
    have zero : name = 0 := by
      rcases needed with named | needed
      · simpa [Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
          GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
          GeneralDeclarationPatterns.Pattern.variables] using named
      · obtain ⟨clause,member,_⟩ := needed; cases member
    subst name
    have previous := old.2.1.2.2.2.1 0 needed
    rw [GeneralNominalVersionedFrame231.binder_eq]
    change GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs 0) _
    rw [GeneralDictionaryOptionalInstall229.bindings_exact]
    change CommonNominalFullCarrier.Subtype (model (names 0)).1 _ ∧
      CommonNominalFullCarrier.Subtype _ (model (names 1)).1
    simp only [lower,upper]
    change GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalAllocation.capture snapshot registry root.identity declaration.id packet.bindings).inputs 0) _ at previous
    rw [GeneralDictionaryOptionalInstall229.bindings_exact] at previous
    exact previous
  have head : SchemaHolds plan plan.headSchema model := by
    have previous := old.2.1.2.2.2.2.1
    refine ⟨previous.1,?_⟩
    intro entry member
    have mode := GeneralNominalHeadSchemaNames186.head_actual plan entry member
    simpa only [mode,ite_true,GeneralNominalVersionedFrame231.binder_eq] using previous.2 entry member
  have outputs : Outputs plan model := by
    unfold Outputs
    rw [GeneralDictionaryVersionedInitialPacket233.emitted_schema]
    intro equation member
    cases List.mem_singleton.mp member
    have output := old.2.2 ⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩ (by rw [GeneralDictionaryOptionalInstall229.emitted_schema]; exact List.mem_singleton_self _)
    change CommonNominalFullCarrier.Equivalent (model 4).1 GeneralDictionaryOptionalOutput229.value at output ⊢
    exact output
  refine ⟨old.1,⟨⟨old.2.1.1.1,newMerges,old.2.1.1.2.2⟩,
    old.2.1.2.1,old.2.1.2.2.1,inputs,head,?_,?_⟩,outputs⟩
  · intro equation member _; exact outputs equation member
  · intro clause member; cases member

end Yulang.GeneralDictionaryVersionedInitialTransport233
