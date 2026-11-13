import Yulang.GeneralDictionaryCapturedSettlementBoundary

/-! A small semantic slice countermodel: source facts plus the terminal
producer output do not force the captured target/source alias. This slice is
not asserted Trusted; it deliberately omits both packets' input facts. -/
namespace Yulang.GeneralDictionaryCapturedAliasCountermodel
open GeneralNominalSupport GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedProducer
open GeneralDictionarySharedCapturedResumption
open GeneralDeclarationExamples (roles)

abbrev oldModel := GeneralDictionarySharedCapturedNovelty.model
noncomputable def model : GeneralNominalCommonBridge.Assignment := fun i =>
  if i = target then (.base .int,Common.rowEmpty) else oldModel i

theorem target_above : 2 < target := GeneralNominalIdentities.source_above_seed source.seed
    (GeneralNominalAllocation.origin root.identity
      GeneralDictionarySharedOutputBinderScope.capturedProposal.id 5 111 0)

theorem old_value (i : Nat) (bounded : i ≤ 2) : model i = oldModel i := by
  have different : i ≠ target := by have := target_above; omega
  simp [model,different]

theorem source_models : GeneralNominalState.Models source model := by
  apply (GeneralNominalOutputGrowthModels.source_models 1 model).mpr
  intro i bounded
  rw [old_value i (by omega),old_value (i+1) (by omega)]
  exact (GeneralNominalOutputGrowthModels.source_models 1 oldModel).mp
    GeneralDictionarySharedCapturedNovelty.source_models i bounded

theorem output_models : GeneralNominalPacketSupport.Outputs candidate model := by
  unfold GeneralNominalPacketSupport.Outputs
  rw [GeneralDictionarySharedCapturedProducer.schema_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source target⟩,?_⟩
    intro actual seen; cases seen
    change Equivalent (model target).1 (.base .int)
    simp only [model,ite_true]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ member; cases member
  · intro _ member; cases member
  · intro _ member; cases member

theorem slice_models (support : List (GeneralSourceDictionaries.Occurrence roles)) :
    GeneralNominalSharedSupport.Models observed [Fact.outputs candidate support] model := by
  refine ⟨source_models,?_⟩
  intro fact member
  cases List.mem_singleton.mp member
  exact output_models

theorem captured_not_int : ¬ Equivalent (model 2).1 (.base .int) := by
  intro same
  rw [old_value 2 (by omega)] at same
  change Equivalent (GeneralDictionarySharedCapturedNovelty.model 2).1 (.base .int) at same
  rw [GeneralDictionarySharedCapturedNovelty.model_old 2 (by omega)] at same
  have old : Common.Subtype (.base .str) (.base .int) :=
    (CommonNominalFullModelMap.subtype_exact _ _).mp same.1
  cases (CommonRigidHeadInspection.base_iff .str .int).mp old

theorem alias_not_entailed (support : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ (∀ m, GeneralNominalSharedSupport.Models observed [Fact.outputs candidate support] m →
      Equivalent (m target).1 (m 2).1) := by
  intro entails
  have same := entails model (slice_models support)
  apply captured_not_int
  have targetInt : Equivalent (model target).1 (.base .int) := by
    simp only [model,ite_true]; exact ⟨subtype_refl _,subtype_refl _⟩
  exact ⟨subtype_trans same.2 targetInt.1,subtype_trans targetInt.2 same.1⟩
/-- The genuinely Trusted empty slice also cannot explain the learned scalar.
This is only the source constructor, not a claim about all Trusted slices. -/
theorem source_slice_trusted : GeneralNominalSharedSupport.Trusted observed [] [] := .source

theorem source_scalar_not_entailed :
    ¬ (∀ m, GeneralNominalSharedSupport.Models observed [] m →
      Equivalent (m 2).1 (.base .int)) := by
  intro entails
  apply captured_not_int
  exact entails model ⟨source_models,by intro _ member; cases member⟩
end Yulang.GeneralDictionaryCapturedAliasCountermodel
