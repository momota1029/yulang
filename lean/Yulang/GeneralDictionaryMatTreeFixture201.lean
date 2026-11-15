import Yulang.GeneralDictionaryMatTreeHead201
import Yulang.GeneralDictionaryMatInputFixture201

namespace Yulang.GeneralDictionaryMatTreeFixture201
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredPointMergeExample (plan)
open GeneralNominalExamples (context state model state_models listDescriptor)

abbrev names : Fin 1 → Nat := fun _ => 0
abbrev bounds : Fin 1 → GeneralNominalInspection.Bounds (state true) := fun _ => (1,1)
abbrev tree : GeneralNominalTreeFacts.Tree (state true) names bounds 0 :=
  .leaf names bounds 0 listDescriptor rfl (by simp [List.ofFn_succ])

abbrev shape : GeneralDictionaryMatTreeHead201.HeadTree plan where
  arity := 1
  names := names
  distinct := fun _ _ _ => Subsingleton.elim _ _
  inputs := by simp [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.variablesArgs,
    GeneralDeclarationPatterns.Pattern.variables,List.ofFn_succ,names]
  bounds := bounds
  slot := 0
  tree := tree
  query := by
    simpa [GeneralNominalTreeFacts.Tree.query,tree,List.ofFn_succ,names] using GeneralDictionaryEarlyMergeExample.query
  located := rfl

theorem same_assignment_head (assignment : Assignment) (valid : GeneralNominalState.Models (state true) assignment) :
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds assignment :=
  GeneralDictionaryMatTreeHead201.head_models plan shape assignment valid

/-- The structural certificate and current model coexist with two real children. -/
theorem inhabited_tree :
    Nonempty (GeneralDictionaryMatTreeHead201.HeadTree plan) ∧
    plan.packet.children.length = 2 ∧
    GeneralNominalCenteredHeadMatStepJournal.Models GeneralDictionaryMatInputFixture201.start model ∧
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds model ∧
    GeneralNominalCenteredHeadMatStepPackets.Holds plan model :=
  ⟨⟨shape⟩,GeneralDictionaryMatInputFixture201.child_count,GeneralDictionaryMatInputFixture201.journal_models,
    same_assignment_head model (state_models true),GeneralDictionaryMatInputFixture201.total_holds model (state_models true)⟩

end Yulang.GeneralDictionaryMatTreeFixture201
