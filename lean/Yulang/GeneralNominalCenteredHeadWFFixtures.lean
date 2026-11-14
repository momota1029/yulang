import Yulang.GeneralNominalCenteredHeadWFBoundary
import Yulang.GeneralNominalCenteredHeadStepMaterializationCounterexample
import Yulang.GeneralNominalCenteredCompletionAliasTrace

set_option backward.isDefEq.respectTransparency false

/-! Ordinary list, alias-class and positional-default sources meet the
constructor contract. The earlier uninterpreted-constructor source does not. -/
namespace Yulang.GeneralNominalCenteredHeadWFFixtures
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralNominalCenteredHeadWFSource GeneralNominalCenteredHeadWFBoundary
open GeneralDeclarationExamples (constructors)
open GeneralNominalExamples (interpretation)

theorem int_constructor : ConstructorUse constructors interpretation 2 0 :=
  ⟨⟨[],2⟩,rfl,rfl,Or.inl ⟨.scalar .int,rfl,rfl⟩⟩

theorem list_constructor : ConstructorUse constructors interpretation 0 1 :=
  ⟨⟨[.type],0⟩,rfl,rfl,Or.inr ⟨rfl,rfl⟩⟩

theorem display_coverage : Coverage GeneralNominalExamples.registry interpretation := by
  constructor
  · intro declaration member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp [DeclarationCovered,PatternsCovered,PatternCovered,int_constructor,list_constructor]
  · intro role name body found
    simp only [GeneralDeclarationExamples.roles,GeneralDeclarationExamples.outputRole,GeneralDeclarationExamples.binaryRole,
      GeneralDeclarationExamples.bareRole] at found
    split at found
    · by_cases named : name = 0 <;> simp [named] at found
    · split at found
      · by_cases named : name = 1 <;> simp [named] at found
      · split at found <;> cases found

theorem alias_coverage : Coverage GeneralNominalCenteredCompletionAliasSource.registry interpretation := by
  constructor
  · intro declaration member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      simp [DeclarationCovered,PatternsCovered,PatternCovered,int_constructor,list_constructor]
  · intro role name body found
    simp only [GeneralNominalCenteredCompletionAliasSource.roles,GeneralDeclarationExamples.outputRole,
      GeneralDeclarationExamples.bareRole] at found
    split at found
    · cases found
    · split at found
      · by_cases named : name = 0 <;> simp [named] at found
      · cases found

theorem defaults_coverage : Coverage GeneralNominalCenteredHeadStepDefaults.registry interpretation := by
  constructor
  · intro declaration member
    cases List.mem_singleton.mp member
    simp [DeclarationCovered,PatternsCovered,PatternCovered,int_constructor]
  · intro role name body found
    change (if name = 0 then some (some (Roles.Term.var 0)) else none) = some (some body) at found
    split at found
    · cases found; trivial
    · cases found

theorem display_initial : (boundary GeneralDeclarationExamples.roles).Initial GeneralNominalExamples.registry
    GeneralNominalExamples.displayRoot
    (GeneralNominalCenteredHeadStepEffects.initial (GeneralNominalExamples.context true) GeneralNominalExamples.displayRoot) := by
  refine ⟨⟨GeneralNominalExamples.context true,[.app 0 [.app 2 []]],
    GeneralDictionarySupportRecursiveExample.initial_source,(fun _ => rfl),?_,rfl⟩,display_coverage⟩
  exact GeneralNominalCenteredCompletionAliasTrace.ground

theorem alias_initial : (boundary GeneralNominalCenteredCompletionAliasSource.roles).Initial
    GeneralNominalCenteredCompletionAliasSource.registry GeneralNominalCenteredCompletionAliasSource.root
    (GeneralNominalCenteredHeadStepEffects.initial (GeneralNominalExamples.context true) GeneralNominalCenteredCompletionAliasSource.root) :=
  ⟨⟨GeneralNominalExamples.context true,[.app 0 [.app 2 []]],GeneralNominalCenteredCompletionAliasSource.source,
    (fun _ => rfl),GeneralNominalCenteredCompletionAliasTrace.ground,rfl⟩,alias_coverage⟩

theorem defaults_initial : (boundary GeneralNominalCenteredHeadStepDefaults.roles).Initial
    GeneralNominalCenteredHeadStepDefaults.registry GeneralNominalCenteredHeadStepDefaults.root
    GeneralNominalCenteredHeadStepDefaults.start :=
  ⟨GeneralNominalCenteredHeadStepDefaults.initial_source,defaults_coverage⟩

theorem old_uninterpreted_not_covered : ¬ Coverage
    GeneralNominalCenteredHeadStepMaterializationSource.registry interpretation := by
  intro covered
  have output := (covered.1 _ (List.mem_singleton_self _)).2.1 _ (List.mem_singleton_self _)
  have use := (output.2 _ (List.mem_singleton_self _)).1
  rcases constructor_interpreted use with ⟨primitive,found⟩ | found <;> cases found

theorem old_uninterpreted_not_initial : ¬ (boundary GeneralNominalCenteredHeadStepMaterializationSource.roles).Initial
    GeneralNominalCenteredHeadStepMaterializationSource.registry GeneralNominalCenteredHeadStepMaterializationSource.root
    GeneralNominalCenteredHeadStepMaterializationSource.start :=
  fun initial => old_uninterpreted_not_covered initial.2

end Yulang.GeneralNominalCenteredHeadWFFixtures
