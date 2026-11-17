import Yulang.GeneralDictionaryOptionalSource229
import Yulang.GeneralDictionaryHeadSharingBoundary220

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundSource238
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDictionaryJournalRefinement228Source

abbrev child : Clause := ⟨0,0,[.variant 0 (.var 0)],[]⟩
abbrev declaration : Declaration := ⟨238,0,[.app 0 [.var 0,.var 0]],[child],[⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩],[]⟩
abbrev sourceRegistry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry
abbrev start := GeneralNominalCenteredHeadMatStepJournal.initial context root

theorem compiled_declaration : GeneralNominalCenteredHeadAllocEncoding.declaration declaration = declaration := rfl
theorem compiled_registry : registry = sourceRegistry := rfl

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,GeneralDictionaryOptionalExpression229.pattern,
      variablesArgs,Pattern.variables,merge,hide,variantRow]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDictionaryOptionalExpression229.pattern]
  · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; cases List.mem_singleton.mp member
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; cases List.mem_singleton.mp member
    unfold ConservativeSmaller; decide +kernel
  · intro clause member capture; cases List.mem_singleton.mp member
    constructor
    · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
      exact Roles.Term.size_pos _
    · intro name
      simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

theorem checked : Checked sourceRegistry :=
  ⟨by simp,by intro d member; cases List.mem_singleton.mp member; exact declaration_checked⟩

theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry context.interpretation := by
  constructor
  · intro d member
    cases List.mem_singleton.mp member
    simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
      GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
      GeneralNominalCenteredHeadWFSource.ConstructorUse,interpretation,constructors,GeneralDictionaryOptionalExpression229.pattern]
    exact ⟨rfl,rfl,rfl⟩
  · intro role name body found
    change (if name = 0 then some none else none) = some (some body) at found
    split at found <;> cases found

theorem source : GeneralNominalSourceFormation.InitialSource registry context root := initial_source registry rfl rfl

theorem initial : (GeneralDictionaryHeadSharingBoundary220.boundary roles).Initial sourceRegistry root start :=
  ⟨context,labels,initial_source sourceRegistry rfl rfl,root_point,ground,coverage,rfl⟩

theorem reachable : B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles) sourceRegistry root start :=
  ⟨start,initial,.refl⟩

theorem boundary_checked : (GeneralDictionaryHeadSharingBoundary220.boundary roles).Checked sourceRegistry :=
  ⟨rfl,checked⟩

end Yulang.GeneralDictionaryCompoundSource238
