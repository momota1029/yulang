import Yulang.GeneralVersionedEndpointObstruction315

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralLiveCompoundRegistry316
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDictionaryJournalRefinement228Source (constructors roles interpretation context root initial_source root_point ground labels)
open GeneralDictionaryCompoundSource238 (compiled_declaration)

abbrev otherChild : Clause := ⟨0,1,[.variant 0 (.var 0)],[]⟩
abbrev declaration : Declaration := { GeneralDictionaryCompoundSource238.declaration with requirements := [otherChild] }

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

abbrev leaf : Declaration := ⟨316,1,[.variant 0 (.var 0)],[],[⟨0,0,.app 3 []⟩],[]⟩
abbrev sourceRegistry : Registry := ⟨constructors,roles,[declaration,leaf]⟩
abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry

theorem compiled_registry : registry = sourceRegistry := rfl

theorem leaf_checked : DeclarationChecked constructors roles leaf := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  all_goals simp

theorem checked : Checked sourceRegistry :=
  ⟨by decide +kernel,by
    intro d member
    rcases List.mem_cons.mp member with eq | last
    · cases eq; exact declaration_checked
    · cases List.mem_singleton.mp last; exact leaf_checked⟩

theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry context.interpretation := by
  constructor
  · intro d member
    rcases List.mem_cons.mp member with eq | last
    · cases eq
      simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
        GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
        GeneralNominalCenteredHeadWFSource.ConstructorUse,interpretation,constructors,GeneralDictionaryOptionalExpression229.pattern]
      exact ⟨rfl,rfl,rfl⟩
    · cases List.mem_singleton.mp last
      simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
        GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
        GeneralNominalCenteredHeadWFSource.ConstructorUse,interpretation,constructors,GeneralCandidateInspection.Primitive.parameters]
  · exact GeneralDictionaryCompoundSource238.coverage.2

theorem source : GeneralNominalSourceFormation.InitialSource registry context root := initial_source registry rfl rfl

theorem boundary_checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked sourceRegistry :=
  ⟨rfl,checked⟩

noncomputable abbrev initialState := GeneralNominalVersionedJournal232.initial context root

theorem initial : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial
    sourceRegistry root initialState :=
  ⟨_,⟨context,labels,initial_source sourceRegistry rfl rfl,root_point,ground,coverage,rfl⟩,rfl⟩

end Yulang.GeneralLiveCompoundRegistry316
