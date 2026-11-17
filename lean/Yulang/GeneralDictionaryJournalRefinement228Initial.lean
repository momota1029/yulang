import Yulang.GeneralDictionaryJournalRefinement228Source
import Yulang.GeneralDictionaryHeadSharingBoundary220

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryJournalRefinement228Initial
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDictionaryJournalRefinement228Source

abbrev declaration : Declaration := ⟨228,0,[.app 0 [.var 0,.var 0]],[],[⟨0,0,.app 3 []⟩],[]⟩
abbrev sourceRegistry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry
abbrev start := GeneralNominalCenteredHeadMatStepJournal.initial context root

theorem compiled_declaration : GeneralNominalCenteredHeadAllocEncoding.declaration declaration = declaration := rfl
theorem compiled_registry : registry = sourceRegistry := rfl

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,Declared]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member

theorem checked : Checked sourceRegistry :=
  ⟨by simp,by intro d member; cases List.mem_singleton.mp member; exact declaration_checked⟩

theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry context.interpretation := by
  constructor
  · intro d member
    cases List.mem_singleton.mp member
    simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
      GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
      GeneralNominalCenteredHeadWFSource.ConstructorUse,interpretation,constructors]
    rfl
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

end Yulang.GeneralDictionaryJournalRefinement228Initial
