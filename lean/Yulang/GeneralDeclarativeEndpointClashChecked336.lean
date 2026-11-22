import Yulang.GeneralDeclarativeEndpointClash336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointClashChecked336
open GeneralDeclarativeEndpointClash336
open GeneralDeclarations (Declaration Checked DeclarationChecked)
open GeneralDeclarationExamples (constructors roles)
open GeneralDeclarationPatterns (normalize normalizeArgs variablesArgs Pattern ArgsWellScoped WellScoped hide)
open GeneralDeclarativeEndpointProgram336 (template)
open GeneralDeclarativeWitnessCutDecl334 (body)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeNestedExample332 (interpretation)

theorem check : DeclarationChecked constructors roles impl := by
  constructor
  · exact GeneralDeclarativeWitnessCutDecl334.check_decl.signature
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,
    Pattern.variables,variablesArgs,normalize,template,hide]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,template]
  all_goals intro _ impossible; cases impossible

theorem checked : Checked registry := by
  constructor
  · decide +kernel
  · intro d here
    cases List.mem_singleton.mp here
    exact check

theorem covered : Coverage registry interpretation := by
  constructor
  · intro d here
    cases List.mem_singleton.mp here
    exact ⟨⟨⟨trivial,trivial⟩,trivial⟩,fun _ no => False.elim (List.not_mem_nil no),
      fun _ included => by cases List.mem_singleton.mp included; trivial⟩
  · exact GeneralDeclarativeWitnessCutDecl334.covered.2

/-- One checked declaration is genuinely elected from supported
ends, but the stable actual-center equality has no model. -/
theorem regression :
    Checked registry ∧ Coverage registry interpretation ∧
    (∃ m, GeneralDeclarativeEndpointOverlay336.ModelsWith named sidecar m) ∧
    GeneralDeclarativeEndpointSelected336.Rule current sidecar registry interpretation wait root .rejected :=
  ⟨checked,covered,before_model,rejected⟩

end Yulang.GeneralDeclarativeEndpointClashChecked336
