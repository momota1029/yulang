import Yulang.GeneralDeclarativeCovariantLate326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeLateProviderDecl326
open GeneralDeclarations (Checked Declaration DeclarationChecked Registry)
open GeneralDeclarationPatterns (ArgsWellScoped WellScoped Pattern normalize normalizeArgs variablesArgs)
open GeneralDeclarationExamples (constructors outputRole roles)
open GeneralDeclarativePairDecl326 (impl clause impl_checked)
open GeneralDeclarativeExampleSource320 (leaf leaf_checked point)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)

def extendedRoles : Roles.RoleDecls := fun n => if n = 3 then outputRole 1 else roles n

def interpretation : Interpretation :=
  ⟨fun n => if n = 2 then some (.scalar .int) else GeneralDeclarativePairDecl326.interpret.primitives n,
   fun _ => false,fun _ impossible => by cases impossible⟩

abbrev body : GeneralDeclarations.Equation := ⟨143,1,.app 2 []⟩
abbrev provider : Declaration := ⟨142,3,[.var 0],[],[body],[]⟩
abbrev call : Demand := ⟨3,[point 0],[⟨1,3⟩]⟩
abbrev reg : Registry := ⟨constructors,extendedRoles,[impl,leaf,provider]⟩
theorem normalized_body : translate constructors interpretation (normalize body.rhs) =
    some (.primitive (.scalar .int) []) := rfl

theorem provider_checked : DeclarationChecked constructors extendedRoles provider := by
  constructor
  · refine ⟨rfl,?_,?_,fun _ never => False.elim (List.not_mem_nil never)⟩
    · intro equation requested
      cases List.mem_singleton.mp requested
      exact ⟨none,rfl⟩
    · intro key rhs seen
      change (if key = 1 then some none else none) = some rhs at seen
      split at seen
      · rename_i keyKnown
        exact .inl ⟨body,List.mem_cons_self,keyKnown.symm⟩
      · cases seen
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro _ missing
    cases missing
  · intro _ missing
    cases missing
  · intro _ missing
    cases missing
  · intro _ missing
    cases missing

theorem root_checked : DeclarationChecked constructors extendedRoles impl := by
  refine ⟨?_,impl_checked.identified,impl_checked.produced,impl_checked.outputOnly,impl_checked.scope,
    impl_checked.constructorScoped,impl_checked.countsCovered,impl_checked.paterson,impl_checked.conservative,
    impl_checked.captureStable⟩
  refine ⟨impl_checked.signature.1,impl_checked.signature.2.1,impl_checked.signature.2.2.1,?_⟩
  intro requirement used
  cases List.mem_singleton.mp used
  exact impl_checked.signature.2.2.2 clause List.mem_cons_self

theorem child_checked : DeclarationChecked constructors extendedRoles leaf := by
  refine ⟨?_,leaf_checked.identified,leaf_checked.produced,leaf_checked.outputOnly,leaf_checked.scope,
    leaf_checked.constructorScoped,leaf_checked.countsCovered,leaf_checked.paterson,leaf_checked.conservative,
    leaf_checked.captureStable⟩
  exact ⟨leaf_checked.signature.1,leaf_checked.signature.2.1,leaf_checked.signature.2.2.1,
    fun _ missing => False.elim (List.not_mem_nil missing)⟩

theorem checked : Checked reg := by
  refine ⟨by decide +kernel,?_⟩
  intro d visible
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl|rfl|rfl
  · exact root_checked
  · exact child_checked
  · exact provider_checked

end Yulang.GeneralDeclarativeLateProviderDecl326
