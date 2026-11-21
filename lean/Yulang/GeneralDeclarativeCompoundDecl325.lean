import Yulang.GeneralDeclarativeNamedAliasResolve325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundDecl325
open GeneralDeclarations (Clause Declaration Registry Checked DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped
  checkSmaller_exact ConservativeSmaller counted encodeArgs substArgs)
open GeneralDeclarationExamples (roles constructors containerChild itemBinder)
open GeneralDeclarativeExampleSource320 (leaf leaf_checked point)
open GeneralDeclarativeHiddenDecl324 (out)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeDemand320 (Demand)

def interpret : Interpretation :=
  ⟨fun _ => none,fun n => n == 0,fun _ _ => rfl⟩

abbrev inner : Pattern := .app 0 [.var 0]
abbrev outer : Pattern := .app 0 [inner]
abbrev clause : Clause := { containerChild with arguments := [inner] }
abbrev impl : Declaration := ⟨97,1,[outer],[clause],[out],[itemBinder]⟩
abbrev reg : Registry := ⟨constructors,roles,[impl,leaf]⟩
abbrev demand : Demand := ⟨1,[⟨0,1,2⟩],[⟨0,6⟩]⟩
abbrev call : Demand := ⟨2,[⟨8,9,10⟩],[⟨1,5⟩]⟩
abbrev innerCode : Expr := .nominal 0 [.variable 0]
abbrev outerCode : Expr := .nominal 0 [innerCode]

theorem inner_trans : translate constructors interpret (normalize inner) = some innerCode := rfl
theorem outer_trans : translate constructors interpret (normalize outer) = some outerCode := rfl

theorem impl_checked : DeclarationChecked constructors roles impl := by
  have old := GeneralDeclarativeHiddenDecl324.declaration_checked
  constructor
  · refine ⟨rfl,old.signature.2.1,old.signature.2.2.1,?_⟩
    intro demanded belongs
    cases List.mem_singleton.mp belongs
    have sig := old.signature.2.2.2 containerChild List.mem_cons_self
    exact ⟨rfl,sig.2⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,Pattern.variables,variablesArgs]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,
      Pattern.variables,variablesArgs,normalize]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro cited known
    cases List.mem_singleton.mp known
    exact ⟨rfl,rfl⟩
  · intro cited known
    cases List.mem_singleton.mp known
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro cited known
    cases List.mem_singleton.mp known
    unfold ConservativeSmaller
    decide +kernel
  · intro cited known cap
    cases List.mem_singleton.mp known
    constructor
    · simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
        Roles.argsSize,Roles.Term.size]
    · intro n
      simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
        Roles.argsOccurrences,Roles.Term.occurrences]

theorem checked : Checked reg := by
  constructor
  · decide +kernel
  · intro d found
    rcases List.mem_cons.mp found with rfl|rest
    · exact impl_checked
    · cases List.mem_singleton.mp rest
      exact leaf_checked

end Yulang.GeneralDeclarativeCompoundDecl325
