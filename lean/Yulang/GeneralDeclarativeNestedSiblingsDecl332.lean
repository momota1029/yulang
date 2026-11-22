import Yulang.GeneralDeclarativeNestedFrame332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedSiblingsDecl332
open GeneralDeclarations (Declaration Clause Checked Registry DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped
  checkSmaller_exact ConservativeSmaller counted encodeArgs substArgs)
open GeneralDeclarationExamples (roles constructors)
open GeneralDeclarativeNestedExample332 (pat interpretation)
open GeneralDeclarativeNestedDecl332 (body root checked_decl)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativePairDecl326 (clause produced)

abbrev equationTwo : GeneralDeclarations.Equation := ⟨23,1,.var 5⟩
abbrev clauseTwo : Clause := ⟨22,2,[.var 3],[equationTwo]⟩
abbrev producedTwo : GeneralDeclarations.OutputBinder := ⟨5,22,23⟩
abbrev impl : Declaration := ⟨97,1,[pat],[clause,clauseTwo],[body],[produced,producedTwo]⟩
abbrev registry : Registry := ⟨constructors,roles,[impl,leaf]⟩

theorem picked (cl : Clause) (used : cl ∈ impl.requirements) : cl = clause ∨ cl = clauseTwo := by
  simpa [impl] using used

theorem impl_checked : DeclarationChecked constructors roles impl := by
  constructor
  · refine ⟨checked_decl.signature.1,checked_decl.signature.2.1,checked_decl.signature.2.2.1,?_⟩
    intro cl chosen
    rcases picked cl chosen with rfl|rfl
    · exact checked_decl.signature.2.2.2 _ List.mem_cons_self
    · refine ⟨rfl,?_⟩
      intro eq having
      cases List.mem_singleton.mp having
      exact ⟨none,rfl⟩
  · simp [Declaration.Identified,Declaration.outputNames,clauseTwo]
  · intro binder allocated
    rcases List.mem_cons.mp allocated with rfl|tail
    · exact ⟨clause,List.mem_cons_self,rfl,_,List.mem_cons_self,rfl,rfl⟩
    · cases List.mem_singleton.mp tail
      exact ⟨clauseTwo,List.mem_cons_of_mem _ List.mem_cons_self,rfl,_,List.mem_cons_self,rfl,rfl⟩
  · simp [Declaration.OutputOnly,Declaration.outputNames,Pattern.variables,variablesArgs,clauseTwo]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,
      Pattern.variables,variablesArgs,normalize,GeneralDeclarationPatterns.hide,clauseTwo]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,clauseTwo]
  · intro cl h
    rcases picked cl h with rfl|rfl <;> exact ⟨rfl,rfl⟩
  · intro cl h
    rcases picked cl h with rfl|rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro cl h
    rcases picked cl h with rfl|rfl <;> (unfold ConservativeSmaller; decide +kernel)
  · intro cl h cap
    rcases picked cl h with rfl|rfl
    · exact checked_decl.captureStable _ List.mem_cons_self cap
    · constructor
      · simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
          Roles.argsSize,Roles.Term.size]
        omega
      · intro n
        simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
          Roles.argsOccurrences,Roles.Term.occurrences]
        omega

theorem checked : Checked registry := by
  constructor
  · decide +kernel
  · intro d visible
    rcases List.mem_cons.mp visible with rfl|other
    · exact impl_checked
    · exact GeneralDeclarativeNestedDecl332.checked.2 d (List.mem_cons_of_mem _ other)

end Yulang.GeneralDeclarativeNestedSiblingsDecl332
