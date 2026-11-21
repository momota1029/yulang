import Yulang.GeneralDeclarativeNFNode324
import Yulang.GeneralDeclarativeExampleSource320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHiddenDecl324
open GeneralDeclarations (Clause Declaration Equation Checked DeclarationChecked Registry)
open GeneralDeclarationPatterns (Pattern Constructors normalize normalizeArgs variablesArgs substArgs
  checkSmaller_exact ConservativeSmaller counted encodeArgs hide ArgsWellScoped WellScoped)
open GeneralDeclarationExamples (roles constructors containerChild itemBinder itemEquation)
open GeneralDeclarativeExampleSource320 (leaf leaf_checked)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeNFHead324 (fact)

def catalogue : Constructors :=
  fun n => if n = 9 then some ⟨[.type],9⟩ else constructors n

def interpretation : Interpretation :=
  ⟨fun n => if n = 4 then some .emptyRecord else none, fun _ => false, fun _ impossible => by cases impossible⟩

abbrev terminal : Pattern := .app 4 []
abbrev hidden : Pattern := .app 9 [.var 40]
abbrev raw : Pattern := .record 7 (.var 0) (.record 7 hidden terminal)
abbrev normal : Pattern := .record 7 (.var 0) terminal
abbrev empty : Expr := .primitive .emptyRecord []
abbrev normCode : Expr := .record 7 (.variable 0) empty
abbrev out : Equation := ⟨96,0,.var 1⟩
abbrev parent : Declaration := ⟨97,1,[raw],[containerChild],[out],[itemBinder]⟩
abbrev registry : Registry := ⟨catalogue,roles,[parent,leaf]⟩

theorem source_normal : normalize raw = normal := rfl

theorem hidden_not_in_scope : parent.inputNames = [0] ∧ 40 ∉ parent.inputNames :=
  ⟨rfl,by decide +kernel⟩

theorem declaration_checked : DeclarationChecked catalogue roles parent := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro eq member
      cases List.mem_singleton.mp member
      exact ⟨none,rfl⟩
    · intro n body declared
      change (if n = 0 then some none else none) = some body at declared
      split at declared
      · rename_i name
        exact .inl ⟨out,List.mem_cons_self,name.symm⟩
      · cases declared
    · intro clause member
      cases List.mem_singleton.mp member
      refine ⟨rfl,?_⟩
      intro eq used
      cases List.mem_singleton.mp used
      exact ⟨none,rfl⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,Pattern.variables,variablesArgs]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,
      Pattern.variables,variablesArgs,normalize]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,catalogue,constructors]
  · intro clause member
    cases List.mem_singleton.mp member
    exact ⟨rfl,rfl⟩
  · intro clause member
    cases List.mem_singleton.mp member
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    cases List.mem_singleton.mp member
    unfold ConservativeSmaller
    decide +kernel
  · intro clause member
    cases List.mem_singleton.mp member
    intro capture
    constructor
    · simp [substArgs,Pattern.subst,normalize,normalizeArgs,hide,counted,encodeArgs,Pattern.encode,
        Roles.argsSize,Roles.Term.size]
      omega
    · intro n
      simp [substArgs,Pattern.subst,normalize,normalizeArgs,hide,counted,encodeArgs,Pattern.encode,
        Roles.argsOccurrences,Roles.Term.occurrences]

theorem checked : Checked registry := by
  constructor
  · decide +kernel
  · intro decl present
    rcases List.mem_cons.mp present with rfl|last
    · exact declaration_checked
    · cases List.mem_singleton.mp last
      refine ⟨leaf_checked.signature,leaf_checked.identified,leaf_checked.produced,leaf_checked.outputOnly,
        leaf_checked.scope,?_,leaf_checked.countsCovered,leaf_checked.paterson,leaf_checked.conservative,leaf_checked.captureStable⟩
      simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]

theorem raw_does_not_compile : translate catalogue interpretation raw = none := rfl
theorem normal_compiles : translate catalogue interpretation (normalize raw) = some normCode := rfl

theorem raw_head_none (cap : Nat → Capture) (arg : Capture) :
    GeneralDeclarativeArgumentFacts320.headFact catalogue interpretation cap arg raw = none := rfl

end Yulang.GeneralDeclarativeHiddenDecl324
