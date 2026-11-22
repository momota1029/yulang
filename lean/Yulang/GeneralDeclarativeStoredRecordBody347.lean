import Yulang.GeneralDeclarativeObservedBody347
import Yulang.GeneralDeclarativeStoredRecordRoute347
import Yulang.GeneralDeclarativeWitnessCutDecl334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoredRecordBody347
open GeneralDeclarativeStoredRecordRoute347 (cap blank support lowRows highRows loFields hiFields closeEnd openEnd protect lower upper)
open GeneralDeclarativeStoredRecordBase347 (raw raw_model)
open GeneralDeclarativeStoredAuthority347 (admits)
open GeneralDeclarativeObservedSupport347 (attach)
open GeneralDeclarativeWitnessCutDecl334 (impl registry pat checked covered)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeHead320 (Equation State)
open GeneralDeclarativeCompoundTree338 (World Tree TreeExact)
open GeneralDeclarativeCompoundSources338 (Source)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEndpointBody336 (Body)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (normalize)

abbrev anchors := attach support raw (admits raw) (lowRows++highRows)
abbrev current : World GeneralDeclarativeStoredRecordRoute347.done := ⟨_,anchors,[]⟩
abbrev root : Demand := ⟨1,[cap],[⟨0,8⟩]⟩
abbrev keep : List Nat := protect ++ [8]
def fallback (_ : Nat) : Capture := ⟨3,3,3⟩
def target (_ : GeneralDeclarations.Clause) (_ : Nat) : Nat := 8

theorem declared : Declared registry root := by
  intro out member
  cases List.mem_singleton.mp member
  exact ⟨none,rfl⟩

theorem bound : Bounds blank cap := by
  refine ⟨.interval ?_,.interval ?_⟩
  · change (0,1) ∈ [(0,1),(1,2)]
    exact List.mem_cons_self
  · change (1,2) ∈ [(0,1),(1,2)]
    exact List.mem_cons_of_mem _ List.mem_cons_self

theorem actual_tree :
    ∃ v spans, Tree keep current cap (normalize pat) v spans ∧
      TreeExact keep current (normalize pat) v spans := by
  have left : ∀ k ∈ ([7] : List Nat), ∃ a, (k,a) ∈ CommonRoleCanonicalRows.normalize loFields := by
    intro k used; cases List.mem_singleton.mp used; exact ⟨_,List.mem_cons_self⟩
  have right : ∀ k ∈ ([7] : List Nat), ∃ a, (k,a) ∈ CommonRoleCanonicalRows.normalize hiFields := by
    intro k used; cases List.mem_singleton.mp used; exact ⟨_,List.mem_cons_self⟩
  refine GeneralDeclarativeObservedCompound347.compile support cap (normalize pat) keep lower upper
    (fs := [(7,.var 0)]) (tail := .var 1) rfl (by decide) (by decide) left right bound ?_ .binder
  intro f listed a b _ _
  cases List.mem_singleton.mp listed
  exact .binder

/-- Physical authored record readers feed the existing checked
associated-body compiler. Both original capture occurrences survive
in order, the requested fixed target is 8, and this declaration makes
no child requests. No successful solver report is assumed. -/
theorem compiles_actual :
    ∃ (v : World GeneralDeclarativeStoredRecordRoute347.done) (spans : List (Nat × Capture)) (out : State),
      TreeExact keep current (normalize pat) v spans ∧ spans.map Prod.fst = [0,1] ∧
      compileBody registry interpretation root impl v.state spans keep fallback target = some (out,[]) ∧
      ∃ b : @Body registry interpretation root impl out [], b.rootRows.map Equation.left = [8] := by
  obtain ⟨v,uses,witness,exactTree⟩ := actual_tree
  obtain ⟨out,children,b,ran,targets,_,_,_⟩ :=
    GeneralDeclarativeObservedBody347.compile_one_arg (d := root) (impl := impl)
      rfl rfl witness checked covered List.mem_cons_self rfl declared fallback target
  have only : children = [] := b.ordered.symm
  subst children
  exact ⟨v,uses,out,exactTree,exactTree.2.1,ran,b,targets⟩

end Yulang.GeneralDeclarativeStoredRecordBody347
