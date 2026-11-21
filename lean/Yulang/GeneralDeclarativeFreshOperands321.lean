import Yulang.GeneralDeclarativeFreshCalls321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFreshOperands321
open GeneralDeclarativeFreshCalls321 (argCode arguments results length_argCode from_append)
open GeneralDeclarativeNewNames321 (numbered)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhereProducer321 (Operand ChildName)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open CommonRoleOutermostResolver (All₂)

theorem fresh_arguments {s : State} {capture} {patterns : List Pattern} {codes : List Expr}
    (translated : All₂ (fun pattern code => translate catalogue interp (normalize pattern) = some code) patterns codes)
    (seed : Nat) (stored : numbered seed (codes.flatMap (argCode capture)) ⊆ s.equations) :
    All₂ (Operand s catalogue interp capture) (arguments seed codes) patterns := by
  induction translated generalizing seed with
  | nil => exact .nil
  | @cons p x ps xs compiled rest ih =>
    apply All₂.cons
    · refine ⟨x,compiled,.fact (.whole ?_),.fact (.whole ?_),.fact (.whole ?_)⟩
      · exact stored List.mem_cons_self
      · exact stored (List.mem_cons_of_mem _ List.mem_cons_self)
      · have member : (⟨seed+2, logical capture .upper x⟩ : Equation) ∈
            numbered seed ((x :: xs).flatMap (argCode capture)) :=
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        exact stored member
    · have tail : numbered (seed+3) (xs.flatMap (argCode capture)) ⊆ s.equations := by
        intro eq h
        exact stored (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
      exact ih (seed+3) tail

theorem fresh_outputs {s : State} {capture} {source : List GeneralDeclarations.Equation}
    {wanted : List (Nat × Expr)}
    (translated : All₂ (fun eqn pr => pr.1 = eqn.name ∧ translate catalogue interp eqn.rhs = some pr.2) source wanted)
    (seed : Nat) (stored : numbered seed (wanted.map fun pr => logical capture .actual pr.2) ⊆ s.equations) :
    All₂ (ChildName s catalogue interp capture) source (results seed wanted) := by
  induction translated generalizing seed with
  | nil => exact .nil
  | @cons src row rest rows body other ih =>
    rcases row with ⟨name,rhs⟩
    exact .cons ⟨body.1,rhs,body.2,.fact (.whole (stored List.mem_cons_self))⟩
      (ih (seed+1) (fun _ h => stored (List.mem_cons_of_mem _ h)))

end Yulang.GeneralDeclarativeFreshOperands321
