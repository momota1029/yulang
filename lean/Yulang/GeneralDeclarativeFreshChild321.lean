import Yulang.GeneralDeclarativeFreshOperands321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFreshChild321
open GeneralDeclarativeFreshCalls321 (SourceCodes argCode arguments results demand codes seed length_argCode from_append)
open GeneralDeclarativeFreshOperands321 (fresh_arguments fresh_outputs)
open GeneralDeclarativeNewNames321 (numbered supply old_plus_extra)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeWhereProducer321 (Child)
open GeneralDeclarativeFresh321 (extend)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeSubstitution320 (logical)

theorem compile_child {s : State} {capture : Nat → Capture}
    (source : SourceCodes r interp clause args out) (first : Nat)
    (stored : numbered first (codes capture args out) ⊆ s.equations) :
    Child s r interp capture clause (demand clause.role first args out) := by
  have partition : numbered first (codes capture args out) =
      numbered first (args.flatMap (argCode capture)) ++
        numbered (first + 3 * args.length) (out.map fun pr => logical capture .actual pr.2) := by
    rw [codes,from_append,length_argCode]
  have lo : numbered first (args.flatMap (argCode capture)) ⊆ s.equations := by
    intro eq member
    exact stored (partition.symm ▸ List.mem_append_left _ member)
  have hi : numbered (first + 3 * args.length) (out.map fun pr => logical capture .actual pr.2) ⊆ s.equations := by
    intro eq member
    exact stored (partition.symm ▸ List.mem_append_right _ member)
  exact ⟨rfl,fresh_arguments source.arguments first lo,fresh_outputs source.outputs _ hi⟩

theorem child_extension {s : State} {capture : Nat → Capture} {extra : List Nat}
    (source : SourceCodes r interp clause args out) (m) (valid : Models s m) :
    let exps := codes capture args out
    let defs := supply s extra exps
    let s' := appendFacts s defs
    let child := demand clause.role (seed s extra exps) args out
    Models s' (extend m defs) ∧
    (∀ name ∈ stateNames s ++ extra, extend m defs name = m name) ∧
    Child s' r interp capture clause child := by
  dsimp only
  have together := old_plus_extra s extra (codes capture args out) m valid
  have generated := compile_child (s := appendFacts s (supply s extra (codes capture args out))) source
    (seed s extra (codes capture args out)) (fun _ there => List.mem_append_right _ there)
  exact ⟨together.1,together.2,generated⟩

end Yulang.GeneralDeclarativeFreshChild321
