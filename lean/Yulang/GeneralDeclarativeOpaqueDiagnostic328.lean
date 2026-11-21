import Yulang.GeneralDeclarativeOpaqueGraph328
import Yulang.GeneralDeclarativeOpaqueIntervals328
import Yulang.GeneralDeclarativeRank321
import Yulang.GeneralDeclarativeRepeat320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueDiagnostic328
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (Entails literal)
open GeneralDeclarativeOpaqueIntervals328 (Ends ready left right low high preserved)
open GeneralDeclarativeCaptureClosure320 (atoms withOrdinary)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty nominal Equivalent subtype_refl observeTy)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev endpoints : Ends := ⟨3,4,8,8⟩
abbrev root : Capture := ⟨0,1,2⟩
abbrev rows : List Equation := [⟨0,low endpoints⟩,⟨2,high endpoints⟩,⟨3,.nominal 5 [.variable 4]⟩]
abbrev old : State := ⟨⟨[],[(0,1),(1,2),(4,3)]⟩,rows⟩
abbrev next := ready old 1 [] endpoints

abbrev block : CommonNominalSyntax.State Common.Row := .block [.nominal 5 [.inl (.inl 0)]] 0
abbrev looping : Ty := .nominal 5 [.inl block]

theorem unfold_loop (d : Nat) : observeTy d looping = observeTy d (nominal 5 [.inl looping]) := by
  cases d <;> rfl

theorem unfolds : Equivalent looping (nominal 5 [.inl looping]) := by
  constructor <;> intro d
  · rw [unfold_loop d]
    exact CommonNominalFullDemand.producerLe_refl _
  · rw [unfold_loop d]
    exact CommonNominalFullDemand.producerLe_refl _

abbrev plain : Ty := GeneralDeclarativeRepeat320.int
abbrev product := CommonNominalFullCarrier.pair looping plain
def model : Assignment := fun n => (if n ≤ 2 then product else if n = 3 ∨ n = 4 then looping else plain, Common.rowEmpty)

theorem inhabited : Models old model := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · simp
  · intro i present
    change _ ∈ [(0,1),(1,2),(4,3)] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with h|h|h <;> cases h <;> exact subtype_refl _
  · intro row occurs
    change row ∈ rows at occurs
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at occurs
    rcases occurs with h|h|h <;> cases h
    · exact eqv_refl _
    · exact eqv_refl _
    · exact unfolds

def rank (n : Nat) := if n ≤ 2 then 3 else if n = 3 then 2 else 1

theorem old_bound_rank (p : Bound old.normal a b) : rank a ≤ rank b := by
  induction p with
  | refl => exact Nat.le_refl _
  | constraint impossible => simp at impossible
  | interval present =>
    change _ ∈ [(0,1),(1,2),(4,3)] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with h|h|h <;> cases h <;> decide +kernel
  | trans _ _ a b => exact Nat.le_trans a b

theorem old_alias_rank (p : Alias old a b) : rank a = rank b := by
  have noVar {x y : Nat} : ¬(⟨x,.variable y⟩ : Equation) ∈ old.equations := by
    intro belongs
    change _ ∈ rows at belongs
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at belongs
    rcases belongs with same|same|same <;> cases same
  induction p with
  | bounds forward backward => exact Nat.le_antisymm (old_bound_rank forward) (old_bound_rank backward)
  | forward h => exact False.elim (noVar h)
  | backward h => exact False.elim (noVar h)
  | trans _ _ a b => exact a.trans b

theorem old_acyclic : ∀ n, ¬ AliasCycle old (observed old) n := by
  apply graph_no_cycle rank (fun _ _ h => old_alias_rank h)
  rintro n shape child ⟨code,there,read⟩ member
  change _ ∈ rows at there
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with x|x|x <;> cases x
  all_goals cases read
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at member
  all_goals first
    | (rcases member with rfl|rfl; all_goals decide +kernel)
    | (subst child; decide +kernel)

theorem added_forward : Bound next.normal 3 4 := by
  apply Bound.trans (b := (left old 1 [] endpoints).center)
  · exact .constraint List.mem_cons_self
  · exact .constraint (List.mem_cons_of_mem _ List.mem_cons_self)

theorem becomes_cycle : AliasCycle next (observed next) 3 := by
  refine ⟨4,4,⟨.nominal 5 [4],⟨3,alias_refl 3,.nominal 5 [.variable 4],?_,rfl⟩,List.mem_cons_self⟩,
    .refl 4,.bounds ?_ added_forward⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact .interval (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem conservative (m) : Models old m ↔ ∃ out, Models next out ∧
    ∀ n ∈ GeneralDeclarativeOpaqueNames328.kept old 1 (GeneralDeclarativeOpaqueIntervals328.protect [] endpoints),
      out n = m n := by
  have bounds : Bounds old root := ⟨.interval List.mem_cons_self,
    .interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  exact preserved bounds (literal List.mem_cons_self) (literal (List.mem_cons_of_mem _ List.mem_cons_self)) [] m

/-- Ordinary model-conservative pair projection need not preserve the raw
diagnostic graph once inferred component intervals are written.  This is
not acceptance or rejection of a stable source demand. -/
theorem separates : (∃ m, Models old m) ∧ (∃ m, Models next m) ∧
    (∀ n, ¬AliasCycle old (observed old) n) ∧ AliasCycle next (observed next) 3 := by
  obtain ⟨out,fit,_⟩ := (conservative model).mp inhabited
  exact ⟨⟨model,inhabited⟩,⟨out,fit⟩,old_acyclic,becomes_cycle⟩

end Yulang.GeneralDeclarativeOpaqueDiagnostic328
