import Yulang.GeneralDeclarativeRepeatProbe327

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeRepeatGraph327
open GeneralDeclarativeRepeatDecl327
open GeneralDeclarativeRepeatState327
open GeneralDeclarativeRepeatProbe327
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativePriority321 (Recurs)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def rank (n : Nat) : Nat :=
  if n = 11 then 2 else if n ≤ 2 ∨ n = 5 ∨ n = 6 ∨ (20 ≤ n ∧ n ≤ 22) then 1 else 0

theorem exact_rows : result.equations = presentRows ++
    [⟨12,.variable 3⟩,⟨13,.variable 7⟩,⟨14,.variable 4⟩,⟨15,.variable 9⟩,
     ⟨16,.variable 7⟩,⟨17,.variable 10⟩] ++
    [⟨20,.nominal 0 [.variable 13]⟩,⟨21,.nominal 0 [.variable 13]⟩,
     ⟨22,.nominal 0 [.variable 13]⟩,⟨6,.variable 5⟩,⟨5,.variable 21⟩] := rfl

theorem checked_intervals : result.normal.intervals =
    [(0,1),(1,2),(12,13),(13,14),(15,16),(16,17),(20,21),(21,22)] := rfl

theorem bounds_rank {a b : Nat} (line : Bound result.normal a b) :
    rank a = rank b := by
  induction line with
  | refl => rfl
  | trans _ _ first last => exact first.trans last
  | interval known =>
    rw [checked_intervals] at known
    simp only [List.mem_cons,List.not_mem_nil,or_false] at known
    rcases known with h|h|h|h|h|h|h|h <;> cases h <;> rfl
  | constraint known =>
    change _ ∈
      [PresenceNormalForm.Atom.tyLe (.var 13) (.var 13),.tyLe (.var 13) (.var 13),
       .tyLe (.var 16) (.var 13),.tyLe (.var 13) (.var 16),
       .tyLe (.var 18) (.union (.var 12) (.var 15)),.tyLe (.union (.var 12) (.var 15)) (.var 18),
       .tyLe (.var 19) (.inter (.var 14) (.var 17)),.tyLe (.inter (.var 14) (.var 17)) (.var 19),
       .tyLe (.var 18) (.var 13),.tyLe (.var 13) (.var 19)] at known
    simp only [List.mem_cons,List.not_mem_nil,or_false] at known
    rcases known with h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl

theorem equal_rank {a b : Nat} (equal : Alias result a b) : rank a = rank b := by
  have whenever {x y : Nat} (row : (⟨x,.variable y⟩ : Equation) ∈ result.equations) : rank x = rank y := by
    rw [exact_rows] at row
    simp only [presentRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at row
    rcases row with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl
  induction equal with
  | bounds x _ => exact bounds_rank x
  | forward row => exact whenever row
  | backward row => exact (whenever row).symm
  | trans _ _ x y => exact x.trans y

theorem no_cycle : ∀ n, ¬AliasCycle result (observed result) n := by
  apply graph_no_cycle rank (fun _ _ eq => equal_rank eq)
  rintro name shape child ⟨body,written,seen⟩ childOf
  rw [exact_rows] at written
  simp only [presentRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at written
  rcases written with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h
  all_goals first
    | cases seen
    | skip
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at childOf
  all_goals first
    | (rcases childOf with rfl|rfl; all_goals decide +kernel)
    | (subst child; decide +kernel)

theorem safe (done : Nat → Prop) (d) : ¬Recurs result reg interp (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,spot,_,cycle⟩)
  · exact no_cycle arg.lower cycle
  · exact no_cycle spot cycle

end Yulang.GeneralDeclarativeRepeatGraph327
