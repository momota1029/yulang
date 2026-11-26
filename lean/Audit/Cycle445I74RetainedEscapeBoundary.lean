import Yulang.GeneralDeclarativeI65I74ExactEscape410

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedFull445.InputEscapeBoundary
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf literal_head)
open GeneralDeclarativeK2Graph321 (Descends Path Shape)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeWitnessRank350 (rank)
open List410

def flat : Equation := ⟨1,.variable 2⟩
def structuralRow : Equation := ⟨0,.nominal 9 [.variable 1]⟩

/-- Directed bounds 2→0→1, a literal flat alias 1~2 and one
structural edge 0→1 in precisely the original decoder. -/
def raw : State := ⟨⟨[],[(2,0),(0,1)]⟩,[flat,structuralRow]⟩

def tier (n : Nat) : Nat := if n = 2 then 0 else if n = 0 then 1 else if n = 1 then 2 else 3

theorem tier_zero_iff (n : Nat) : tier n = 1 ↔ n = 0 := by
  unfold tier
  split
  · rename_i neq
    subst n
    decide
  · split
    · rename_i zero; simp [zero]
    · split <;> simp_all

theorem bound_nondecreasing_tier {a b} (h : Bound raw.normal a b) : tier a ≤ tier b := by
  induction h with
  | interval present =>
    change (_,_) ∈ [(2,0),(0,1)] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with zero | one
    · cases zero; decide
    · cases one; decide
  | constraint present => cases present
  | refl => exact Nat.le_refl _
  | trans _ _ ab bc => exact Nat.le_trans ab bc

theorem alias_preserves_zero {a b} (alias : Alias raw a b) : (a = 0 ↔ b = 0) := by
  induction alias with
  | bounds lo hi =>
    have rankEq := Nat.le_antisymm (bound_nondecreasing_tier lo) (bound_nondecreasing_tier hi)
    rw [← tier_zero_iff _, ← tier_zero_iff _,rankEq]
  | forward present =>
    change _ ∈ [flat,structuralRow] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with f | s
    · cases f; decide
    · cases s
  | backward present =>
    change _ ∈ [flat,structuralRow] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with f | s
    · cases f; decide
    · cases s
  | trans _ _ ab bc => exact ab.trans bc

theorem actual_edges_only_zero_one {a b} (e : Descends (structural raw) a b) : a = 0 ∧ b = 1 := by
  obtain ⟨head,⟨owner,alias,exp,row,decoded⟩,child⟩ := e
  change _ ∈ [flat,structuralRow] at row
  simp only [List.mem_cons,List.not_mem_nil,or_false] at row
  rcases row with f | s
  · cases f; cases decoded
  · cases s
    have headExact : Shape.nominal 9 [1] = head := Option.some.inj decoded
    subst head
    exact ⟨(alias_preserves_zero alias).mpr rfl,List.mem_singleton.mp child⟩

theorem actual_edge_zero_one : Descends (structural raw) 0 1 :=
  ⟨.nominal 9 [1],literal_head (show structuralRow ∈ raw.equations from List.mem_cons_of_mem _ List.mem_cons_self) rfl,
    List.mem_cons_self⟩

theorem root_is_raw_safe445 : ¬AliasCycle raw (observed raw) 0 := by
  rintro ⟨first,last,edge,path,back⟩
  have firstOne := (actual_edges_only_zero_one edge).2
  subst first
  cases path with
  | refl => exact (by decide : (1 : Nat) ≠ 0) ((alias_preserves_zero back).mpr rfl)
  | next head _ => exact (by decide : (1 : Nat) ≠ 0) (actual_edges_only_zero_one head).1

theorem raw_safe_does_not_imply_C410_escape_wire445 :
    ∀ w : ExactEscapeWire, checkExactEscape raw 0 w = false := by
  intro w
  cases got : checkExactEscape raw 0 w with
  | false => rfl
  | true =>
    have head := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp got).1)
    have stepped : (raw.normal.intervals.all
        (fun p => decide (rank w.ranks p.1 ≤ rank w.ranks p.2))) = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp head.1).1).2
    have lo : rank w.ranks 2 ≤ rank w.ranks 0 := of_decide_eq_true
      (List.all_eq_true.mp stepped (2,0) (by decide))
    have hi : rank w.ranks 0 ≤ rank w.ranks 1 := of_decide_eq_true
      (List.all_eq_true.mp stepped (0,1) (by decide))
    have same : rank w.ranks 1 = rank w.ranks 2 :=
      aliasRanks_eq_on_original_alias410 head.1 (.forward (show flat ∈ raw.equations from List.mem_cons_self))
    have rankEq : rank w.ranks 0 = rank w.ranks 1 := Nat.le_antisymm hi (same ▸ lo)
    have col : w.side 0 = w.side 1 := congrArg (colour w.palette) rankEq
    have zero : w.side 0 = 0 := of_decide_eq_true head.2
    have one : w.side 1 = 1 := exact_escape_tracks_original_edge410 got
      (by simp [zero]) actual_edge_zero_one
    exact ((by decide : (0 : Nat) ≠ 1) (zero.symm.trans (col.trans one))).elim

end Yulang.GeneralDeclarativeI65.I72.RetainedFull445.InputEscapeBoundary

open Yulang.GeneralDeclarativeI65.I72.RetainedFull445.InputEscapeBoundary
#print axioms root_is_raw_safe445
#print axioms raw_safe_does_not_imply_C410_escape_wire445
