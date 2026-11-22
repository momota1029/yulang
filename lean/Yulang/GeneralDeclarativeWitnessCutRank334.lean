import Yulang.GeneralDeclarativeWitnessCutBody334
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralDeclarativeWitnessCutRank334
open GeneralDeclarativeWitnessCutDecl334
open GeneralDeclarativeWitnessCutBody334
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias alias_mono)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativePriority321 (Candidates Recurs)
open PresenceNormalForm (Atom)

def height (n : Nat) := if n < 3 then n+1 else 0

def edgeOK (edge : Nat × Nat) : Bool := decide (height edge.1 ≤ height edge.2)

def atomOK (a : Atom Nat) : Bool :=
  match a with
  | .tyLe (.var n) (.var m) => edgeOK (n,m)
  | _ => true

def rowOK (e : Equation) : Bool :=
  match e.right with
  | .variable n => decide (height e.left = height n)
  | _ => true

theorem intervals_preserve : final.normal.intervals.all edgeOK = true := by decide +kernel
theorem atoms_preserve : final.normal.ordinary.all atomOK = true := by decide +kernel
theorem rows_preserve : final.equations.all rowOK = true := by decide +kernel

theorem bounds_only_increase (proof : Bound final.normal a b) : height a ≤ height b := by
  induction proof with
  | interval read =>
    exact of_decide_eq_true (List.all_eq_true.mp intervals_preserve _ read)
  | constraint read =>
    exact of_decide_eq_true (List.all_eq_true.mp atoms_preserve _ read)
  | refl => exact Nat.le_refl _
  | trans _ _ h k => exact Nat.le_trans h k

theorem alias_same (witness : Alias final a b) : height a = height b := by
  induction witness with
  | bounds both reverse => exact Nat.le_antisymm (bounds_only_increase both) (bounds_only_increase reverse)
  | forward e => exact of_decide_eq_true (List.all_eq_true.mp rows_preserve _ e)
  | backward e => exact (of_decide_eq_true (List.all_eq_true.mp rows_preserve _ e)).symm
  | trans _ _ h k => exact h.trans k

theorem is_stored {e : Equation} (seen : e ∈ knownRows) : e ∈ final.equations := by
  rw [final_rows]
  exact List.mem_append_left _ seen

theorem at_center (witness : Alias (restriction support) 1 n) : n = 1 := by
  have same := alias_same (alias_mono (s := restriction support) (t := final) rfl
    (fun _ present => is_stored (exact_supported.mp present)) witness)
  change 2 = height n at same
  unfold height at same
  split at same <;> omega

theorem no_present_center {rhs} :
    (⟨1,rhs⟩ : Equation) ∉ (restriction support).equations := by
  intro here
  have visible := exact_supported.mp here
  change (⟨1,rhs⟩ : Equation) ∈ [lo,hi,scalar,tailRow] at visible
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with a|b|c|d <;> cases ‹_›

def decreases (e : Equation) : Bool :=
  match shapeOf e.right with
  | none => true
  | some tag => tag.children.all (fun c => decide (height c < height e.left))

theorem shape_descends : final.equations.all decreases = true := by decide +kernel

theorem no_cycles : ∀ root, ¬AliasCycle final (observed final) root := by
  apply graph_no_cycle height (fun _ _ => alias_same)
  rintro n tag child ⟨rhs,seen,code⟩ member
  have yes := List.all_eq_true.mp shape_descends ⟨n,rhs⟩ seen
  change decreases ⟨n,rhs⟩ = true at yes
  unfold decreases at yes
  rw [code] at yes
  exact of_decide_eq_true (List.all_eq_true.mp yes child member)

theorem safe (tests : Candidates) : ¬Recurs final registry interpretation tests root := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

end Yulang.GeneralDeclarativeWitnessCutRank334
