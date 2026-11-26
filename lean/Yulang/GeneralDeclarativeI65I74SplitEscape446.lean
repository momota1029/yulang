import Yulang.GeneralDeclarativeI65I74ExactEscape410

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SplitEscape446
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeK2Graph321 (Shape Descends Path)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeGraphRows321 (shapeOf observed structural)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeWitnessRank350 (rank)
open List410

/-- Bound SCC grades and ordinary Alias-side information are different
objects. A flat alias preserves the SIDE, not necessarily its Bound grade. -/
structure SplitReady (s : GeneralDeclarativeHead320.State) (site : Nat) (w : ExactEscapeWire) : Prop where
  boundShape : ∀ a b, Bound s.normal a b → rank w.ranks a ≤ rank w.ranks b
  flatSide : ∀ e ∈ s.equations, ∀ n, e.right = .variable n → w.side e.left = w.side n
  rootZero : w.side site = 0
  edges : ∀ e ∈ s.equations, ∀ h : Shape, shapeOf e.right = some h →
    w.side e.left ≤ 1 → ∀ n ∈ h.children, w.side n = 1

theorem sameSide {s site w} (h : SplitReady s site w) {a b} (eq : GeneralDeclarativeLowerKnown321.Alias s a b) :
    w.side a = w.side b := by
  induction eq with
  | bounds lo hi =>
    exact congrArg (colour w.palette)
      (Nat.le_antisymm (h.boundShape _ _ lo) (h.boundShape _ _ hi))
  | forward present => exact h.flatSide _ present _ rfl
  | backward present => exact (h.flatSide _ present _ rfl).symm
  | trans _ _ ab bc => exact ab.trans bc

theorem actualEdges {s site w} (h : SplitReady s site w) {a b}
    (reached : w.side a ≤ 1) (edge : Descends (structural s) a b) : w.side b = 1 := by
  obtain ⟨head,⟨owner,alias,write,present,shape⟩,child⟩ := edge
  exact h.edges _ present _ shape (sameSide h alias ▸ reached) b child

theorem pathsFromOne {s site w} (h : SplitReady s site w) {a b}
    (path : Path (structural s) a b) (entered : w.side a = 1) : w.side b = 1 := by
  induction path with
  | refl => exact entered
  | next e _ rest => exact rest (actualEdges h (by simp [entered]) e)

theorem split_independent_certificate_excludes_exact_raw_K2446 {s site w}
    (h : SplitReady s site w) : ¬AliasCycle s (observed s) site := by
  rintro ⟨dest,last,edge,tail,back⟩
  have lastSide := pathsFromOne h tail (actualEdges h (by simp [h.rootZero]) edge)
  have root := (sameSide h back).symm.trans lastSide
  simp [h.rootZero] at root

open GeneralDeclarativeWitnessRank350 (atom)

def splitCheck446 (s : GeneralDeclarativeHead320.State) (site : Nat) (w : ExactEscapeWire) : Bool :=
  ((((s.normal.ordinary.all (atom (rank w.ranks)) &&
    s.normal.intervals.all (fun e => decide (rank w.ranks e.1 ≤ rank w.ranks e.2))) &&
    s.equations.all (aliasRow w.side)) &&
    decide (w.side site = 0)) &&
    s.equations.all (exactShapeEscape w.side))

theorem split_check_reflects_actual_rows446 {s site w} :
    splitCheck446 s site w = true ↔ SplitReady s site w := by
  unfold splitCheck446
  constructor
  · intro checked
    obtain ⟨left,edges⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨ranks,atRoot⟩ := Bool.and_eq_true_iff.mp left
    obtain ⟨grades,flat⟩ := Bool.and_eq_true_iff.mp ranks
    obtain ⟨atoms,intervals⟩ := Bool.and_eq_true_iff.mp grades
    refine ⟨?_,?_,of_decide_eq_true atRoot,?_⟩
    · intro a b bound
      induction bound with
      | interval present => exact of_decide_eq_true (List.all_eq_true.mp intervals _ present)
      | constraint present => exact of_decide_eq_true (List.all_eq_true.mp atoms _ present)
      | refl => exact Nat.le_refl _
      | trans _ _ ab bc => exact Nat.le_trans ab bc
    · intro e atRow n eq
      have good := List.all_eq_true.mp flat e atRow
      unfold aliasRow at good
      rw [eq] at good
      exact of_decide_eq_true good
    · intro e atRow head eq entered n inHead
      have ok := List.all_eq_true.mp edges e atRow
      simp only [exactShapeEscape,eq,ite_eq_left entered] at ok
      exact of_decide_eq_true (List.all_eq_true.mp ok n inHead)
  · intro h
    refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨?_,?_⟩,?_⟩,
        decide_eq_true h.rootZero⟩,?_⟩
    · apply List.all_eq_true.mpr
      intro a present
      cases a with
      | rowLe => rfl
      | tyLe lo hi =>
        cases lo <;> cases hi <;>
          first | rfl | exact decide_eq_true (h.boundShape _ _ (.constraint present))
    · apply List.all_eq_true.mpr
      rintro ⟨a,b⟩ present
      exact decide_eq_true (h.boundShape _ _ (.interval present))
    · apply List.all_eq_true.mpr
      intro e present
      unfold aliasRow
      split
      · rename_i n seen
        exact decide_eq_true (h.flatSide e present n seen)
      · rfl
    · apply List.all_eq_true.mpr
      intro e present
      unfold exactShapeEscape
      split
      · rfl
      · rename_i head decoded
        split
        · rename_i reached
          apply List.all_eq_true.mpr
          intro n used
          exact decide_eq_true (h.edges e present head decoded reached n used)
        · rfl

theorem checked_split_escape_excludes_exact_raw_K2446 {s site w}
    (ok : splitCheck446 s site w = true) : ¬AliasCycle s (observed s) site :=
  split_independent_certificate_excludes_exact_raw_K2446 (split_check_reflects_actual_rows446.mp ok)

end Yulang.GeneralDeclarativeI65.I72.SplitEscape446
