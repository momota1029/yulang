import Yulang.GeneralDeclarativeI65I74RootEscape410

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.List410
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Graph321 (Descends Path)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeWitnessRank350 (rank atom)

/-- A nondecreasing ordinary alias rank is separate from the escape
side. It need not decrease on *any* structural edge. The palette
only identifies ranks; distinct ranks need not have distinct sides. -/
structure ExactEscapeWire where
  ranks : List Nat
  palette : List Nat

def ExactEscapeWire.side (w : ExactEscapeWire) (n : Nat) : Nat :=
  colour w.palette (rank w.ranks n)

def aliasRow (r : Nat → Nat) (e : Equation) : Bool :=
  match e.right with
  | .variable n => decide (r e.left = r n)
  | _ => true

def aliasRanks (s : State) (r : Nat → Nat) : Bool :=
  (s.normal.ordinary.all (atom r) &&
    s.normal.intervals.all (fun e => decide (r e.1 ≤ r e.2))) &&
  s.equations.all (aliasRow r)

theorem aliasRanks_eq_on_original_alias410 {s r} (checked : aliasRanks s r = true) :
    ∀ {a b}, Alias s a b → r a = r b := by
  obtain ⟨atomsAndIntervals,rows⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨atoms,intervals⟩ := Bool.and_eq_true_iff.mp atomsAndIntervals
  have bounded : ∀ a b, Bound s.normal a b → r a ≤ r b := by
    intro a b bound
    induction bound with
    | interval atRow => exact of_decide_eq_true (List.all_eq_true.mp intervals _ atRow)
    | constraint atRow => exact of_decide_eq_true (List.all_eq_true.mp atoms _ atRow)
    | refl n => exact Nat.le_refl _
    | trans _ _ a b => exact Nat.le_trans a b
  intro a b relation
  induction relation with
  | bounds lo hi => exact Nat.le_antisymm (bounded _ _ lo) (bounded _ _ hi)
  | forward eq => exact of_decide_eq_true (List.all_eq_true.mp rows _ eq)
  | backward eq => exact (of_decide_eq_true (List.all_eq_true.mp rows _ eq)).symm
  | trans _ _ l h => exact l.trans h

/-- Check only the original graph decoder's actual outgoing edges.
Unknown/nonstructural rows do not add graph edges, while aliases
and every raw decoded row (including unsupported ones) still count. -/
def exactShapeEscape (side : Nat → Nat) (e : Equation) : Bool :=
  match shapeOf e.right with
  | none => true
  | some head => if side e.left ≤ 1 then head.children.all (fun n => decide (side n = 1)) else true

def checkExactEscape (s : State) (site : Nat) (w : ExactEscapeWire) : Bool :=
  aliasRanks s (rank w.ranks) && decide (w.side site = 0) &&
    s.equations.all (exactShapeEscape w.side)

theorem exact_escape_preserves_alias_side410 {s site w}
    (ok : checkExactEscape s site w = true) {a b} (equivalent : Alias s a b) :
    w.side a = w.side b :=
  congrArg (colour w.palette)
    (aliasRanks_eq_on_original_alias410 ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).1) equivalent)

theorem exact_escape_tracks_original_edge410 {s site w}
    (ok : checkExactEscape s site w = true) {a b}
    (reached : w.side a ≤ 1) (edge : Descends (structural s) a b) :
    w.side b = 1 := by
  obtain ⟨head,observedAt,child⟩ := edge
  obtain ⟨author,alias,expr,original,decoded⟩ := observedAt
  have same := exact_escape_preserves_alias_side410 ok alias
  have atAuthor : w.side author ≤ 1 := same ▸ reached
  have row := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 _ original
  have checked : head.children.all (fun n => decide (w.side n = 1)) = true := by
    simpa [exactShapeEscape,decoded,atAuthor] using row
  exact of_decide_eq_true (List.all_eq_true.mp checked _ child)

private theorem exact_escape_follows_path410 {s site w}
    (ok : checkExactEscape s site w = true) {a b}
    (tail : Path (structural s) a b) (inside : w.side a = 1) : w.side b = 1 := by
  induction tail with
  | refl => exact inside
  | next edge _ next =>
    exact next (exact_escape_tracks_original_edge410 ok (by simp [inside]) edge)

theorem exact_escape_refutes_raw_root_K2410 {s site w}
    (ok : checkExactEscape s site w = true) : ¬ AliasCycle s (observed s) site := by
  have zero : w.side site = 0 :=
    of_decide_eq_true ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).2)
  rintro ⟨first,last,begin,follow,back⟩
  have inside := exact_escape_follows_path410 ok follow
    (exact_escape_tracks_original_edge410 ok (by simp [zero]) begin)
  have contradiction := (exact_escape_preserves_alias_side410 ok back).symm.trans inside
  simp [zero] at contradiction

end Yulang.GeneralDeclarativeI65.I72.List410
