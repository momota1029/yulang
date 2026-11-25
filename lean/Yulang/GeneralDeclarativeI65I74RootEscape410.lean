import Yulang.GeneralDeclarativeWitnessRank350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.List410
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Graph321 (Descends Path)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeTraceNames321 (names)

/-- 0 is the root side, 1 the forward-closed region after the first step,
and all other labels are ignored as structural owners. Use the original
unfiltered constraints and equations, not a witness-selected subgraph. -/
def colour (wire : List Nat) (name : Nat) : Nat := wire[name]?.getD 2

def checkRow (c : Nat → Nat) (row : Equation) : Bool :=
  match row.right with
  | .variable b => decide (c row.left = c b)
  | rhs =>
    if c row.left ≤ 1 then (names rhs).all (fun n => decide (c n = 1))
    else true

def checkEscape (s : State) (site : Nat) (wire : List Nat) : Bool :=
  let c := colour wire
  (decide (c site = 0) &&
    s.normal.ordinary.all (GeneralDeclarativeWitnessRank350.atom c) &&
    s.normal.intervals.all (fun e => decide (c e.1 ≤ c e.2))) &&
    s.equations.all (checkRow c)

structure EscapeRows (s : State) (c : Nat → Nat) : Prop where
  bound : ∀ {a b}, Bound s.normal a b → c a ≤ c b
  aliasFlat : ∀ {a b}, (⟨a,.variable b⟩ : Equation) ∈ s.equations → c a = c b
  rawStep : ∀ row ∈ s.equations, ∀ n ∈ names row.right, c row.left ≤ 1 →
    (∀ b, row.right ≠ .variable b) → c n = 1

theorem escape_rows_checked410 {s : State} {site : Nat} {wire : List Nat}
    (yes : checkEscape s site wire = true) :
    colour wire site = 0 ∧ EscapeRows s (colour wire) := by
  obtain ⟨head,rows⟩ := Bool.and_eq_true_iff.mp yes
  obtain ⟨colAndAtoms,intervals⟩ := Bool.and_eq_true_iff.mp head
  obtain ⟨first,atoms⟩ := Bool.and_eq_true_iff.mp colAndAtoms
  refine ⟨of_decide_eq_true first,⟨?_,?_,?_⟩⟩
  · intro a b bound
    induction bound with
    | interval used => exact of_decide_eq_true (List.all_eq_true.mp intervals _ used)
    | constraint used => exact of_decide_eq_true (List.all_eq_true.mp atoms _ used)
    | refl n => exact Nat.le_refl _
    | trans _ _ a b => exact Nat.le_trans a b
  · intro a b row
    exact of_decide_eq_true (List.all_eq_true.mp rows _ row)
  · intro row belongs n occurs nearby notVariable
    have verified := List.all_eq_true.mp rows row belongs
    cases h : row.right with
    | «variable» b => exact False.elim (notVariable b h)
    | primitive | nominal | record | variant | join =>
      simp only [checkRow,h,nearby, ↓reduceIte] at verified
      rw [h] at occurs
      exact of_decide_eq_true (List.all_eq_true.mp verified _ occurs)

theorem EscapeRows.sameAlias {s c} (rows : EscapeRows s c) {x y}
    (a : Alias s x y) : c x = c y := by
  induction a with
  | bounds lo hi => exact Nat.le_antisymm (rows.bound lo) (rows.bound hi)
  | forward eq => exact rows.aliasFlat eq
  | backward eq => exact (rows.aliasFlat eq).symm
  | trans _ _ l r => exact l.trans r

theorem EscapeRows.escapes {s c} (rows : EscapeRows s c) {a b}
    (nearby : c a ≤ 1) (raw : Descends (structural s) a b) : c b = 1 := by
  obtain ⟨head,owner,child⟩ := raw
  obtain ⟨origin,alias,expr,eq,decoded⟩ := owner
  refine rows.rawStep ⟨origin,expr⟩ eq b
    (GeneralDeclarativeGraphFootprint326.shape_children decoded child)
    ((rows.sameAlias alias) ▸ nearby) ?_
  intro n plain
  change expr = .variable n at plain
  subst expr
  cases decoded

theorem EscapeRows.follows {s c} (rows : EscapeRows s c) {a b}
    (tail : Path (structural s) a b) (arrived : c a = 1) : c b = 1 := by
  induction tail with
  | refl => exact arrived
  | next first _ later => exact later (rows.escapes (by simp [arrived]) first)

theorem checked_escape_refutes_exact_raw_root_K2410 {s site wire} (yes : checkEscape s site wire = true) :
    ¬AliasCycle s (observed s) site := by
  obtain ⟨root,rows⟩ := escape_rows_checked410 yes
  rintro ⟨first,last,begin,follow,returns⟩
  have escaped := rows.follows follow (rows.escapes (by simp [root]) begin)
  have impossible := (rows.sameAlias returns).symm.trans escaped
  simp [root] at impossible

end Yulang.GeneralDeclarativeI65.I72.List410
