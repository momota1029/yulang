import Yulang.GeneralDeclarativeFresh321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNewNames321
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeFresh321 (Fresh extend old_name preserves_and_extends)
open GeneralDeclarativeEntailment320 (appendFacts Holds)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def after : List Nat → Nat
  | [] => 0
  | n :: ns => max (n+1) (after ns)

theorem before_after {n : Nat} {ns : List Nat} (used : n ∈ ns) : n < after ns := by
  induction ns with
  | nil => cases used
  | cons one tail ih =>
    rcases List.mem_cons.mp used with rfl|later
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih later) (Nat.le_max_right _ _)

def numbered (first : Nat) : List Expr → List Equation
  | [] => []
  | exp::more => ⟨first,exp⟩ :: numbered (first+1) more

theorem rhs_exact (seed : Nat) (exps : List Expr) :
    (numbered seed exps).map Equation.right = exps := by
  induction exps generalizing seed with
  | nil => rfl
  | cons first tail ih => simp [numbered,ih]

theorem numbered_lower {first : Nat} {exps : List Expr} {row : Equation}
    (known : row ∈ numbered first exps) : first ≤ row.left := by
  induction exps generalizing first with
  | nil => cases known
  | cons e more ih =>
    rcases List.mem_cons.mp known with rfl|later
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ _) (ih later)

theorem no_target_collision {exps : List Expr} {first : Nat}
    {row other : Equation} (one : row ∈ numbered first exps) (two : other ∈ numbered first exps)
    (same : row.left = other.left) : row.right = other.right := by
  induction exps generalizing first with
  | nil => cases one
  | cons e more ih =>
    rcases List.mem_cons.mp one with rfl|later
    · rcases List.mem_cons.mp two with rfl|otherLater
      · rfl
      · have no := numbered_lower otherLater
        change first = other.left at same
        omega
    · rcases List.mem_cons.mp two with rfl|otherLater
      · have no := numbered_lower later
        change row.left = first at same
        omega
      · exact ih later otherLater

def supply (s : State) (extra : List Nat) (exps : List Expr) : List Equation :=
  numbered (after ((stateNames s ++ extra) ++ exps.flatMap names)) exps

theorem supply_avoids {s : State} {extra : List Nat} {exps : List Expr} {row : Equation}
    (used : row ∈ supply s extra exps) {name : Nat}
    (kept : name ∈ (stateNames s ++ extra) ++ exps.flatMap names) : row.left ≠ name := by
  have afterNames := numbered_lower used
  have below := before_after kept
  intro collides
  unfold supply at used
  change after ((stateNames s ++ extra) ++ exps.flatMap names) ≤ row.left at afterNames
  omega

theorem fresh_supply (s : State) (extra : List Nat) (exps : List Expr) :
    Fresh s (supply s extra exps) := by
  refine ⟨?_,fun _ one _ two same => no_target_collision one two same,?_⟩
  · intro row there repeats
    exact supply_avoids there (List.mem_append_left _ (List.mem_append_left _ repeats)) rfl
  · intro row there other thereToo used
    have oldRhs : row.right ∈ exps := by
      rw [← rhs_exact (after ((stateNames s ++ extra) ++ exps.flatMap names)) exps]
      exact List.mem_map.mpr ⟨row,there,rfl⟩
    exact supply_avoids thereToo (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨row.right,oldRhs,used⟩)) rfl

theorem old_plus_extra (s : State) (extra : List Nat) (exps : List Expr) (m)
    (valid : Models s m) :
    Models (appendFacts s (supply s extra exps)) (extend m (supply s extra exps)) ∧
    ∀ name ∈ stateNames s ++ extra, extend m (supply s extra exps) name = m name :=
  ⟨(preserves_and_extends (fresh_supply s extra exps) m valid).1,
    fun _ h => old_name (fun _ present => supply_avoids present (List.mem_append_left _ h))⟩

end Yulang.GeneralDeclarativeNewNames321
