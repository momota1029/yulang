import Yulang.GeneralDeclarativeEqualities322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNameLookup322
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- The pool contains existing logical names for a source position. The
choice is declarative, based on an ordinary proof, not search for a model
or a criterion for rejecting any program. -/
noncomputable def find (s : State) (pool : List Nat) (code : Expr) : Option Nat := by
  classical
  exact pool.find? (fun n => decide (Derives s (.variable n) code))

theorem exact_found {s : State} {pool : List Nat} {code : Expr} {name : Nat}
    (found : find s pool code = some name) :
    name ∈ pool ∧ Derives s (.variable name) code := by
  classical
  unfold find at found
  exact ⟨List.mem_of_find?_eq_some found,of_decide_eq_true (List.find?_some (p := fun n : Nat => decide (Derives s (.variable n) code)) found)⟩

theorem found_if {s : State} {pool : List Nat} {code : Expr}
    (present : ∃ name ∈ pool, Derives s (.variable name) code) :
    ∃ name, find s pool code = some name := by
  classical
  cases h : find s pool code with
  | some name => exact ⟨name,rfl⟩
  | none =>
    unfold find at h
    have missing := List.find?_eq_none.mp h
    obtain ⟨name,used,proof⟩ := present
    simpa [proof] using missing name used

theorem singleton_exact {s : State} {code : Expr} {name : Nat}
    (proof : Derives s (.variable name) code) : find s [name] code = some name := by
  classical
  simp [find,proof]

/-- Returning different names from two lawful pools cannot alter the
ordinary value. It need not make the logical names syntactically equal. -/
theorem choices_agree {s : State} {code : Expr} {p q : List Nat}
    (first : find s p code = some a) (second : find s q code = some b) :
    Derives s (.variable a) (.variable b) :=
  .trans (exact_found first).2 (.symm (exact_found second).2)

end Yulang.GeneralDeclarativeNameLookup322
