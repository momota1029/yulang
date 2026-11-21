import Yulang.GeneralDeclarativeFootprint321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFresh321
open GeneralDeclarativeFootprint321 (stateNames value_same preserves_models)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeHead320 (Equation State Models environment)
open GeneralDeclarativeEntailment320 (Holds appendFacts model_append)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

/-- Simultaneous ordinary definitions with no feedback to their own fresh
names. Keep the old row component even when a new type name is defined. -/
def extend (before : Assignment) (defs : List Equation) : Assignment := fun n =>
  match defs.find? (fun eqn => eqn.left == n) with
  | none => before n
  | some row => (value (environment before) .actual row.right,(before n).2)

def Fresh (s : State) (defs : List Equation) : Prop :=
  (∀ row ∈ defs, row.left ∉ stateNames s) ∧
  (∀ row ∈ defs, ∀ other ∈ defs, row.left = other.left → row.right = other.right) ∧
  ∀ row ∈ defs, ∀ other ∈ defs, other.left ∉ names row.right

theorem old_name {before : Assignment} {defs : List Equation} {n}
    (outside : ∀ row ∈ defs, row.left ≠ n) : extend before defs n = before n := by
  cases search : defs.find? (fun eqn => eqn.left == n) with
  | none => simp [extend,search]
  | some row =>
    have found : row.left = n := beq_iff_eq.mp (List.find?_some (p := fun eqn : Equation => eqn.left == n) search)
    exact False.elim (outside row (List.mem_of_find?_eq_some search) found)

theorem defined_value {before : Assignment} {defs : List Equation} {s : State}
    (fresh : Fresh s defs) {row : Equation} (used : row ∈ defs) :
    (extend before defs row.left).1 = value (environment before) .actual row.right := by
  cases search : defs.find? (fun eqn => eqn.left == row.left) with
  | none =>
    have absent : ∀ eqn ∈ defs, eqn.left ≠ row.left := by simpa [List.find?_eq_none] using search
    exact False.elim (absent row used rfl)
  | some selected =>
    have named : selected.left = row.left := beq_iff_eq.mp (List.find?_some (p := fun eqn : Equation => eqn.left == row.left) search)
    have rhs := fresh.2.1 selected (List.mem_of_find?_eq_some search) row used named
    simp [extend,search,rhs]

theorem preserves_names {before : Assignment} {defs : List Equation} {s : State}
    (fresh : Fresh s defs) : ∀ n ∈ stateNames s, extend before defs n = before n := by
  intro n listed
  exact old_name (fun row there eq => fresh.1 row there (eq.symm ▸ listed))

theorem new_eq {before : Assignment} {defs : List Equation} {s : State}
    (fresh : Fresh s defs) {row : Equation} (used : row ∈ defs) :
    Holds (extend before defs) row := by
  have same : ∀ n ∈ names row.right, extend before defs n = before n := by
    intro n listed
    exact old_name (fun new found eq => fresh.2.2 row used new found (eq.symm ▸ listed))
  simp only [Holds,defined_value fresh used,value_same _ _ .actual _ same]
  exact eqv_refl _

theorem preserves_and_extends {s : State} {defs : List Equation} (fresh : Fresh s defs)
    (before : Assignment) (valid : Models s before) :
    Models (appendFacts s defs) (extend before defs) ∧
      (∀ n ∈ stateNames s, extend before defs n = before n) :=
  ⟨(model_append _).mpr ⟨(preserves_models s (preserves_names fresh)).mpr valid,
      fun _ there => new_eq fresh there⟩,preserves_names fresh⟩

/-- Conservative over old logical names; not literal equality of two sets
of total assignments on additional names. -/
theorem old_model_projection {s : State} {defs : List Equation} (fresh : Fresh s defs) (before : Assignment) :
    Models s before ↔ ∃ extended, Models (appendFacts s defs) extended ∧
      ∀ n ∈ stateNames s, extended n = before n := by
  constructor
  · intro valid
    exact ⟨extend before defs,preserves_and_extends fresh before valid⟩
  · rintro ⟨extended,valid,kept⟩
    exact (preserves_models s kept).mp ((model_append extended).mp valid).1

end Yulang.GeneralDeclarativeFresh321
