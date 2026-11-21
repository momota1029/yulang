import Yulang.GeneralDeclarativeOrigins321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSettled321

/-! Finite proof of completed source dependencies, not an iteration or
termination assertion. An inference rule supplies its actual dependency
list; a cycle cannot be justified by labeling all its members complete. -/
mutual
 inductive Done (rule : List Nat → Nat → Prop) : Nat → Prop where
  | usingRule : rule prerequisites owner → DoneAll rule prerequisites → Done rule owner
 inductive DoneAll (rule : List Nat → Nat → Prop) : List Nat → Prop where
  | nil : DoneAll rule []
  | cons : Done rule o → DoneAll rule os → DoneAll rule (o :: os)
end

theorem least_closed {rule : List Nat → Nat → Prop} {on : Nat → Prop}
    (closed : ∀ list owner, rule list owner → (∀ n ∈ list, on n) → on owner)
    (finished : Done rule owner) : on owner := by
  exact Done.rec
    (motive_1 := fun o _ => on o)
    (motive_2 := fun prereqs _ => ∀ n ∈ prereqs, on n)
    (by intro prereqs who inferred _ ready; exact closed prereqs who inferred ready)
    (by intro n h; cases h)
    (by
      intro o os _ _ head tail n found
      rcases List.mem_cons.mp found with rfl|later
      · exact head
      · exact tail n later)
    finished

/-- An output-only dependency component with no possible rule grounded
outside that component cannot bootstrap completed support. -/
theorem no_self_grounding {rule : List Nat → Nat → Prop} {island : Nat → Prop}
    (unfounded : ∀ deps owner, island owner → rule deps owner → ∃ dep ∈ deps, island dep)
    (inside : island owner) : ¬Done rule owner := by
  intro proof
  have no : ¬island owner :=
    least_closed (on := fun n => ¬island n)
      (fun deps who inferred ready inSet =>
        let ⟨dep,listed,member⟩ := unfounded deps who inSet inferred
        ready dep listed member) proof
  exact no inside

theorem external_witness {rule : List Nat → Nat → Prop} (grounded : rule [] owner) :
    Done rule owner := .usingRule grounded .nil

theorem pending_origin_not_available {rule : List Nat → Nat → Prop} {island : Nat → Prop}
    (unfounded : ∀ deps owner, island owner → rule deps owner → ∃ dep ∈ deps, island dep)
    (inside : island owner) :
    ¬GeneralDeclarativeOrigins321.Available (Done rule) (.output owner) := by
  intro h
  cases h with
  | completed proof => exact no_self_grounding unfounded inside proof

end Yulang.GeneralDeclarativeSettled321
