import Yulang.CommonRoleStatefulPathComplete
import Yulang.CommonRoleStatefulParentExample

/-! A declared finite associated path, ordinary solver, and actual Parent dictionary.
Path length is input data; no fuel/success/accessibility proof is an input.
This is still not general source inference or Paterson/K2 saturation. -/
namespace Yulang.CommonRoleStatefulPathParent
open CommonRoleStatefulIndexPath (expected)
open CommonRoleStatefulPathComplete
open CommonRoleStatefulParentExample (visible declarations_wellFormed parentGoal parent_str_resolved)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness
open CommonRoleCandidateStateFrontier (extend)

def lastSlot : List (Fin n) → Fin n → Fin n
  | [], receiver => receiver
  | output :: rest, _ => lastSlot rest output

theorem final_evidence (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (evidence : Evidence s.atoms receiver .str) :
    Evidence (expected outputs s).atoms (lastSlot outputs receiver) .str := by
  induction outputs generalizing receiver s with
  | nil => exact evidence
  | cons output rest ih => exact ih output (extend s output .str) (extension_evidence s output)

theorem final_materialized (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (models : (expected outputs (extend s receiver .str)).Models) :
    materialize (expected outputs (extend s receiver .str)).atoms (lastSlot outputs receiver) =
      some Roles.Examples.str := by
  have known := detect_of_models _ _ models
    (final_evidence outputs receiver _ (extension_evidence s receiver))
  simp only [materialize, known]
  rfl

def run (outputs : List (Fin n)) (receiver : Fin n) (s : State n) :
    Option (State n × Roles.Term × RoleDictionaries.Answer) := do
  let out ← checkedRun outputs receiver s
  let argument ← materialize out.atoms (lastSlot outputs receiver)
  pure (out, argument, RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal argument))

/-- Independent finite-entry result judgment: explicit generated equations,
ordinary model existence, ground argument, and declarative dictionary. -/
def Final (outputs : List (Fin n)) (receiver : Fin n) (s out : State n)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer) : Prop :=
  out = expected outputs (extend s receiver .str) ∧ out.Models ∧
    argument = Roles.Examples.str ∧
    ∃ dictionary : RoleDictionaries.Dictionary visible (parentGoal Roles.Examples.str),
      answer = .resolved dictionary.erase

theorem run_of_models (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (models : (expected outputs (extend s receiver .str)).Models) :
    run outputs receiver s = some (expected outputs (extend s receiver .str), Roles.Examples.str,
      RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal Roles.Examples.str)) := by
  have checked := (CommonRoleStatefulPathComplete.checked_exact outputs receiver s _).mpr ⟨rfl, models⟩
  unfold run
  rw [checked]
  change (materialize _ _).bind _ = _
  rw [final_materialized outputs receiver s models]
  rfl

/-- All finite paths and arbitrary old states. Neither success nor model existence
is an external premise of this iff. The source registry is the stated fixed fragment. -/
theorem outer_exact (outputs : List (Fin n)) (receiver : Fin n) (s out : State n)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer) :
    run outputs receiver s = some (out, argument, answer) ↔
      Final outputs receiver s out argument answer := by
  constructor
  · intro result
    unfold run at result
    cases checked : checkedRun outputs receiver s with
    | none => simp [checked] at result
    | some final =>
      obtain ⟨eq, models⟩ := (CommonRoleStatefulPathComplete.checked_exact ..).mp checked
      subst final
      have actual := run_of_models outputs receiver s models
      have same : some (expected outputs (extend s receiver .str), Roles.Examples.str,
          RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal Roles.Examples.str)) =
          some (out, argument, answer) := by
        exact actual.symm.trans (show run outputs receiver s = some (out, argument, answer) from result)
      cases same
      let dictionary := RoleDictionaries.buildResolved visible declarations_wellFormed
        (parentGoal Roles.Examples.str) parent_str_resolved
      exact ⟨rfl, models, rfl, dictionary,
        (RoleDictionaries.elaborate_success_iff ..).mpr ⟨dictionary, rfl⟩⟩
  · rintro ⟨rfl, models, rfl, dictionary, rfl⟩
    rw [run_of_models outputs receiver s models]
    rw [(RoleDictionaries.elaborate_success_iff ..).mpr ⟨dictionary, rfl⟩]

theorem success_visible (outputs : List (Fin n)) (receiver : Fin n) (s out : State n)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer)
    (result : run outputs receiver s = some (out, argument, answer)) :
    ∃ plan, answer = .resolved plan ∧
      ∀ implementation ∈ plan.declarations, implementation ∈ visible := by
  obtain ⟨_, _, _, dictionary, eq⟩ := (outer_exact ..).mp result
  exact ⟨dictionary.erase, eq, dictionary.all_visible⟩

end Yulang.CommonRoleStatefulPathParent
