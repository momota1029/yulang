import Yulang.CommonRoleStatefulPathParent

namespace Yulang.CommonRolePathOrder
open CommonRoleSettledConstraints (State)
open CommonRoleStatefulIndexPath (expected expected_models)
open CommonRoleCandidateStateFrontier (extend)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

def SameTargets (left right : List (Fin n)) : Prop := ∀ slot, slot ∈ left ↔ slot ∈ right

theorem expected_same_models (left right : List (Fin n)) (same : SameTargets left right)
    (s : State n) (values : Fin n → Comp Common.model) :
    All Common.model values (expected left s).atoms ↔
      All Common.model values (expected right s).atoms := by
  rw [expected_models, expected_models]
  exact and_congr_right fun _ => forall_congr' fun slot => imp_congr (same slot) Iff.rfl

theorem models_equivalent (left right : List (Fin n)) (same : SameTargets left right)
    (s : State n) : (expected left s).Models ↔ (expected right s).Models :=
  exists_congr fun values => expected_same_models left right same s values

def observable (result : Option (State n × Roles.Term × RoleDictionaries.Answer)) :=
  result.map fun item => (item.2.1, item.2.2)

theorem no_models_none (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (bad : ¬ (expected outputs (extend s receiver .str)).Models) :
    CommonRoleStatefulPathParent.run outputs receiver s = none := by
  cases found : CommonRoleStatefulPathParent.run outputs receiver s with
  | none => rfl
  | some value =>
    rcases value with ⟨out, argument, answer⟩
    obtain ⟨rfl, model, _, _⟩ := (CommonRoleStatefulPathParent.outer_exact ..).mp found
    exact False.elim (bad model)

/-- Unconditional equality of both successful and absent observable results.
The explicit finite path and fixed str seed remain part of the fragment. -/
theorem observable_order_independent (left right : List (Fin n))
    (same : SameTargets left right) (receiver : Fin n) (s : State n) :
    observable (CommonRoleStatefulPathParent.run left receiver s) =
      observable (CommonRoleStatefulPathParent.run right receiver s) := by
  by_cases models : (expected left (extend s receiver .str)).Models
  · have other := (models_equivalent left right same (extend s receiver .str)).mp models
    rw [CommonRoleStatefulPathParent.run_of_models left receiver s models,
      CommonRoleStatefulPathParent.run_of_models right receiver s other]
    rfl
  · have other : ¬ (expected right (extend s receiver .str)).Models :=
      fun h => models ((models_equivalent left right same (extend s receiver .str)).mpr h)
    rw [no_models_none left receiver s models, no_models_none right receiver s other]

/-- Permutation is one sufficient case; duplicate multiplicities are not semantically relevant. -/
theorem permutation_observable (left right : List (Fin n)) (perm : left.Perm right)
    (receiver : Fin n) (s : State n) :
    observable (CommonRoleStatefulPathParent.run left receiver s) =
      observable (CommonRoleStatefulPathParent.run right receiver s) :=
  observable_order_independent left right (fun _ => perm.mem_iff) receiver s

end Yulang.CommonRolePathOrder
