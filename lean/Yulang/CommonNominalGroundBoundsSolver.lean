import Yulang.CommonNominalTypeBounds
import Yulang.CommonNominalGroundAdapter

/-!
# Actual checked ground bounds with unrestricted full nominal instances

Fixed bounds use exactly the existing explicit ground adapter grammar and its
computed normalization/checker. Slot values and family parameters use the full
new regular nominal carrier. The checker discharges every static consistency
pair, so no compatibility oracle or residual parameter condition remains.
Dynamic constructed-node bounds are not included in this fixed-bound stage.
-/

namespace Yulang.CommonNominalGroundBoundsSolver

open CommonNominalCarrier
open CommonNominalTypeFlow (Edge)
open CommonGroundNominalCasts (Ground)
open CommonNominalGroundAdapter (meaning)

structure Problem (slots : Nat) where
  edges : List (Edge slots)
  lower : List (Fin slots × Ground)
  upper : List (Fin slots × Ground)

def Problem.meaning (problem : Problem slots) : CommonNominalTypeBounds.Problem slots :=
  ⟨problem.edges, problem.lower.map (Prod.map id CommonNominalGroundAdapter.meaning),
    problem.upper.map (Prod.map id CommonNominalGroundAdapter.meaning)⟩

def checkPair (problem : Problem slots) (first last : Fin slots × Ground) : Bool :=
  !CastGraph.reachable problem.edges first.1 last.1 ||
    CommonGroundNominalCasts.fitsCommonGround.check
      (CommonGroundNominalCasts.lower first.2) (CommonGroundNominalCasts.lower last.2)

def check (problem : Problem slots) : Bool :=
  problem.lower.all fun first => problem.upper.all fun last => checkPair problem first last

theorem check_pair_exact (problem : Problem slots) (first last : Fin slots × Ground) :
    checkPair problem first last = true ↔
      CastGraph.Path problem.edges first.1 last.1 → CommonNominalCarrier.Subtype (meaning first.2) (meaning last.2) := by
  cases reached : CastGraph.reachable problem.edges first.1 last.1 with
  | false =>
      have absent : ¬ CastGraph.Path problem.edges first.1 last.1 := by
        intro path
        have accepted := (CastGraph.reachable_exact _ _ _).mpr path
        simp [reached] at accepted
      simp [checkPair, reached, absent]
  | true =>
      have path := (CastGraph.reachable_exact _ _ _).mp reached
      simp only [checkPair, reached, Bool.not_true, Bool.false_or, path, true_implies]
      exact CommonNominalGroundAdapter.ground_check_exact first.2 last.2

theorem check_exact (problem : Problem slots) : check problem = true ↔ CommonNominalTypeBounds.Consistent problem.meaning := by
  simp only [check, List.all_eq_true, check_pair_exact]
  constructor
  · intro checked first firstMember last lastMember path
    obtain ⟨originalFirst, firstPresent, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨originalLast, lastPresent, rfl⟩ := List.mem_map.mp lastMember
    exact checked originalFirst firstPresent originalLast lastPresent path
  · intro consistent first firstMember last lastMember path
    exact consistent _ (List.mem_map.mpr ⟨first, firstMember, rfl⟩)
      _ (List.mem_map.mpr ⟨last, lastMember, rfl⟩) path

abbrev Scheme (slots : Nat) := CommonNominalTypeBounds.Problem slots
abbrev Parameters (slots : Nat) := Fin slots → Ty

def solve (problem : Problem slots) : List (Scheme slots) :=
  if check problem then [problem.meaning] else []

private theorem returned (problem : Problem slots) (scheme : Scheme slots) (member : scheme ∈ solve problem) :
    check problem = true ∧ scheme = problem.meaning := by
  cases checked : check problem <;> simp [solve, checked] at member ⊢
  exact member

theorem all_parameters_models (problem : Problem slots) (scheme : Scheme slots) (member : scheme ∈ solve problem)
    (parameters : Parameters slots) :
    CommonNominalTypeBounds.Models problem.meaning (CommonNominalTypeBounds.instantiate scheme parameters) := by
  obtain ⟨checked, rfl⟩ := returned problem scheme member
  exact CommonNominalTypeBounds.all_parameters_models problem.meaning ((check_exact problem).mp checked) parameters

theorem solve_all_instances_exact (problem : Problem slots) (values : Fin slots → Ty) :
    CommonNominalTypeBounds.Models problem.meaning values ↔
      ∃ scheme ∈ solve problem, ∃ parameters : Parameters slots, ∀ index,
        Equivalent (CommonNominalTypeBounds.instantiate scheme parameters index) (values index) := by
  constructor
  · intro models
    have consistent := CommonNominalTypeBounds.models_consistent problem.meaning values models
    have checked := (check_exact problem).mpr consistent
    exact ⟨problem.meaning, by simp [solve, checked], values,
      CommonNominalTypeBounds.model_retraction problem.meaning values models⟩
  · rintro ⟨scheme, member, parameters, recovered⟩
    obtain ⟨checked, rfl⟩ := returned problem scheme member
    exact CommonNominalTypeBounds.models_of_recovered problem.meaning ((check_exact problem).mp checked)
      parameters values recovered

theorem rejected_iff (problem : Problem slots) : solve problem = [] ↔ ¬ ∃ values, CommonNominalTypeBounds.Models problem.meaning values := by
  constructor
  · intro rejected ⟨values, models⟩
    obtain ⟨scheme, member, _⟩ := (solve_all_instances_exact problem values).mp models
    simp [rejected] at member
  · intro absent
    cases checked : check problem with
    | false => simp [solve, checked]
    | true =>
        have member : problem.meaning ∈ solve problem := by simp [solve, checked]
        exact False.elim (absent ⟨_, all_parameters_models problem problem.meaning member (fun _ => .bottom)⟩)

end Yulang.CommonNominalGroundBoundsSolver
