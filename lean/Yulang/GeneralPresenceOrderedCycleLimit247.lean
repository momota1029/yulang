import Yulang.GeneralPresenceOrderedRebase247

/-! A self-alias is not an ordered definition. Naively applying the finite
rewrite to it and replacing its definition can shrink public solutions even
in the concrete Common model. This tests the SafeOrder premise; it is not a
source-reachability result or a source-language counterexample. -/
namespace Yulang.GeneralPresenceOrderedCycleLimit247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedDependence247
open CommonNominalFullCarrier

def old : List (Entry Nat) := [(2,.var 2)]
def fresh : List (Entry Nat) := [(2,.exactEmpty)]
def consumers : List (Atom Nat) := equations 2 (.var 0)
def boundary : Nat → Comp model := fun _ => (.emptyRecord,Common.rowEmpty)

theorem old_not_safe : ¬ SafeOrder old := by
  simp [old,SafeOrder,GeneralPresenceUsedSupport245.typedReads]

theorem fresh_safe : SafeOrder fresh := by
  simp [fresh,SafeOrder,GeneralPresenceUsedSupport245.typedReads]

theorem targets_within : TargetsWithin fresh old := by
  intro entry member
  have same : entry = (2,TyTerm.exactEmpty) := by simpa [fresh] using member
  subst entry
  exact ⟨(2,.var 2),by simp [old],rfl⟩

theorem rewrite_unchanged : rewrite old consumers = consumers := rfl

theorem old_models : All model boundary (consumers ++ block old) := by
  intro atom member
  simp only [consumers,old,block,equations,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl | rfl) | (rfl | rfl)
  all_goals exact subtype_refl _

theorem old_public_solution :
    ∃ assignment, All model assignment (consumers ++ block old) ∧ assignment 0 = boundary 0 :=
  ⟨boundary,old_models,rfl⟩

theorem no_new_public_solution :
    ¬ ∃ assignment, All model assignment (rewrite old consumers ++ block fresh) ∧
      assignment 0 = boundary 0 := by
  rintro ⟨assignment,valid,agreement⟩
  obtain ⟨used,defined⟩ := (all_append model assignment _ _).mp valid
  rw [rewrite_unchanged] at used
  have publicToPrivate : model.subTy (assignment 0).1 (assignment 2).1 :=
    used (.tyLe (.var 0) (.var 2)) (by simp [consumers,equations])
  have privateToEmpty : model.subTy (assignment 2).1 .exactEmpty :=
    defined (.tyLe (.var 2) .exactEmpty) (by simp [fresh,block,equations])
  have impossible := subtype_trans publicToPrivate privateToEmpty
  rw [agreement] at impossible
  exact width_not_below_exactEmpty impossible

theorem public_equivalence_fails : ¬
    ((∃ assignment, All model assignment (consumers ++ block old) ∧ assignment 0 = boundary 0) ↔
     (∃ assignment, All model assignment (rewrite old consumers ++ block fresh) ∧ assignment 0 = boundary 0)) := by
  intro claimed
  exact no_new_public_solution (claimed.mp old_public_solution)

end Yulang.GeneralPresenceOrderedCycleLimit247
