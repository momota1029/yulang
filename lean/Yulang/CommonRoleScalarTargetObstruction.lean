import Yulang.B4Skeleton
import Yulang.CommonRoleScalarRegistry

/-!
# An inhabited source witness against the old target overlap

This finite scalar adapter has a real empty ordinary state and empty visible
registry. Its actual executor returns pending, while the old formal target
also derives rejected. This refutes that target instantiation, not intended
language B4. No existing target or language rule is changed. The absent
knownness guard and lossless-tree alignment remain supervisor review items.
-/
namespace Yulang.CommonRoleScalarTargetObstruction
open CommonRoleScalarRegistry (Entry Candidate Known)
open CommonRoleSettledConstraints (State)
open CommonRoleOutermostResolver (Dictionary)
open Core.PresenceGeneration (Comp)
open B4Target

abbrev vocabulary : Vocabulary where
  Registry := List Entry
  State := State 1
  Demand := Nat
  Model := Fin 1 → Comp Common.model

/-- A concrete one-slot source fragment, not an arbitrary oracle for B4.
There are no where/associated updates in this leaf fragment. -/
def boundary : SourceBoundary vocabulary where
  Checked entries := Roles.WellFormed (CommonRoleScalarRegistry.visible entries)
  Models state assignment := PresenceNormalForm.All Common.model assignment state.atoms
  Step _ _ _ _ := False
  Stable _ _ _ := True
  Generated _ _ _ _ := False
  RootPending _ state _ := ∀ term, ¬ Known state 0 term
  RootK2 _ _ _ := False
  CandidateK2 _ _ _ := False
  InspectionPending _ _ _ := False
  Survivor entries state role key children := ∃ (term : Roles.Term) (entry : Entry),
    Known state 0 term ∧ Candidate entries role term entry.impl ∧ entry.key = key ∧ children = []
  Evidence entries _ assignment role dictionary := ∃ entry : Entry, entry ∈ (entries : List Entry) ∧
    entry.role = role ∧ dictionary = Dictionary.node entry.key [] ∧
      Common.Equivalent (assignment 0).1 (.base entry.scalar.base)
  Reorders := List.Perm
  DictionaryEquivalent := Eq

/-- The witness registry passes the actual leaf declaration check. -/
theorem empty_checked : boundary.Checked [] := CommonRoleScalarRegistry.wellFormed []

/-- The original state is inhabited by an actual Common model. -/
theorem empty_has_model : ∃ model, boundary.Models State.empty model :=
  ⟨fun _ => Comp.pure Common.model .bottom, by intro atom member; cases member⟩

theorem empty_pending (role : Nat) : boundary.RootPending [] State.empty role := by
  intro term known
  obtain ⟨scalar, evidence, _⟩ := known
  exact List.not_mem_nil evidence.1

/-- No source-visible declaration exists, independently of receiver knowledge. -/
theorem empty_survivors (state : State 1) (role key : Nat) (children : List Nat) :
    ¬ boundary.Survivor [] state role key children := by
  rintro ⟨term, entry, _, candidate, _⟩
  obtain ⟨source, member, _⟩ := candidate
  cases member

/-- The old formal classifier assigns two different root tags to one
well-formed, model-inhabited source input. -/
theorem old_target_double_classification (role : Nat) :
    B4Target.Classify boundary [] State.empty role .pending ∧
      B4Target.Classify boundary [] State.empty role .rejected := by
  exact ⟨.pending (empty_pending role),
    .rejected (Or.inr (Or.inr (empty_survivors State.empty role)))⟩

/-- The executable source adapter itself has the intended pending behavior. -/
theorem actual_source_pending (role : Nat) :
    CommonRoleScalarRegistry.run [] role (0 : Fin 1) State.empty = some .pending :=
  CommonRoleScalarRegistry.empty_pending [] role 0

/-- With no source updates, genuine reachability cannot invent a new state
solely to evade the conflicting classification. -/
theorem steps_unchanged (entries : List Entry) (role : Nat) (before after : State 1)
    (trace : Steps (boundary.Step entries role) before after) : after = before := by
  cases trace with
  | refl => rfl
  | tail _ step => exact False.elim step

/-- No executor satisfies the old five-clause formal target on this concrete
fragment. This is not a refutation of the intended corrected language target. -/
theorem old_target_impossible (executor : Executor vocabulary) : ¬ B4Skeleton.B4Statement boundary executor := by
  intro target
  have reached := (target.1 [] empty_checked State.empty 0).2.1
  have unchanged := steps_unchanged [] 0 State.empty _ reached
  have pending : boundary.RootPending [] (executor.run [] State.empty 0).1 0 := by
    rw [unchanged]
    exact empty_pending 0
  exact B4Skeleton.pending_empty_survivors_obstruction boundary executor [] empty_checked
    State.empty 0 pending (empty_survivors _ 0) target

/-- The old twelve-field bridge package cannot be instantiated for this
source adapter before the formal target's knownness boundary is aligned. -/
theorem old_bridges_impossible (executor : Executor vocabulary) (frontiers : B4Skeleton.Frontiers vocabulary) :
    ¬ B4Skeleton.B4Bridges boundary executor frontiers := by
  intro bridges
  exact old_target_impossible executor (B4Skeleton.b4_of_bridges boundary executor frontiers bridges)

end Yulang.CommonRoleScalarTargetObstruction
