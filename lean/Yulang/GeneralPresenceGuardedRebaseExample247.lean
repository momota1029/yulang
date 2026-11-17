import Yulang.GeneralPresenceGuardedRebase247
import Yulang.GeneralPresenceGuardedExamples247
namespace Yulang.GeneralPresenceGuardedRebaseExample247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceGuardedBlock246 GeneralPresenceGuardedEnvironment247
open GeneralPresenceGuardedRebase247
open CommonNominalFullCarrier

def old : Closure Nat :=
 ⟨2,1,GeneralPresenceGuardedExamples247.body,GeneralPresenceGuardedExamples247.targets,GeneralPresenceGuardedExamples247.parametersAt,GeneralPresenceGuardedExamples247.targets_injective,GeneralPresenceGuardedExamples247.parameters_separate⟩

def fresh : Body Nat 2 1 := fun index => if index.val = 0 then .bottom else .top

def state (atoms : List (Atom Nat)) : State Nat := ⟨old,[],atoms⟩

def sharedNames (name : Nat) : Prop := name ≠ 2 ∧ name ≠ 3

theorem targets_private : ∀ name, sharedNames name → ∀ index, old.targets index ≠ name := by
 intro name outside index
 have bound : index.val < 2 := index.isLt
 change 2 + index.val ≠ name
 rcases outside with ⟨first,last⟩
 omega

/-- The consumer list is arbitrary and may contain direct private type reads. -/
theorem arbitrary_consumers_exact (atoms : List (Atom Nat)) (boundary : Nat → Comp model) :
 (∃ assignment, Models (state atoms) assignment ∧ Agrees sharedNames assignment boundary) ↔
 (∃ assignment, Models (rebase (state atoms) fresh GeneralPresenceGuardedExamples247.parametersAt GeneralPresenceGuardedExamples247.parameters_separate) assignment ∧
   Agrees sharedNames assignment boundary) :=
 public_models_iff (state atoms) fresh GeneralPresenceGuardedExamples247.parametersAt GeneralPresenceGuardedExamples247.parameters_separate sharedNames targets_private boundary

def newAssignment (boundary : Nat → Comp model) : Nat → Comp model :=
 (freshClosure old fresh GeneralPresenceGuardedExamples247.parametersAt GeneralPresenceGuardedExamples247.parameters_separate).read boundary

theorem raw_private_becomes_bottom (boundary : Nat → Comp model) : (newAssignment boundary 2).1 = .bottom := by
 change (extend fresh GeneralPresenceGuardedExamples247.targets GeneralPresenceGuardedExamples247.parametersAt boundary (GeneralPresenceGuardedExamples247.targets 0)).1 = .bottom
 rw [extend_at fresh GeneralPresenceGuardedExamples247.targets GeneralPresenceGuardedExamples247.targets_injective]
 unfold values
 rw [CommonNominalFullGuardedClosure.instantiate_graph]
 rfl

theorem old_private_not_bottom (boundary : Nat → Comp model) : (old.read boundary 2).1 ≠ .bottom := by
 change (extend GeneralPresenceGuardedExamples247.body GeneralPresenceGuardedExamples247.targets GeneralPresenceGuardedExamples247.parametersAt boundary (GeneralPresenceGuardedExamples247.targets 0)).1 ≠ .bottom
 rw [extend_at GeneralPresenceGuardedExamples247.body GeneralPresenceGuardedExamples247.targets GeneralPresenceGuardedExamples247.targets_injective]
 unfold values
 rw [CommonNominalFullGuardedClosure.instantiate_graph]
 intro impossible
 cases impossible

/-- The explicit old closure, rather than the fresh raw coordinate, preserves
this private query's literal old value. -/
theorem transported_private (atoms : List (Atom Nat)) (boundary : Nat → Comp model) :
 (read (rebase (state atoms) fresh GeneralPresenceGuardedExamples247.parametersAt GeneralPresenceGuardedExamples247.parameters_separate).environment (newAssignment boundary) 2).1 =
 (old.read boundary 2).1 := by
 change (old.read (newAssignment boundary) 2).1 = (old.read boundary 2).1
 exact congrArg (fun assignment => (assignment 2).1)
   (closure_absorbs old fresh GeneralPresenceGuardedExamples247.parametersAt GeneralPresenceGuardedExamples247.parameters_separate boundary)

theorem raw_private_changed (boundary : Nat → Comp model) :
 (newAssignment boundary 2).1 ≠ (old.read boundary 2).1 := by
 rw [raw_private_becomes_bottom]
 exact Ne.symm (old_private_not_bottom boundary)
end Yulang.GeneralPresenceGuardedRebaseExample247
