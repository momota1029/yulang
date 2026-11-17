import Yulang.GeneralPresenceOrderedRebase247
/-! Arbitrarily long finite refresh sequences preserve the same public solution
set. This is an invariant, not termination: no bound on list length or textual
substitution growth follows, and source production of the certificates is open. -/
namespace Yulang.GeneralPresenceOrderedRefreshSequence247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedRebase247 GeneralPresenceModelCongruence245
variable {Name : Type} [DecidableEq Name]

structure State (Name : Type) where
 definitions : List (Entry Name)
 consumers : List (Atom Name)

def refresh (state : State Name) (fresh : List (Entry Name)) : State Name :=
 ⟨fresh,rewrite state.definitions state.consumers⟩

def run : State Name → List (List (Entry Name)) → State Name
 | state, [] => state
 | state, fresh :: rest => run (refresh state fresh) rest

def ValidSteps : List (Entry Name) → List (List (Entry Name)) → Prop
 | _, [] => True
 | old, fresh :: rest => SafeOrder fresh ∧ TargetsWithin fresh old ∧ ValidSteps fresh rest

def PublicModels (model : Model) (sharedNames : Name → Prop)
 (boundary : Name → Comp model) (state : State Name) : Prop :=
 ∃ assignment, All model assignment (state.consumers ++ block state.definitions) ∧
   Agrees model sharedNames assignment boundary

theorem refresh_preserves (model : Model) (laws : Laws model) (state : State Name)
 (fresh : List (Entry Name)) (oldSafe : SafeOrder state.definitions)
 (freshSafe : SafeOrder fresh) (within : TargetsWithin fresh state.definitions)
 (sharedNames : Name → Prop)
 (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ state.definitions, entry.1 ≠ name)
 (boundary : Name → Comp model) :
 PublicModels model sharedNames boundary state ↔ PublicModels model sharedNames boundary (refresh state fresh) :=
 public_models_iff model laws state.definitions fresh oldSafe freshSafe within state.consumers
   sharedNames privateTargets boundary

theorem run_preserves (model : Model) (laws : Laws model) (state : State Name)
 (updates : List (List (Entry Name))) (safe : SafeOrder state.definitions)
 (valid : ValidSteps state.definitions updates) (sharedNames : Name → Prop)
 (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ state.definitions, entry.1 ≠ name)
 (boundary : Name → Comp model) :
 PublicModels model sharedNames boundary state ↔ PublicModels model sharedNames boundary (run state updates) := by
 induction updates generalizing state with
 | nil => exact Iff.rfl
 | cons fresh rest ih =>
   obtain ⟨freshSafe,within,tail⟩ := valid
   apply (refresh_preserves model laws state fresh safe freshSafe within sharedNames privateTargets boundary).trans
   apply ih (refresh state fresh) freshSafe tail
   intro name shared entry member
   obtain ⟨original,present,equal⟩ := within entry member
   rw [← equal]
   exact privateTargets name shared original present
end Yulang.GeneralPresenceOrderedRefreshSequence247
