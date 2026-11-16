import Yulang.GeneralDictionaryHeadSharing220
import Yulang.GeneralDictionaryDefaultBoundary208

/-! I-41 conflict ranges over all eligible current frames and journal models.
A missing frame or an empty journal is not called a sharing contradiction. -/
namespace Yulang.GeneralDictionaryHeadSharingConflict220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal (State Models)
open GeneralNominalCenteredHeadOutputs (Frame)
open GeneralDictionaryHeadSharing220 (Holds)
variable {roles : Roles.RoleDecls}

def Feasible (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  ∃ model, Models state model ∧ ∃ plan, Frame registry state.core root key plan ∧ Holds plan model

def AtKey (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  (∃ model, Models state model) ∧ (∃ plan, Frame registry state.core root key plan) ∧
    ¬ Feasible registry state root key

def Conflict (value : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∃ key children, B4TargetV7.Unique (GeneralDictionaryDefaultBoundary208.boundary roles)
    value state root key children ∧ AtKey (GeneralNominalCenteredHeadAllocEncoding.registry value) state root key

theorem atKey_inhabited (bad : AtKey registry state root key) : ∃ model, Models state model := bad.1

theorem atKey_has_frame (bad : AtKey registry state root key) : ∃ plan, Frame registry state.core root key plan := bad.2.1

theorem feasible_not_atKey (good : Feasible registry state root key) : ¬ AtKey registry state root key :=
  fun bad => bad.2.2 good

theorem atKey_iff (inhabited : ∃ model, Models state model)
    (framed : ∃ plan, Frame registry state.core root key plan) :
    AtKey registry state root key ↔ ¬ Feasible registry state root key :=
  ⟨fun bad => bad.2.2,fun bad => ⟨inhabited,framed,bad⟩⟩

theorem no_conflict_feasible
    (unique : B4TargetV7.Unique (GeneralDictionaryDefaultBoundary208.boundary roles) value state root key children)
    (inhabited : ∃ model, Models state model)
    (framed : ∃ plan, Frame (GeneralNominalCenteredHeadAllocEncoding.registry value) state.core root key plan)
    (clear : ¬ Conflict value state root) :
    Feasible (GeneralNominalCenteredHeadAllocEncoding.registry value) state root key := by
  classical
  apply Classical.byContradiction
  intro absent
  exact clear ⟨key,children,unique,inhabited,framed,absent⟩

end Yulang.GeneralDictionaryHeadSharingConflict220
