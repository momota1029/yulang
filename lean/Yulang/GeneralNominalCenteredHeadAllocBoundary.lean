import Yulang.GeneralNominalCenteredHeadAllocAllocation
import Yulang.GeneralNominalCenteredHeadMatCanonicalClosure

namespace Yulang.GeneralNominalCenteredHeadAllocBoundary
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadMatStepLocal (vocabulary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls}

abbrev Step (value : Registry) := GeneralNominalCenteredHeadMatStepKernel.Step (registry value) (roles := roles)
abbrev Stable (value : Registry) := GeneralNominalCenteredHeadMatStepKernel.Stable (registry value) (roles := roles)

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) :=
  { GeneralNominalCenteredHeadMatStepLocal.fields roles with
    CandidateK2 := fun value => (GeneralNominalCenteredHeadMatStepLocal.fields roles).CandidateK2 (registry value)
    InspectionPending := fun value => (GeneralNominalCenteredHeadMatStepLocal.fields roles).InspectionPending (registry value)
    Survivor := fun value => (GeneralNominalCenteredHeadMatStepLocal.fields roles).Survivor (registry value) }

def remaining (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Remaining (vocabulary roles) where
  Step := Step
  Stable := Stable
  Generated := fun _ state => GeneralNominalSaturationState.Generated state.core.erased.current
  Evidence := fun value state => GeneralDictionaryFeedbackEvidence.evidence roles (registry value) state.core.erased.current

def boundary (roles : Roles.RoleDecls) : B4TargetV6.SourceBoundary (vocabulary roles) where
  toV5 := { toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) (remaining roles)
            Initial := GeneralNominalCenteredHeadMatStepBoundary.Initial }
  OutputConflict := fun value => GeneralNominalCenteredHeadMatStepLocal.OutputConflict (registry value)

abbrev Local (value : Registry) (state : State roles) := B4TargetV6.Local (boundary roles) value state

theorem checked_compiled (checked : (boundary roles).Checked value) :
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Checked (registry value) :=
  ⟨checked.1,GeneralNominalCenteredHeadAllocEncoding.registry_checked checked.2⟩

theorem initial_compiled (initial : (boundary roles).Initial value root state) :
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Initial (registry value) root state := by
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := initial
  exact ⟨context,labels,GeneralNominalCenteredHeadAllocEncoding.initial_source source,point,ground,
    GeneralNominalCenteredHeadAllocEncoding.coverage coverage,rfl⟩

theorem reachable_compiled (reachable : B4TargetV6.Reachable (boundary roles) value root state) :
    B4TargetV6.Reachable (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) (registry value) root state := by
  obtain ⟨start,initial,path⟩ := reachable
  exact ⟨start,initial_compiled initial,path⟩

theorem local_iff : Local value state demand frontier ↔
    GeneralNominalCenteredHeadMatStepBoundary.Local (registry value) state demand frontier := by
  constructor <;> intro chosen <;> cases chosen with
  | pending h => exact .pending h
  | inspectionPending a b c d => exact .inspectionPending a b c d
  | rejected h => exact .rejected h
  | ambiguous a b c d => exact .ambiguous a b c d
  | selected a b c => exact .selected a b c

theorem local_eq : Local value state = GeneralNominalCenteredHeadMatStepBoundary.Local (registry value) state := by
  funext demand frontier
  exact propext local_iff

theorem local_total (checked : (boundary roles).Checked value) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local value state root frontier := by
  obtain ⟨frontier,chosen⟩ := GeneralNominalCenteredHeadMatStepBoundary.local_total (checked_compiled checked).2 state root
  exact ⟨frontier,local_iff.mpr chosen⟩

theorem local_functional (one : Local value state root first) (two : Local value state root last) : first = last :=
  B4TargetV6.local_functional one two

theorem initialReorders (order : (boundary roles).Reorders first last)
    (initial : (boundary roles).Initial first root state) : (boundary roles).Initial last root state :=
  GeneralNominalCenteredHeadMatStepBoundary.initialReorders order initial

theorem stepModels (value : Registry) (checked : (boundary roles).Checked value) (root : Occurrence roles)
    (before after : State roles) (reachable : B4TargetV6.Reachable (boundary roles) value root before)
    (step : Step value root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  GeneralNominalCenteredHeadMatStepBoundary.stepModels (registry value) (checked_compiled checked) root before after
    (reachable_compiled reachable) step

theorem closure (value : Registry) (checked : (boundary roles).Checked value) (state : State roles)
    (root : Occurrence roles) (reachable : B4TargetV6.Reachable (boundary roles) value root state)
    (halted : ∀ next, ¬ Step value root state next) :
    Stable value state root ∧ ∀ child, (boundary roles).Generated value state root child → Stable value state child :=
  GeneralNominalCenteredHeadMatStepBoundary.closure (registry value) (checked_compiled checked) state root
    (reachable_compiled reachable) halted

theorem whereAccessible (value : Registry) (state : State roles) (root : Occurrence roles) :
    Acc (CommonRoleOutermostResolver.Child (Local value state)) root := by
  rw [local_eq]
  exact GeneralNominalCenteredHeadMatStepBoundary.whereAccessible (registry value) state root

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (boundary roles).DictionaryEquivalent dictionary dictionary := rfl

end Yulang.GeneralNominalCenteredHeadAllocBoundary
