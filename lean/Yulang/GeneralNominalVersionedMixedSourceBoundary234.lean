import Yulang.GeneralNominalVersionedMixedBoundary234
import Yulang.B4SkeletonV8
set_option backward.isDefEq.respectTransparency false
/-! Source-registry adapter using the established HeadAlloc encoding.
Initial source formation stays in the original registry; operational and
diagnostic consumers read its encoded registry, as in the prior source boundary. -/
namespace Yulang.GeneralNominalVersionedMixedSourceBoundary234
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls}

def boundary (roles : Roles.RoleDecls) :
    B4TargetV8.SourceBoundary (GeneralNominalVersionedDiagnostic232.vocabulary roles) :=
  { GeneralNominalVersionedMixedBoundary234.boundary roles with
    CandidateK2 := fun value => (GeneralNominalVersionedMixedBoundary234.boundary roles).CandidateK2 (registry value)
    InspectionPending := fun value => (GeneralNominalVersionedMixedBoundary234.boundary roles).InspectionPending (registry value)
    Survivor := fun value => (GeneralNominalVersionedMixedBoundary234.boundary roles).Survivor (registry value)
    Step := fun value => GeneralNominalVersionedMixedKernel234.Step (registry value)
    Stable := fun value => GeneralNominalVersionedMixedKernel234.Stable (registry value)
    Evidence := fun value state => GeneralNominalVersionedEvidence231.Evidence (registry value) state.core
    OutputConflict := fun value => GeneralNominalVersionedDiagnostic232.OutputConflict (registry value)
    SharingConflict := fun value => GeneralNominalVersionedDiagnostic232.SharingConflict (registry value) }

abbrev Local (value : Registry) (state : State roles) := B4TargetV8.Local (boundary roles) value state

theorem checked_compiled (checked : (boundary roles).Checked value) :
    (GeneralNominalVersionedMixedBoundary234.boundary roles).Checked (registry value) :=
  ⟨checked.1,GeneralNominalCenteredHeadAllocEncoding.registry_checked checked.2⟩

theorem initial_compiled (initial : (boundary roles).Initial value root state) :
    (GeneralNominalVersionedMixedBoundary234.boundary roles).Initial (registry value) root state := by
  obtain ⟨legacy,source,same⟩ := initial
  exact ⟨legacy,GeneralNominalCenteredHeadAllocBoundary.initial_compiled source,same⟩

theorem reachable_compiled (reachable : B4TargetV8.Reachable (boundary roles) value root state) :
    B4TargetV8.Reachable (GeneralNominalVersionedMixedBoundary234.boundary roles) (registry value) root state := by
  obtain ⟨start,initial,path⟩ := reachable
  exact ⟨start,initial_compiled initial,path⟩

theorem v6_local_iff : B4TargetV6.Local (boundary roles).toV7.toV6 value state root frontier ↔
    B4TargetV6.Local (GeneralNominalVersionedMixedBoundary234.boundary roles).toV7.toV6 (registry value) state root frontier := by
  constructor <;> intro chosen <;> cases chosen with
  | pending h => exact .pending h
  | inspectionPending a b c d => exact .inspectionPending a b c d
  | rejected h => exact .rejected h
  | ambiguous a b c d => exact .ambiguous a b c d
  | selected a b c => exact .selected a b c

theorem v7_local_iff : B4TargetV7.Local (boundary roles).toV7 value state root frontier ↔
    B4TargetV7.Local (GeneralNominalVersionedMixedBoundary234.boundary roles).toV7 (registry value) state root frontier :=
  B4TargetV7.local_transport (b := (boundary roles).toV7)
    (other := (GeneralNominalVersionedMixedBoundary234.boundary roles).toV7)
    (fun _ => v6_local_iff) Iff.rfl Iff.rfl _

theorem local_iff {state : State roles} : Local value state root frontier ↔
    GeneralNominalVersionedMixedBoundary234.Local (registry value) state root frontier :=
  B4TargetV8.local_transport (b := boundary roles)
    (other := GeneralNominalVersionedMixedBoundary234.boundary roles)
    (fun _ => v7_local_iff) Iff.rfl Iff.rfl _

theorem local_total (checked : (boundary roles).Checked value) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local value state root frontier := by
  obtain ⟨frontier,chosen⟩ := GeneralNominalVersionedMixedBoundary234.local_total (checked_compiled checked).2 state root
  exact ⟨frontier,local_iff.mpr chosen⟩

theorem local_functional (one : Local value state root first) (two : Local value state root last) : first = last :=
  B4TargetV8.local_functional one two

theorem evidenceAt_iff :
    B4SkeletonV8.EvidenceAt (boundary roles) value state root ↔
      B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedBoundary234.boundary roles) (registry value) state root := by
  constructor
  · intro held model valid demand key children dictionaries generated stable childStable selected evidence
    exact held model valid demand key children dictionaries generated stable childStable (local_iff.mpr selected) evidence
  · intro held model valid demand key children dictionaries generated stable childStable selected evidence
    exact held model valid demand key children dictionaries generated stable childStable (local_iff.mp selected) evidence

theorem stepModels (step : (boundary roles).Step value root before after)
    (valid : (boundary roles).Models after model) : (boundary roles).Models before model :=
  GeneralNominalVersionedMixedKernel234.step_models step valid

theorem closure (halted : ∀ after, ¬ (boundary roles).Step value root state after) :
    (boundary roles).Stable value state root ∧
    ∀ child, (boundary roles).Generated value state root child → (boundary roles).Stable value state child :=
  GeneralNominalVersionedMixedKernel234.closure halted

theorem initialReorders (order : (boundary roles).Reorders first last)
    (initial : (boundary roles).Initial first root state) : (boundary roles).Initial last root state :=
  GeneralNominalVersionedMixedBoundary234.initialReorders order initial

theorem dictionaryRefl (dictionary : Dictionary) : (boundary roles).DictionaryEquivalent dictionary dictionary := rfl

end Yulang.GeneralNominalVersionedMixedSourceBoundary234
