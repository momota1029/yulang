import Yulang.GeneralNominalVersionedMixedKernel234
import Yulang.GeneralNominalCenteredHeadMatStepBoundary
set_option backward.isDefEq.respectTransparency false
/-! Concrete guarded V8 boundary with the versioned journal, not a theorem
assuming its desired laws. Only the individual laws proved below are claimed.
The full twelve bridges, termination, general EvidenceNode and regression
coverage remain open; cache eligibility uses independently trusted legacy/versioned slices. -/
namespace Yulang.GeneralNominalVersionedMixedBoundary234
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open CommonRoleOutermostResolver

def Initial (registry : Registry) (root : Occurrence roles) (state : State roles) : Prop :=
  ∃ legacy, GeneralNominalCenteredHeadMatStepBoundary.Initial registry root legacy ∧ state = lift legacy

def boundary (roles : Roles.RoleDecls) :
    B4TargetV8.SourceBoundary (GeneralNominalVersionedDiagnostic232.vocabulary roles) :=
  { GeneralNominalVersionedDiagnostic232.boundary roles with
    Step := GeneralNominalVersionedMixedKernel234.Step
    Stable := GeneralNominalVersionedMixedKernel234.Stable
    Initial := Initial }

abbrev Local (registry : Registry) (state : State roles) := B4TargetV8.Local (boundary roles) registry state

variable {roles : Roles.RoleDecls} {state : State roles} {root : Occurrence roles}

theorem v6_local_iff : B4TargetV6.Local (boundary roles).toV7.toV6 registry state root frontier ↔
    B4TargetV6.Local (GeneralNominalVersionedDiagnostic232.v6 roles) registry state root frontier := by
  constructor <;> intro chosen <;> cases chosen with
  | pending h => exact .pending h
  | inspectionPending a b c d => exact .inspectionPending a b c d
  | rejected h => exact .rejected h
  | ambiguous a b c d => exact .ambiguous a b c d
  | selected a b c => exact .selected a b c

theorem v7_local_iff : B4TargetV7.Local (boundary roles).toV7 registry state root frontier ↔
    B4TargetV7.Local (GeneralNominalVersionedDiagnostic232.v7 roles) registry state root frontier :=
  B4TargetV7.local_transport (b := (boundary roles).toV7)
    (other := GeneralNominalVersionedDiagnostic232.v7 roles) (fun _ => v6_local_iff) Iff.rfl Iff.rfl _

theorem local_iff : Local registry state root frontier ↔
    GeneralNominalVersionedDiagnostic232.Local registry state root frontier :=
  B4TargetV8.local_transport (b := boundary roles)
    (other := GeneralNominalVersionedDiagnostic232.boundary roles) (fun _ => v7_local_iff) Iff.rfl Iff.rfl _

theorem local_total (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier := by
  obtain ⟨frontier,chosen⟩ := GeneralNominalVersionedDiagnostic232.local_total checked state root
  exact ⟨frontier,local_iff.mpr chosen⟩

theorem local_functional (one : Local registry state root first) (two : Local registry state root last) : first = last :=
  B4TargetV8.local_functional one two

theorem stepModels (step : (boundary roles).Step registry root before after)
    (valid : (boundary roles).Models after model) : (boundary roles).Models before model :=
  GeneralNominalVersionedMixedKernel234.step_models step valid

theorem closure (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
    ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child :=
  GeneralNominalVersionedMixedKernel234.closure halted

theorem initialReorders (order : (boundary roles).Reorders first last)
    (initial : (boundary roles).Initial first root state) : (boundary roles).Initial last root state := by
  obtain ⟨legacy,initial,same⟩ := initial
  exact ⟨legacy,GeneralNominalCenteredHeadMatStepBoundary.initialReorders order initial,same⟩

theorem dictionaryRefl (dictionary : Dictionary) : (boundary roles).DictionaryEquivalent dictionary dictionary := rfl

theorem source_initial {legacy : Legacy.State roles} {root : Occurrence roles} (source : GeneralNominalCenteredHeadMatStepBoundary.Initial registry root legacy) :
    (boundary roles).Initial registry root (lift legacy) := ⟨legacy,source,rfl⟩

end Yulang.GeneralNominalVersionedMixedBoundary234
