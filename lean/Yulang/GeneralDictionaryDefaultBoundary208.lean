import Yulang.GeneralDictionaryDefaultKernel208
import Yulang.GeneralDictionaryTotalBoundary206

namespace Yulang.GeneralDictionaryDefaultBoundary208
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls}

abbrev Step (value : Registry) := GeneralDictionaryDefaultKernel208.Step (registry value) (roles := roles)
abbrev Stable (value : Registry) := GeneralDictionaryDefaultKernel208.Stable (registry value) (roles := roles)

def boundary (roles : Roles.RoleDecls) :
    B4TargetV7.SourceBoundary (GeneralNominalCenteredHeadMatStepLocal.vocabulary roles) :=
  { GeneralDictionaryTotalBoundary206.boundary roles with Step := Step, Stable := Stable }

abbrev Local (value : Registry) (state : State roles) := B4TargetV7.Local (boundary roles) value state

theorem ordinary_iff : B4TargetV6.Local (boundary roles).toV6 r s d f ↔
    B4TargetV6.Local (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).toV6 r s d f := by
  constructor <;> intro h <;> cases h with
  | pending h => exact .pending h
  | inspectionPending a b c d => exact .inspectionPending a b c d
  | rejected h => exact .rejected h
  | ambiguous a b c d => exact .ambiguous a b c d
  | selected a b c => exact .selected a b c

theorem local_iff : Local r s d f ↔ GeneralNominalCenteredHeadAllocV7Boundary.Local r s d f :=
  B4TargetV7.local_transport (fun _ => ordinary_iff) Iff.rfl Iff.rfl _

theorem local_eq : Local (roles := roles) r s = GeneralNominalCenteredHeadAllocV7Boundary.Local r s := by
  funext d f
  exact propext local_iff

theorem local_total (checked : (boundary roles).Checked r) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local r state root frontier := by
  obtain ⟨frontier,valid⟩ := GeneralNominalCenteredHeadAllocV7Boundary.local_total checked state root
  exact ⟨frontier,local_iff.mpr valid⟩

theorem whereAccessible (r : Registry) (state : State roles) (root : Occurrence roles) :
    Acc (Child (Local r state)) root := by
  rw [local_eq]
  exact GeneralNominalCenteredHeadAllocV7Boundary.whereAccessible r state root

theorem stepModels (step : Step r root before after) (valid : (boundary roles).Models after model) :
    (boundary roles).Models before model := GeneralDictionaryDefaultKernel208.stepModels step valid

theorem closure (halted : ∀ after, ¬ Step r root state after) :
    Stable r state root ∧ ∀ child, (boundary roles).Generated r state root child → Stable r state child :=
  GeneralDictionaryDefaultKernel208.closure halted

theorem initialReorders (order : (boundary roles).Reorders first last)
    (initial : (boundary roles).Initial first root state) : (boundary roles).Initial last root state :=
  GeneralNominalCenteredHeadAllocV7Boundary.initialReorders order initial

theorem dictionaryRefl (dictionary : Dictionary) : (boundary roles).DictionaryEquivalent dictionary dictionary := rfl

theorem old_step (step : GeneralNominalCenteredHeadAllocV7Boundary.Step r root before after) :
    Step r root before after :=
  ⟨step.choose,step.choose_spec.1,GeneralDictionaryDefaultKernel208.old_at step.choose_spec.2⟩

theorem old_steps (path : B4Target.Steps (GeneralNominalCenteredHeadAllocV7Boundary.Step r root) before after) :
    B4Target.Steps (Step r root) before after := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact .tail ih (old_step step)

theorem old_reachable (reachable : B4TargetV7.Reachable (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles) r root state) :
    B4TargetV7.Reachable (boundary roles) r root state := by
  obtain ⟨start,initial,path⟩ := reachable
  exact ⟨start,initial,old_steps path⟩

/-- Reachability is only transported in this direction. The repaired step is larger. -/
theorem stable_old (stable : Stable r state root) :
    GeneralNominalCenteredHeadAllocV7Boundary.Stable r state root :=
  GeneralDictionaryDefaultKernel208.stable_old stable

end Yulang.GeneralDictionaryDefaultBoundary208
