import Yulang.GeneralDictionaryDefaultAvailability208
import Yulang.GeneralDictionaryDefaultSimulation208

namespace Yulang.GeneralDictionaryDefaultRecorded208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralDictionaryDefaultSimulation208 (Recorded)
variable {roles : Roles.RoleDecls} {state : State roles}

/-- Every installed plan retains its live effect, including after alias merges. -/
theorem recorded (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    Recorded state := by
  obtain ⟨start,initial,path⟩ := reachable
  have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
  induction path with
  | refl =>
      constructor
      · intro plan member
        cases member
      · intro plan member
        cases member
  | tail path step ih => exact GeneralDictionaryDefaultSimulation208.recorded_at ih step.choose_spec.2

theorem committed (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (member : plan ∈ state.core.plans) :
    GeneralDictionaryDefaultKernel208.Committed state plan :=
  GeneralDictionaryDefaultSimulation208.full_committed (recorded reachable) member

/-- Stored parents already enforce the whole current class, not only the
outputs present when their child edges were recorded. -/
theorem current_class (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (member : plan ∈ state.core.plans) (valid : Models state model) :
    GeneralNominalCenteredHeadMatEffects.ClassEffects state.core plan.packet.site.occurrence plan model :=
  GeneralDictionaryDefaultKernel208.committed_class (committed reachable member) valid

theorem certificate (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan)
    (member : plan ∈ state.core.plans) (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key plan.packet.children plan :=
  GeneralDictionaryDefaultCommitment208.certificate frame (committed reachable member)
    (GeneralDictionaryDefaultAvailability208.ready checked reachable frame) valid

/-- Model-relative assembly from an actual stored plan. No inhabitation or
fresh-install choice premise is needed on this already-installed branch. -/
theorem evidence_node (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan)
    (member : plan ∈ state.core.plans) (valid : Models state model)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model)
      plan.packet.children dictionaries) :
    GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model focus (.node key dictionaries) :=
  GeneralDictionaryTotalEvidence206.evidence_node ⟨plan,certificate checked reachable frame member valid⟩ given

end Yulang.GeneralDictionaryDefaultRecorded208
