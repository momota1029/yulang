import Yulang.GeneralDictionaryHeadSharingBoundary220
import Yulang.GeneralDictionaryDefaultAvailability208
import Yulang.GeneralDictionaryCurrentHeadEquations217

set_option backward.isDefEq.respectTransparency false
/-! V8 selection removes the all-frame sharing obstruction, but it does not
assert agreement for every journal model or simultaneous packet/effect models. -/
namespace Yulang.GeneralDictionaryHeadSharingWitness220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal (State Models)
open GeneralDictionaryHeadSharingBoundary220 (boundary Local)
open GeneralDictionaryHeadSharingConflict220 (Feasible)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem feasible_not_conflict
    (unique : B4TargetV7.Unique (GeneralDictionaryDefaultBoundary208.boundary roles) value state focus key children)
    (good : Feasible (registry value) state focus key) :
    ¬ GeneralDictionaryHeadSharingConflict220.Conflict value state focus := by
  rintro ⟨other,kids,only,bad⟩
  have same := (unique.2 other kids only.1).1
  subst other
  exact bad.2.2 good

theorem selected_of_feasible
    (old : GeneralDictionaryDefaultBoundary208.Local value state focus (.selected key children))
    (good : Feasible (registry value) state focus key) : Local value state focus (.selected key children) := by
  have unique : B4TargetV7.Unique (GeneralDictionaryDefaultBoundary208.boundary roles) value state focus key children := by
    have prior := (B4TargetV7.selected_iff.mp old).1
    cases prior with
    | selected _ unique _ => exact unique
  exact .ordinary (feasible_not_conflict unique good) old

theorem selected_feasible
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (inhabited : ∃ model, Models state model) : Feasible (registry value) state focus key := by
  obtain ⟨old,clear⟩ := GeneralDictionaryHeadSharingBoundary220.selected_iff.mp selected
  obtain ⟨plan,frame,_⟩ := GeneralDictionaryDefaultAvailability208.selected_frame reachable old
  have unique : B4TargetV7.Unique (GeneralDictionaryDefaultBoundary208.boundary roles) value state focus key children := by
    have prior := (B4TargetV7.selected_iff.mp old).1
    cases prior with
    | selected _ unique _ => exact unique
  exact GeneralDictionaryHeadSharingConflict220.no_conflict_feasible unique inhabited ⟨plan,frame⟩ clear

theorem selected_agreement
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (inhabited : ∃ model, Models state model) :
    ∃ model, Models state model ∧ ∃ plan,
      GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan ∧
        GeneralDictionaryCountedProjection216.Agreement plan model := by
  obtain ⟨model,valid,plan,frame,held⟩ := selected_feasible reachable selected inhabited
  exact ⟨model,valid,plan,frame,GeneralDictionaryHeadSharing220.agreement_of_holds plan model held⟩

/-- A recorded packet has sharing in every current journal model. -/
theorem recorded_sharing (plan : Plan roles) (recorded : plan ∈ state.core.plans)
    (valid : Models state model) : GeneralDictionaryHeadSharing220.Holds plan model :=
  GeneralDictionaryHeadSharing220.packet_holds plan model (valid.2.2.2.2.1 plan recorded)

/-- A compatible current head is enough for the new guard, with no effect assumption. -/
theorem head_feasible (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame r state.core focus key plan)
    (valid : Models state model) (head : GeneralNominalCenteredHeadOutputs.HeadEquations plan model) :
    Feasible r state focus key :=
  ⟨model,valid,plan,frame,GeneralDictionaryHeadSharing220.head_holds plan model head⟩

/-- Sharing rejection rules out a same-key certificate in every current model. -/
theorem atKey_no_certificate
    (bad : GeneralDictionaryHeadSharingConflict220.AtKey r state focus key)
    (valid : Models state model)
    (certificate : GeneralDictionaryTotalEvidence206.Certificate r state.core model focus key children plan) : False :=
  bad.2.2 ⟨model,valid,plan,certificate.frame,
    GeneralDictionaryHeadSharing220.packet_holds plan model certificate.packet⟩

theorem atKey_no_instance
    (bad : GeneralDictionaryHeadSharingConflict220.AtKey r state focus key)
    (valid : Models state model) :
    ¬ GeneralDictionaryTotalEvidence206.Instance r state.core model focus key children := by
  rintro ⟨plan,certificate⟩
  exact atKey_no_certificate bad valid certificate

end Yulang.GeneralDictionaryHeadSharingWitness220
