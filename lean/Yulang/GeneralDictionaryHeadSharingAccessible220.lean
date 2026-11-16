import Yulang.GeneralDictionaryHeadSharingPrecision220
import Yulang.GeneralDictionaryHeadSharingWitness220

/-! Reachable nonrepeating-head conservativity. The ordinary source and trace
premises are obtained from reachability; model existence is required only for
an existential feasible witness, not for absence of the sharing diagnostic. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryHeadSharingAccessible220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal (State Models)
open GeneralNominalCenteredHeadOutputs (Frame)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralDictionaryHeadSharingPrecision220 (NoDistinctSameName)
open GeneralDictionaryHeadSharingConflict220 (Feasible Conflict)
open GeneralDictionaryHeadSharingBoundary220 (boundary Local)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem holds_of_reachable_frame
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (candidate : Plan roles) (frame : Frame (registry value) state.core focus key candidate)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (distinct : NoDistinctSameName candidate) : GeneralDictionaryHeadSharing220.Holds candidate model := by
  obtain ⟨start,initial,path⟩ := reachable
  have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
  exact GeneralDictionaryHeadSharingPrecision220.holds_of_no_distinct_same_name
    source point ground coverage path candidate frame model valid distinct

theorem feasible_of_reachable_frame
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (candidate : Plan roles) (frame : Frame (registry value) state.core focus key candidate)
    (distinct : NoDistinctSameName candidate) (inhabited : ∃ model, Models state model) :
    Feasible (registry value) state focus key := by
  obtain ⟨model,valid⟩ := inhabited
  exact ⟨model,valid,candidate,frame,holds_of_reachable_frame reachable candidate frame model valid distinct⟩

/-- An empty journal is not an obstacle to this no-conflict theorem: Conflict
itself contains a current model. Unique refers to the unchanged V7 survivors. -/
theorem no_conflict_of_reachable_frame
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (unique : B4TargetV7.Unique (GeneralDictionaryDefaultBoundary208.boundary roles)
      value state focus key children)
    (candidate : Plan roles) (frame : Frame (registry value) state.core focus key candidate)
    (distinct : NoDistinctSameName candidate) : ¬ Conflict value state focus := by
  rintro ⟨other,kids,only,_safe,bad⟩
  have same := (unique.2 other kids only.1).1
  subst other
  exact bad.2.2 (feasible_of_reachable_frame reachable candidate frame distinct bad.1)

theorem selected_of_reachable_frame
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (old : GeneralDictionaryDefaultBoundary208.Local value state focus (.selected key children))
    (candidate : Plan roles) (frame : Frame (registry value) state.core focus key candidate)
    (distinct : NoDistinctSameName candidate) : Local value state focus (.selected key children) := by
  have unique : B4TargetV7.Unique (GeneralDictionaryDefaultBoundary208.boundary roles)
      value state focus key children := by
    have prior := (B4TargetV7.selected_iff.mp old).1
    cases prior with
    | selected _ unique _ => exact unique
  exact .ordinary (no_conflict_of_reachable_frame reachable unique candidate frame distinct) old

theorem selected_iff_prior_of_reachable_frame
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (candidate : Plan roles) (frame : Frame (registry value) state.core focus key candidate)
    (distinct : NoDistinctSameName candidate) :
    Local value state focus (.selected key children) ↔
      GeneralDictionaryDefaultBoundary208.Local value state focus (.selected key children) :=
  ⟨fun selected => (GeneralDictionaryHeadSharingBoundary220.selected_iff.mp selected).1,
    fun old => selected_of_reachable_frame reachable old candidate frame distinct⟩

theorem feasible_of_nodup_names
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (candidate : Plan roles) (frame : Frame (registry value) state.core focus key candidate)
    (distinct : (candidate.headSchema.variables.map GeneralNominalMaterialization.Use.name).Nodup)
    (inhabited : ∃ model, Models state model) : Feasible (registry value) state focus key :=
  feasible_of_reachable_frame reachable candidate frame
    (GeneralDictionaryHeadSharingPrecision220.no_distinct_same_name_of_nodup candidate distinct) inhabited

theorem no_conflict_of_nodup_names
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (unique : B4TargetV7.Unique (GeneralDictionaryDefaultBoundary208.boundary roles)
      value state focus key children)
    (candidate : Plan roles) (frame : Frame (registry value) state.core focus key candidate)
    (distinct : (candidate.headSchema.variables.map GeneralNominalMaterialization.Use.name).Nodup) :
    ¬ Conflict value state focus :=
  no_conflict_of_reachable_frame reachable unique candidate frame
    (GeneralDictionaryHeadSharingPrecision220.no_distinct_same_name_of_nodup candidate distinct)

theorem selected_iff_prior_of_nodup_names
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (candidate : Plan roles) (frame : Frame (registry value) state.core focus key candidate)
    (distinct : (candidate.headSchema.variables.map GeneralNominalMaterialization.Use.name).Nodup) :
    Local value state focus (.selected key children) ↔
      GeneralDictionaryDefaultBoundary208.Local value state focus (.selected key children) :=
  selected_iff_prior_of_reachable_frame reachable candidate frame
    (GeneralDictionaryHeadSharingPrecision220.no_distinct_same_name_of_nodup candidate distinct)

end Yulang.GeneralDictionaryHeadSharingAccessible220
