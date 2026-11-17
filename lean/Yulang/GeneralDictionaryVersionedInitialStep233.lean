import Yulang.GeneralDictionaryVersionedInitialFrame233
import Yulang.GeneralNominalVersionedSourceBoundary232
import Yulang.GeneralNominalVersionedFrameFunctional232
import Yulang.GeneralDictionaryOptionalEnable229
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedInitialStep233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229 (plan packet model)
open GeneralDictionaryVersionedInitialModel233
open GeneralDictionaryVersionedInitialFrame233
open GeneralNominalVersionedJournal232
open GeneralNominalCenters
open CommonNominalFullCarrier

theorem old_model_initial : Models before model :=
  (lift_models start model).mpr GeneralDictionaryOptionalInstall229.inhabited

theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic before origin :=
  GeneralNominalVersionedAcyclic232.acyclic old_model_initial
    (fun identity => ⟨GeneralDictionaryOptionalStageSafety229.sourceForm identity,
      GeneralDictionaryOptionalStageSafety229.model_form identity⟩) origin

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady before root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one _ last two _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry before root := by
  refine ⟨GeneralDictionaryOptionalInstall229.known,?_,?_,?_⟩
  · rintro (raw | (⟨index,cycle⟩ | ⟨site,_,_,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralDictionaryOptionalEnable229.no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (raw | ⟨candidate,framed,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralDictionaryOptionalEnable229.no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unready)
    · cases List.mem_singleton.mp visible
      exact unprepared prepared
    · exact unready administrative_ready

theorem positions : GeneralNominalVersionedCycles232.Safe before plan :=
  ⟨GeneralDictionaryOptionalEnable229.enabled.positions.1,fun entry _ => acyclic entry.1⟩

theorem alternatives : GeneralNominalVersionedKernel232.AlternativesSafe registry before plan.input := by
  intro candidate same framed
  have equal := GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl rfl rfl framed frame
  subst candidate
  exact positions

theorem installable : GeneralNominalVersionedKernel232.Installable registry before effect := by
  refine ⟨rfl,rfl,safe,GeneralDictionaryDefaultCache208.initial_valid context root,?_,?_,positions,alternatives,
    extended,installation_models⟩
  · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
    rw [GeneralDictionaryVersionedInitialPacket233.emitted_schema]
  · intro prior member; cases member

theorem unassigned_lower : (model (names 0)).1 = .emptyRecord := by
  have high : 4 < names 0 := GeneralNominalAggregateVersion231.above_seed _ _ _ _ _ _
  have distinct : names 0 ≠ GeneralDictionaryOptionalInstall229.lo :=
    GeneralNominalAggregateVersion231.not_legacy_slot _ _ _ _ _ _ _ _ _ _
  simp [GeneralDictionaryOptionalInstall229.model,Nat.not_le.mpr high,distinct]

theorem no_packet : ¬ GeneralNominalVersionedPlans231.Holds plan model := by
  intro valid
  have merges := valid.2.1.1.2.1
  rw [GeneralDictionaryOptionalInstall229.bindings_exact] at merges
  change PresenceNormalForm.All CommonNominalFullCarrier.model model
    ((GeneralNominalAllocation.equations (names 0) (.union (.var 4) (.var 4)) ++ _) ++ _) at merges
  have lower := (PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merges).1 |>.1
  have equal := (GeneralNominalCaptureMerges.equations_exact ..).mp lower
  change Equivalent (model (names 0)).1 (.union GeneralDictionaryOptionalOutput229.value GeneralDictionaryOptionalOutput229.value) at equal
  rw [unassigned_lower] at equal
  exact GeneralDictionaryOptionalOutput229.not_width
    ⟨GeneralDictionaryOptionalOutput229.below_width,
      subtype_trans equal.1 ((common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩)⟩

theorem not_committed : ¬ GeneralNominalVersionedInstallStep232.Committed before plan :=
  fun committed => no_packet (committed.1 model old_model_initial).1

theorem step : GeneralNominalVersionedKernel232.Step registry root before installed :=
  ⟨root,.root,.install effect installable not_committed⟩

/-- A new-only one-step prefix starting from the original source initialization. -/
theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles)
    sourceRegistry root installed :=
  ⟨before,⟨start,GeneralDictionaryOptionalInitial229.initial,rfl⟩,.tail .refl step⟩

end Yulang.GeneralDictionaryVersionedInitialStep233
