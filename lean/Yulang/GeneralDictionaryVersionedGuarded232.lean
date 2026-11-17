import Yulang.GeneralNominalVersionedKernel232
import Yulang.GeneralDictionaryVersionedStep232
import Yulang.GeneralNominalVersionedAcyclic232
import Yulang.GeneralNominalVersionedFrameFunctional232
import Yulang.GeneralDictionaryOptionalStageSafety229
import Yulang.GeneralDictionaryDefaultCache208
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! The concrete migration installation satisfies every guard of the versioned
kernel, not only the smaller install relation. This is one guarded transition,
not global termination, a twelve-law boundary, or a new EvidenceNode theorem. -/
namespace Yulang.GeneralDictionaryVersionedGuarded232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229 (model)
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedInstalled232
open GeneralNominalVersionedJournal232
open GeneralNominalCenters

 theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic before origin :=
  GeneralNominalVersionedAcyclic232.acyclic
    ((lift_models after model).mpr GeneralDictionaryUpper230Step.inhabited)
    (fun identity => ⟨GeneralDictionaryOptionalStageSafety229.sourceForm identity,
      GeneralDictionaryOptionalStageSafety229.model_form identity⟩) origin

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady before root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one _ last two _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry before root := by
  refine ⟨GeneralDictionaryUpper230Safety.known,?_,?_,?_⟩
  · rintro (raw | (⟨index,cycle⟩ | ⟨site,_,_,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralDictionaryUpper230Safety.no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (raw | ⟨plan,frame,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralDictionaryUpper230Safety.no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unready)
    · cases List.mem_singleton.mp visible
      exact unprepared GeneralDictionaryVersionedPrepared231.prepared
    · exact unready administrative_ready

theorem cache : GeneralNominalCenteredHeadMatStepObservations.CacheSound before.legacy
    before.core.erased.current.context.state :=
  GeneralDictionaryDefaultCache208.steps_cache
    (.tail GeneralDictionaryOptionalReachable229.path GeneralDictionaryUpper230Step.step)
    (GeneralDictionaryDefaultCache208.initial_valid context root)

theorem positions : GeneralNominalVersionedCycles232.Safe before currentPlan :=
by
  constructor
  · unfold GeneralNominalCenteredSteps.inspection
    change (GeneralNominalRecursiveInspection.inspectMany _
      (GeneralNominalInspection.queries GeneralDictionaryUpper230Current.currentContext.state interpretation declaration)
      _ _ _).inspected.length = _
    rw [GeneralDictionaryUpper230Current.query]
    simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
      GeneralNominalRecursiveInspection.typeArguments,GeneralNominalRecursiveInspection.Report.append,
      GeneralNominalRecursiveInspection.Report.visit,GeneralDictionaryUpper230Snapshot.pointDesc,
      Site.observed,rootSite,root,GeneralDictionaryJournalRefinement228Source.roles]
    simp only [GeneralNominalRefinements.renameDescriptor]
    change (GeneralNominalRecursiveInspection.inspectMany GeneralDictionaryUpper230Snapshot.extendedSnapshot
      [.variables [0],.variables [0]] [((2 : Fin 6),2),(2,2)]
      (fun index => some ((GeneralNominalRecursiveInspection.Origin.source 0).nominal 0 index)) 0).inspected.length =
      (GeneralNominalRecursiveInspection.inspectMany GeneralDictionaryUpper230Snapshot.extendedSnapshot
      [.variables [0],.variables [0]] [((2 : Fin 6),2),(2,2)]
      (fun index => some ((GeneralNominalRecursiveInspection.Origin.source 0).nominal 0 index)) 0).tests.length
    simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
      GeneralNominalRecursiveInspection.Report.append]

  · exact fun entry _ => acyclic entry.1

theorem frame_plan (frame : GeneralNominalVersionedEvidence231.Frame registry before.core root key plan) :
    plan = currentPlan :=
  GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl rfl rfl frame
    GeneralDictionaryVersionedEvidence231.frame

theorem alternatives : GeneralNominalVersionedKernel232.AlternativesSafe registry before currentPlan.input := by
  intro plan same frame
  have samePlan := frame_plan frame
  subst plan
  exact positions

theorem choice : GeneralNominalCycleSteps.ChoiceCompatible before.core.erased.current currentPacket := by
  intro prior member _
  cases List.mem_singleton.mp member
  rfl

theorem installable : GeneralNominalVersionedKernel232.Installable registry before effect := by
  refine ⟨rfl,rfl,safe,cache,?_,choice,positions,alternatives,?_⟩
  · change (GeneralNominalVersionedPlans231.emittedSchema currentPlan).unknown = false
    rw [GeneralDictionaryVersionedPacket231.emitted_schema]
  · obtain ⟨m,valid⟩ := GeneralDictionaryVersionedCompletion231.inhabited
    exact ⟨m,installation_models valid⟩

theorem step : GeneralNominalVersionedKernel232.Step registry root before installed :=
  ⟨root,.root,.install effect installable GeneralDictionaryVersionedNovel232.not_committed⟩

end Yulang.GeneralDictionaryVersionedGuarded232
