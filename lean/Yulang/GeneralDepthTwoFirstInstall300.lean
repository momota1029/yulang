import Yulang.GeneralDepthTwoRootFrame300
import Yulang.GeneralDepthTwoSafety300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDepthTwoFirstInstall300
open GeneralGeneratedNestedSource299
open GeneralGeneratedNestedPredictions299
open GeneralDepthTwoRootPlan300 (plan holds emitted_schema emitted_sites child)
open GeneralDepthTwoRootFrame300
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (registry)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalVersionedMixedKernel234 (Step Installable AlternativesSafe)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedInstall232 (install InstallationModels)

abbrev after := install initial effect

theorem administration : GeneralNominalVersionedDiagnostic232.AdministrativeReady initial root := by
  constructor
  · exact ⟨plan.input,List.mem_singleton_self _,rfl⟩
  · intro a one _ b two _
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles)
    compiled initial root := by
  refine ⟨root_known,?_,?_,?_⟩
  · rintro (raw | (⟨i,cyclic⟩ | ⟨site,_,_,i,cyclic⟩))
    · obtain ⟨_,_,_,slot,_,cyclic⟩ := raw
      exact GeneralDepthTwoSafety300.raw_acyclic snapshot rfl snapshot_model slot cyclic
    · exact GeneralDepthTwoSafety300.semantic initial_model _ cyclic
    · exact GeneralDepthTwoSafety300.semantic initial_model _ cyclic
  · rintro (raw | ⟨p,_,entry,_,cyclic⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cyclic⟩ := raw
      exact GeneralDepthTwoSafety300.raw_acyclic snapshot rfl snapshot_model visited.1 cyclic
    · exact GeneralDepthTwoSafety300.semantic initial_model _ cyclic
  · rintro (⟨_,d,visible,role,notFailed,notPrepared⟩ | pending)
    · rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
      · exact notFailed wrong_failed
      · exact notPrepared prepared
    · exact pending administration

theorem positions : GeneralNominalVersionedCycles232.Safe initial plan :=
  ⟨by decide +kernel,fun entry _ => GeneralDepthTwoSafety300.semantic initial_model entry.1⟩

theorem alternatives : AlternativesSafe compiled initial plan.input := by
  intro possible same framed
  have rootFrame : Frame compiled initial.core root possible.packet.declaration.id possible := framed
  have declaration : possible.packet.declaration = display := by
    rcases GeneralRebaseCompiledDisplay277.compiled_members rootFrame.visible rootFrame.role_eq with wrong|right
    · exact False.elim (wrong_not_prepared (wrong ▸ rootFrame.prepared))
    · exact right
  have eq := GeneralRebaseScopedFrame276.same_frame rootFrame frame declaration
    (List.mem_singleton.mp rootFrame.raw_recorded) same
  subst possible
  exact positions

theorem requests (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests after.core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,listed,_,part⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  change site ∈ [GeneralNominalDemandMerging.pointSite root] ++
    GeneralNominalVersionedChildren232.rawSites plan at listed
  rw [GeneralNominalVersionedChildren232.rawSites,emitted_sites] at listed
  simp only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with rfl|rfl
  · cases part
  · have empty : child.observed.occurrence.demand.outputs = [] := by decide +kernel
    rw [empty] at part
    cases part

theorem installation (m : Assignment) (valid : Models initial m) :
    InstallationModels initial effect m := by
  have principles := ((GeneralNominalVersionedJournal232.initial_models ..).mp valid).1
  have planHeld := holds m principles
  refine ⟨valid,planHeld,⟨GeneralNominalVersionedPlans231.head_models planHeld,
    GeneralRebaseDisplayFrame276.classes_empty (initial_requests root) plan m⟩,
    GeneralRebaseDisplayFrame276.classes_empty (requests root) plan m,?_,?_⟩
  all_goals intro _ no; cases no

theorem enabled : Installable compiled initial effect := by
  refine ⟨rfl,rfl,safe,?_,?_,?_,positions,alternatives,model,installation model initial_model⟩
  · exact GeneralNominalVersionedMixedObservations233.legacy_cache
      (GeneralDictionaryDefaultCache208.initial_valid context root)
  · exact congrArg (fun x => x.unknown) emitted_schema
  · intro _ no; cases no

theorem actual : (boundary roles).Step registry root initial after :=
  ⟨root,.root,.install effect enabled (GeneralGeneratedNestedInstallInterface299.first_not_committed rfl)⟩

theorem models (m : Assignment) : Models after m ↔ Models initial m := by
  exact ⟨fun held => GeneralNominalVersionedMixedSourceBoundary234.stepModels actual held,
    fun held => (GeneralNominalVersionedInstall232.install_models (effect := effect) rfl).mpr (installation m held)⟩

theorem actual_middle :
    B4TargetV8.Reachable (boundary roles) registry root after ∧
      GeneralNominalSaturationState.Generated after.core.erased.current root middle :=
  ⟨⟨initial,GeneralGeneratedNestedInitial299.actual_initial,.tail .refl actual⟩,
    GeneralGeneratedNestedInstallInterface299.middle_generated rfl⟩

end Yulang.GeneralDepthTwoFirstInstall300
