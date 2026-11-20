import Yulang.GeneralObservedLadderSafety301
import Yulang.GeneralNominalVersionedMixedEmbedding234
import Yulang.GeneralRebaseScopedFrame276
import Yulang.GeneralRebaseDisplayChildFresh276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralObservedLadderRoot301
open GeneralObservedLadderSource301 (snapshot model_exists)
open GeneralObservedLadderInitial301 (context initial)
open GeneralObservedLadderPlan301
open GeneralObservedLadderSemantics301 (holds)
open GeneralObservedLadderSelection301
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (registry displayRoot intDisplay)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalVersionedMixedKernel234 (Installable AlternativesSafe Committed)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedInstall232 (InstallationModels install installed_child)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalOutputGrowth (finiteModel)
open GeneralSourceDictionaries (Occurrence)

abbrev top (n : Nat) := plan n 0 100 (Nat.zero_le n)
abbrev kid (n : Nat) := child n 0 100 (Nat.zero_le n)
abbrev next (n : Nat) := (kid n).occurrence

theorem frame (n : Nat) : Frame compiled (initial n).core displayRoot 1 (top n) :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,
    List.mem_cons_of_mem _ (List.mem_cons_self ..),rfl,located n 0 100 (by omega),prepared n 0 100 (Nat.zero_le n)⟩

theorem initial_requests (n : Nat) (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests (initial n).core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output h
  obtain ⟨site,listed,_,member⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp h
  change site ∈ [GeneralNominalDemandMerging.pointSite displayRoot] at listed
  cases List.mem_singleton.mp listed
  cases member

theorem ready (n : Nat) :
    GeneralNominalCenteredHeadMatEffects.Ready (initial n).core displayRoot (top n) := by
  intro output shown
  rw [initial_requests] at shown
  cases shown

def effect (n : Nat) : Effect roles :=
  ⟨compiled,(initial n).core,top n,frame n,(one_child n 0 100 (Nat.zero_le n)).symm ▸
    unique n 0 100 (Nat.zero_le n),ready n⟩

abbrev after (n : Nat) := install (initial n) (effect n)

theorem administrative (n : Nat) : GeneralNominalVersionedDiagnostic232.AdministrativeReady (initial n) displayRoot := by
  constructor
  · exact ⟨(top n).input,List.mem_singleton_self _,rfl⟩
  · intro a one _ b two _
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact .refl _

theorem safe (n : Nat) : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles)
    compiled (initial n) displayRoot := by
  have init := GeneralObservedLadderInitial301.models n
  have semantic := GeneralObservedLadderSafety301.semantic n init
  refine ⟨known n 0 100 (by omega),?_,?_,?_⟩
  · rintro (raw | (⟨i,cyclic⟩ | ⟨site,_,_,i,cyclic⟩))
    · obtain ⟨_,_,_,slot,_,cyclic⟩ := raw
      exact GeneralObservedLadderSafety301.raw_acyclic n (snapshot n) rfl (model_exists n) slot cyclic
    · exact semantic _ cyclic
    · exact semantic _ cyclic
  · rintro (raw | ⟨p,_,entry,_,cyclic⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cyclic⟩ := raw
      exact GeneralObservedLadderSafety301.raw_acyclic n (snapshot n) rfl (model_exists n) visited.1 cyclic
    · exact semantic _ cyclic
  · rintro (⟨_,d,visible,role,notFailed,notPrepared⟩ | pending)
    · rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
      · exact notFailed (failed_int n 0 100 (Nat.zero_le n))
      · exact notPrepared (prepared n 0 100 (Nat.zero_le n))
    · exact pending (administrative n)

theorem positions (n : Nat) : GeneralNominalVersionedCycles232.Safe (initial n) (top n) := by
  refine ⟨?_,
    fun e _ => GeneralObservedLadderSafety301.semantic n (GeneralObservedLadderInitial301.models n) e.1⟩
  unfold GeneralNominalCenteredSteps.inspection
  rw [show GeneralNominalInspection.queries (top n).packet.context.state (top n).packet.context.interpretation
    (top n).packet.declaration = _ from GeneralObservedLadderReport301.display_query n]
  have head : (snapshot n).nominals (0 : Fin (n+2)) = some
      (GeneralNominalOutputGrowthModels.descriptor n (GeneralObservedLadderReport301.pos n 0 (by omega)) (Nat.zero_le n)) := by
    exact GeneralObservedLadderSource301.nominal_at n 0 (Nat.zero_le n)
  simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
    GeneralNominalRecursiveInspection.typeArguments,GeneralNominalRecursiveInspection.Report.visit,
    GeneralNominalRecursiveInspection.Report.append,head,GeneralNominalCenters.rootSite,GeneralNominalCenters.Site.observed,List.ofFn_succ,GeneralNominalOutputGrowthModels.descriptor]

theorem alternatives (n : Nat) : AlternativesSafe compiled (initial n) (top n).input := by
  intro possible same framed
  have rootFrame : Frame compiled (initial n).core displayRoot possible.packet.declaration.id possible := framed
  have declaration : possible.packet.declaration = display := by
    rcases GeneralRebaseCompiledDisplay277.compiled_members rootFrame.visible rootFrame.role_eq with wrong|right
    · exact False.elim (int_not_prepared n 0 100 (Nat.zero_le n) (wrong ▸ rootFrame.prepared))
    · exact right
  have eq := GeneralRebaseScopedFrame276.same_frame rootFrame (frame n) declaration
    (List.mem_singleton.mp rootFrame.raw_recorded) same
  subst possible
  exact positions n

theorem requests (n : Nat) (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests (after n).core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,listed,_,part⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  change site ∈ [GeneralNominalDemandMerging.pointSite displayRoot] ++
    GeneralNominalVersionedChildren232.rawSites (top n) at listed
  rw [GeneralNominalVersionedChildren232.rawSites,emitted_sites] at listed
  simp only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with rfl|rfl
  · cases part
  · rw [show (kid n).observed.occurrence.demand.outputs = [] from rfl] at part
    cases part

theorem installation (n : Nat) (m : Assignment) (valid : Models (initial n) m) :
    InstallationModels (initial n) (effect n) m := by
  have principles := ((GeneralNominalVersionedJournal232.initial_models ..).mp valid).1
  have held := holds n 0 100 (Nat.zero_le n) m principles
  refine ⟨valid,held,⟨GeneralNominalVersionedPlans231.head_models held,
    GeneralRebaseDisplayFrame276.classes_empty (initial_requests n displayRoot) (top n) m⟩,
    GeneralRebaseDisplayFrame276.classes_empty (requests n displayRoot) (top n) m,?_,?_⟩
  all_goals intro _ no; cases no

theorem enabled (n : Nat) : Installable compiled (initial n) (effect n) := by
  refine ⟨rfl,rfl,safe n,?_,?_,?_,positions n,alternatives n,finiteModel n,
    installation n _ (GeneralObservedLadderInitial301.models n)⟩
  · exact GeneralNominalVersionedMixedObservations233.legacy_cache
      (GeneralDictionaryDefaultCache208.initial_valid (context n) displayRoot)
  · exact congrArg (fun x => x.unknown) (emitted_schema n 0 100 (Nat.zero_le n))
  · intro _ no; cases no

theorem not_committed (n : Nat) : ¬ Committed (initial n) (top n) := by
  intro yes
  have first := yes.2 (next n) ((one_child n 0 100 (Nat.zero_le n)).symm ▸ List.mem_singleton_self _)
  cases first

theorem actual (n : Nat) : (boundary roles).Step registry displayRoot (initial n) (after n) :=
  ⟨displayRoot,.root,.install (effect n) (enabled n) (not_committed n)⟩

theorem models (n : Nat) (m : Assignment) : Models (after n) m ↔ Models (initial n) m :=
  ⟨fun valid => GeneralNominalVersionedMixedSourceBoundary234.stepModels (actual n) valid,
    fun valid => (GeneralNominalVersionedInstall232.install_models (effect := effect n) rfl).mpr (installation n m valid)⟩

theorem generated (n : Nat) :
    B4TargetV8.Reachable (boundary roles) registry displayRoot (after n) ∧
      GeneralNominalSaturationState.Generated (after n).core.erased.current displayRoot (next n) := by
  refine ⟨⟨initial n,GeneralObservedLadderInitial301.actual_initial n,.tail .refl (actual n)⟩,.child .root ?_⟩
  exact installed_child (state := initial n) (effect := effect n)
    ((one_child n 0 100 (Nat.zero_le n)).symm ▸ List.mem_singleton_self _)

end Yulang.GeneralObservedLadderRoot301
