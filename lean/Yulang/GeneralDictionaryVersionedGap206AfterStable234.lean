import Yulang.GeneralDictionaryVersionedGap206AfterSelected234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedGap206AfterStable234
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 GeneralDictionaryVersionedGap206Install233
open GeneralDictionaryVersionedGap206Feedback234 (feedback)
open GeneralDictionaryVersionedGap206After234 (currentPlan)
open GeneralDictionaryVersionedGap206AfterSelected234 (raw_sites centers generated_only)
open GeneralNominalVersionedJournal232 GeneralNominalVersionedKernel232
open CommonNominalFullCarrier

theorem raw_to_models (assignment) (valid : GeneralNominalState.Models feedback.core.erased.current.context.state assignment) :
    Models feedback assignment := by
  have before : GeneralNominalState.Models installed.core.erased.current.context.state assignment :=
    ((GeneralNominalState.extend_models ..).mp valid).1
  have sourceModels : GeneralNominalState.Models snapshot assignment :=
    ((GeneralDictionaryOrdinaryTransport.models_extended _ _ _ _ _).mp before).1
  have initialModels : Models current assignment := (lift_models start assignment).mpr
    ((GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr sourceModels)
  have equal : Equivalent (assignment 0).1 (assignment 1).1 :=
    GeneralNominalVersionedEquate234.feedback_equal assignment valid
  have classes : GeneralNominalVersionedEffects231.ClassEffects current.core root plan assignment := by
    apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
    constructor
    · intro output member body found
      cases GeneralDictionaryDefaultGap206State.request_exact member
      have same : body = .default 0 0 (.var 0) := Option.some.inj found.symm
      subst body
      exact (GeneralNominalCenteredHeadMatEffects.positional_default plan assignment (0 : Fin 1)).mpr equal
    · intro first one last two _
      cases GeneralDictionaryDefaultGap206State.request_exact one
      cases GeneralDictionaryDefaultGap206State.request_exact two
      exact ⟨subtype_refl _,subtype_refl _⟩
  apply (GeneralDictionaryVersionedGap206After234.models_iff assignment).mpr
  apply (GeneralNominalVersionedInstall232.install_models rfl).mpr
  refine ⟨initialModels,packet_holds assignment initialModels,
    ⟨GeneralNominalVersionedPlans231.head_models (packet_holds assignment initialModels),classes⟩,?_,?_,?_⟩
  · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun _ => GeneralNominalVersionedTerminal232.requests_iff children_empty)).mpr classes
  · intro prior member; cases member
  · intro prior member; cases member

theorem cut : GeneralNominalCenteredHeadMatStepObservations.Cut feedback.legacy counter := by
  apply GeneralNominalCenteredHeadMatStepObservations.cut_of_recorded
  · exact GeneralDictionaryDefaultGap206Source.counter_model
  · intro site member
    change site ∈ [GeneralNominalCenters.rootSite snapshot.seed root] at member
    cases List.mem_singleton.mp member
    exact GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _
  · intro candidate member; change candidate ∈ [] at member; cases member
  · intro effect member; change effect ∈ [] at member; cases member
  · intro first one last two alias recorded
    rw [centers] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    apply (GeneralNominalDemandMerging.output_atoms_exact ..).mpr
    intro a ha b hb same
    cases List.mem_singleton.mp ha
    cases List.mem_singleton.mp hb
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem no_refresh (context : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh feedback.legacy context)
    (unknown : ¬ GeneralNominalState.Known feedback.core.erased.current.context.state identity)
    (known : GeneralNominalState.Known context.state identity) : False := by
  have one : identity ≠ 1 := by
    intro same; subst identity
    exact unknown ⟨(1 : Fin 3),rfl,Or.inl (by decide +kernel)⟩
  have two : identity ≠ 2 := by
    intro same; subst identity
    exact unknown ⟨(2 : Fin 3),rfl,Or.inl (by decide +kernel)⟩
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have held := GeneralNominalCenteredHeadAllocMergeStable.head_holds head
    (by
      obtain ⟨facts,trusted,sound⟩ := certificate.cache observation (GeneralNominalSupport.head_recorded head)
      exact sound _ (cut facts trusted))
  change test.Holds (counter identity).1 at held
  have bottom : (counter identity).1 = .bottom := by simp [one,two]
  rw [bottom] at held
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head test held

theorem committed : Committed feedback currentPlan := by
  refine ⟨fun assignment valid => ⟨GeneralDictionaryVersionedGap206After234.holds assignment valid,
    GeneralDictionaryVersionedGap206After234.effects assignment valid⟩,?_⟩
  intro child member
  rw [GeneralDictionaryVersionedGap206After234.terminal] at member
  cases member

theorem stable : Stable registry feedback root := by
  intro focus generated next action
  have same := generated_only generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent => exact absent _ (raw_sites ▸ List.mem_singleton_self _) same.symm
    | refresh context certificate identity member unknown known => exact no_refresh context certificate unknown known
    | reobserve revision certificate improved =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision
        (by intro slot descriptor recorded; cases recorded) revision improved
    | equate first last one two equal novel => exact novel (fun assignment valid => equal assignment (raw_to_models assignment valid))
  | refresh focus context certificate identity member unknown known => exact no_refresh context certificate unknown known
  | install candidate enabled novel =>
    have framed := same ▸ enabled.snapshot_eq ▸ enabled.registry_eq ▸ candidate.frame
    have planEq := GeneralDictionaryVersionedGap206AfterSelected234.frame_plan framed
    exact novel (planEq.symm ▸ committed)
  | merge first last one two inputs novel =>
    rw [centers] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact novel (.refl _)

/-- This saturated endpoint is for Kernel232's legacy cache. A mixed-cache
successor may enable a default-derived head refresh and needs a separate check. -/
theorem regression :
    B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) registry root feedback ∧
    Models feedback model ∧ ¬ Models feedback counter ∧ Stable registry feedback root ∧
    GeneralNominalVersionedSourceBoundary232.Local registry feedback root (.selected 37 []) ∧
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles) registry feedback root ∧
    ∀ assignment, Models feedback assignment → GeneralNominalVersionedEvidence231.Evidence registry feedback.core assignment root (.node 37 []) :=
  ⟨GeneralDictionaryVersionedGap206After234.reachable,GeneralDictionaryVersionedGap206After234.model_retained,
    GeneralDictionaryVersionedGap206After234.counter_removed,stable,
    GeneralDictionaryVersionedGap206AfterSelected234.selected,GeneralDictionaryVersionedGap206AfterSelected234.evidenceAt,
    GeneralDictionaryVersionedGap206After234.evidence⟩

end Yulang.GeneralDictionaryVersionedGap206AfterStable234
