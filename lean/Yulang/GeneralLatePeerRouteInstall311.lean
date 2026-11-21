import Yulang.GeneralLatePeerRoutePlan311
import Yulang.GeneralVersionedReplayComposition310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 17500000
namespace Yulang.GeneralLatePeerRouteInstall311
open GeneralLatePeerSource311 (root registry compiled checked initial initial_source route)
open GeneralLatePeerRoot311 (direct branch route_args)
open GeneralLatePeerFirst311 (after centers raw generated_branch)
open GeneralLatePeerDirectInstall311 (recorded reached_recorded model_now centers_same alias_empty)
open GeneralLatePeerRoutePlan311 (middlePacket middle_report child middle_children)
open GeneralLatePeerFresh311 (Pool branch_different distinct_child)
open GeneralNominalVersionedTransport231 (extendedPlan extendedPacket)
open GeneralNominalVersionedInstallation231 (reserved atoms allocated)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedMixedKernel234 (Step Committed)
open GeneralNominalVersionedInstall232 (install install_models)
open GeneralNominalCenters (Plan)
open GeneralGeneratedNestedSource299 (snapshot context model listDescriptor)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState (Generated)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)

abbrev rp := GeneralLatePeerRoot311.packet
abbrev dp := GeneralLatePeerDirectPlan311.packet
abbrev rs := reserved rp ++ reserved dp
abbrev ats := atoms rp ++ atoms dp
abbrev owned := allocated rp ++ allocated dp
abbrev ctx := recorded.core.erased.current.context
abbrev old := GeneralLatePeerRoutePlan311.plan
abbrev partially := extendedPlan (reserved rp) (atoms rp) (allocated rp) old
abbrev plan := extendedPlan (reserved dp) (atoms dp) (allocated dp) partially

theorem plan_flat : plan = extendedPlan rs ats owned old :=
  GeneralVersionedReplayComposition310.compose _ _ _ _ _ _ _
abbrev packet := plan.packet

theorem context_exact : ctx = GeneralDictionaryOrdinaryTransport.extend context rs ats owned :=
  GeneralVersionedReplayComposition310.context _ _ _ _ _ _ _

theorem ctx_packet : packet.context = ctx := rfl

theorem added (m : Assignment) (valid : Models recorded m) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m ats := by
  have current := valid.1.1
  change GeneralNominalState.Models ctx.state m at current
  rw [context_exact] at current
  exact ((GeneralDictionaryOrdinaryTransport.models_extended ..).mp current).2

theorem holds (m : Assignment) (valid : Models recorded m) : GeneralNominalVersionedPlans231.Holds plan m :=
  plan_flat.symm ▸ (GeneralNominalVersionedTransport231.holds_iff rs ats owned old m).mpr
    ⟨GeneralLatePeerRoutePlan311.holds m ((GeneralLatePeerFirst311.models m).mp
      ((GeneralLatePeerDirectInstall311.models m).mp valid).1).1.1,added m valid⟩

theorem pool : Pool ctx.state [direct.occurrence.identity,root.identity] := by
  apply GeneralLatePeerFresh311.extend_pool after.core.erased.current.context dp rfl GeneralLatePeerFresh311.before
  have bound : ∀ n ∈ (atoms dp).flatMap GeneralNominalState.atomSources, n ≤ 2 := by
    unfold atoms
    rw [GeneralLatePeerDirectPlan311.bindings_empty,GeneralLatePeerDirectPlan311.report]
    decide +kernel
  exact fun atom listed n hit => bound n (List.mem_flatMap.mpr ⟨atom,listed,hit⟩)

abbrev one : Fin ctx.state.base.slots := (1 : Fin 3)

theorem located : GeneralNominalRecursiveCandidates.arguments ctx (inputs branch.occurrence) =
    some [(one,one)] := by decide +kernel

theorem known : GeneralLatePeerGuard311.Known recorded branch.occurrence := by
  rintro ⟨i,unknown⟩
  exact unknown ⟨(1 : Fin 3),(congrArg Prod.fst (route_args i)).symm,Or.inr ⟨listDescriptor 2,rfl⟩⟩

theorem linked : GeneralNominalState.Linked ctx.state (inputs branch.occurrence).demand := by
  refine ⟨?_,?_⟩
  · intro i
    change (branch.occurrence.demand.arguments i).1 ∈ GeneralNominalState.sources ctx.state ∧
      (branch.occurrence.demand.arguments i).2 ∈ GeneralNominalState.sources ctx.state
    rw [route_args]
    exact ⟨GeneralNominalAllocationSupport.slot_source ctx.state (1 : Fin 3),
      GeneralNominalAllocationSupport.slot_source ctx.state (1 : Fin 3)⟩
  · intro _ absent; cases absent

theorem prepared : Prepared compiled ctx branch.occurrence route := by
  refine ⟨⟨rfl,initial_source.metadata.2⟩,linked,[(one,one)],located,?_,?_,model,?_⟩
  · exact GeneralLatePeerFresh311.fresh pool compiled branch.occurrence.identity (by
      intro h
      rcases List.mem_cons.mp h with same|last
      · exact distinct_child same
      · exact branch_different (List.mem_singleton.mp last)) _
  · have exactOrig : GeneralNominalRecursiveInspection.Finished
        (GeneralNominalRecursiveCandidates.report context route [(1,1)]) := by
      rw [middle_report]; exact ⟨rfl,rfl,rfl⟩
    exact (GeneralNominalVersionedPreparedTransport231.finished_iff _ _ _ _ _ _).mpr
      ((GeneralNominalVersionedPreparedTransport231.finished_iff _ _ _ _ _ _).mpr exactOrig)
  · exact (GeneralNominalVersionedCandidates231.headModels_packet_iff packet model).mpr
      (GeneralNominalVersionedPlans231.head_models (plan := plan) (holds model model_now))

theorem raw_same : recorded.core.erased.current.sites = after.core.erased.current.sites := by
  change after.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites GeneralLatePeerDirectPlan311.plan = _
  have n : (GeneralNominalVersionedChildren232.rawSites GeneralLatePeerDirectPlan311.plan).length = 0 := by
    unfold GeneralNominalVersionedChildren232.rawSites
    rw [List.length_map,GeneralNominalVersionedChildren232.emitted_length]
    rfl
  rw [List.length_eq_zero_iff.mp n,List.append_nil]

theorem frame : Frame compiled recorded.core branch.occurrence 3 plan :=
  ⟨rfl,ctx_packet,rfl,rfl,raw_same ▸ raw ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    centers_same ▸ centers ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),rfl,
    located,prepared⟩

theorem admin : GeneralNominalVersionedDiagnostic232.AdministrativeReady recorded branch.occurrence := by
  refine ⟨⟨branch,frame.center_recorded,rfl⟩,?_⟩
  intro a one occ b two same
  rw [centers_same,centers] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl|rfl|rfl
  · exact False.elim (branch_different (congrArg Occurrence.identity occ).symm)
  · exact False.elim (distinct_child (congrArg Occurrence.identity occ).symm)
  · rcases two with rfl|rfl|rfl
    · cases same.1
    · cases same.1
    · exact .refl _

theorem class_requests : GeneralNominalCenteredHeadOutputs.requests recorded.core branch.occurrence = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro o present
  obtain ⟨site,mem,alias,inside⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp present
  rw [raw_same,raw] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl
  · cases inside
  · have all : ∀ {a b : Nat}, GeneralNominalSaturationState.Alias recorded.core.erased.current a b → a = b := by
      intro a b relation
      induction relation with
      | refl => rfl
      | edge impossible => cases impossible
      | symm _ ih => exact ih.symm
      | trans _ _ a b => exact a.trans b
    exact distinct_child (all alias)
  · cases inside

theorem classes (m : Assignment) : GeneralNominalVersionedEffects231.ClassEffects recorded.core branch.occurrence plan m :=
  GeneralRebaseDisplayFrame276.classes_empty class_requests plan m

theorem picked : Local registry recorded branch.occurrence (.selected 3 (GeneralLatePeerGuard311.children plan)) :=
  GeneralLatePeerGuard311.select reached_recorded frame known rfl model_now admin (holds model model_now) (classes model)
    (GeneralLatePeerGuard311.no_merged alias_empty)

abbrev effect := GeneralLatePeerGuard311.effect (p := plan) reached_recorded frame known
abbrev emitted := install recorded effect

theorem enabled : GeneralNominalVersionedMixedKernel234.Installable compiled recorded effect :=
  GeneralLatePeerGuard311.enabled (p := plan) reached_recorded frame known picked model_now (holds model model_now) (classes model)

theorem peer_list : GeneralLatePeerGuard311.children plan = [child.occurrence] := by
  unfold GeneralLatePeerGuard311.children
  rw [show plan.packet = (extendedPlan rs ats owned old).packet from congrArg Plan.packet plan_flat]
  change GeneralNominalVersionedFrame231.children (extendedPacket rs ats owned middlePacket) = _
  rw [GeneralNominalVersionedTransport231.children_eq,middle_children]

theorem novel : ¬ Committed recorded plan := by
  intro history
  have kid : child.occurrence ∈ GeneralNominalVersionedFrame231.children plan.packet := by
    change child.occurrence ∈ GeneralLatePeerGuard311.children plan
    rw [peer_list]
    exact List.mem_singleton_self _
  have edge := history.2 child.occurrence kid
  change (branch.occurrence,child.occurrence) ∈ after.core.erased.current.edges ++
    GeneralNominalVersionedChildren232.edges GeneralLatePeerDirectPlan311.plan at edge
  rw [GeneralLatePeerFirst311.edges] at edge
  unfold GeneralNominalVersionedChildren232.edges at edge
  rw [GeneralLatePeerDirectPlan311.no_children] at edge
  simp only [List.map_nil,List.append_nil,List.mem_cons,List.not_mem_nil,or_false] at edge
  rcases edge with a|a <;> exact branch_different (congrArg (fun p : Occurrence roles × Occurrence roles => p.1.identity) a)

theorem step : Step compiled root recorded emitted :=
  ⟨branch.occurrence,GeneralNominalVersionedMixedGrowth234.generated
    (GeneralNominalVersionedMixedGrowth234.step GeneralLatePeerDirectInstall311.step) generated_branch,
    .install effect enabled novel⟩

theorem reached_emitted : B4TargetV8.Reachable (boundary roles) registry root emitted := by
  obtain ⟨first,ini,walk⟩ := reached_recorded
  exact ⟨first,ini,.tail walk step⟩

theorem models (m : Assignment) : Models emitted m ↔ Models recorded m :=
  ⟨GeneralNominalVersionedMixedKernel234.step_models step,
    fun valid => (install_models rfl).mpr
      ((GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ reached_recorded rfl rfl).mpr
        ⟨valid,holds m valid,classes m⟩)⟩

theorem inhabited : Models emitted model := (models _).mpr model_now

end Yulang.GeneralLatePeerRouteInstall311
