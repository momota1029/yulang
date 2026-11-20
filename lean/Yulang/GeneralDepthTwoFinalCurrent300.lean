import Yulang.GeneralDepthTwoFinalHalt300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralDepthTwoFinalCurrent300
open GeneralGeneratedNestedSource299 (root model)
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoSecondInstall300 (final final_requests middleSite leafSite)
open GeneralDepthTwoFinalNodes300
open GeneralDepthTwoFinalScope300
open GeneralDepthTwoFinalSelection300 (unique safe ready)
open GeneralDepthTwoTerminalFrame300 (final_model)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenters (Plan Site)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalVersionedInstallation231 (replayPlan reserved atoms allocated)
open GeneralNominalVersionedTransport231 (extendedPlan)
open GeneralNominalVersionedInstall232 (installCore InstallationModels)
open GeneralNominalVersionedChildren232 (emitted rawSites)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalVersionedMixedKernel234 (Installable Committed AlternativesSafe)
open GeneralNominalVersionedMixedCurrentCandidate235 (Current)
open GeneralRebaseDisplayFrame276 (classes_empty)
open GeneralNominalCommonBridge (Assignment)

theorem emitted_extended (res updates owns) (p : Plan roles) :
    emitted (extendedPlan res updates owns p) = emitted p := by
  unfold emitted
  apply List.map_congr_left
  intro item _
  exact GeneralNominalVersionedTransport231.childSite_eq ..

theorem emitted_replay (p : Plan roles) : emitted (replayPlan p) = emitted p :=
  emitted_extended ..

theorem child_exact (n : Node) : children (plan n).packet = (childNodes n).map demand := by
  cases n
  · exact GeneralDepthTwoFinalParents300.root_children
  · exact GeneralDepthTwoFinalParents300.middle_children
  · exact GeneralDepthTwoTerminalPlan300.children_empty

theorem emitted_layout (n : Node) :
    emitted (plan n) = (childNodes n).map (fun j => (plan j).input) := by
  cases n
  · change emitted (extendedPlan _ _ _ (replayPlan GeneralDepthTwoRootPlan300.plan)) = [middleSite]
    rw [emitted_extended,emitted_replay,GeneralDepthTwoRootPlan300.emitted_sites]
  · change emitted (replayPlan GeneralDepthTwoMiddleContext300.plan) = [leafSite]
    rw [emitted_replay,GeneralDepthTwoSecondInstall300.emitted_sites]
  · apply List.length_eq_zero_iff.mp
    exact GeneralNominalVersionedChildren232.emitted_length _

theorem raw_sites_retained (n : Node) :
    (installCore final.core (plan n)).erased.current.sites ⊆ final.core.erased.current.sites := by
  intro s there
  change s ∈ final.core.erased.current.sites ++ rawSites (plan n) at there
  rcases List.mem_append.mp there with held|new
  · exact held
  · rw [rawSites,emitted_layout,GeneralDepthTwoTerminalFrame300.raw_sites] at *
    cases n
    · refine Eq.mpr (congrArg (fun t => t ∈ _) (List.mem_singleton.mp new)) ?_
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · refine Eq.mpr (congrArg (fun t => t ∈ _) (List.mem_singleton.mp new)) ?_
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    · cases new

theorem no_additional_requests (n : Node) (focus : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests (installCore final.core (plan n)) focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro out happened
  have before := GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
    (root := focus) (raw_sites_retained n) (fun _ h => h) happened
  rw [final_requests] at before
  cases before

theorem ready_at_site (n : Node) : GeneralNominalCenteredHeadMatEffects.Ready final.core (plan n).packet.site.occurrence (plan n) := by
  rw [site_focus]
  exact ready n

theorem key_eq (n : Node) : (plan n).packet.declaration.id = code n :=
  (frame n model final_model).key_eq

def certificate (n : Node) : Effect roles :=
  ⟨compiled,final.core,plan n,(site_focus n).symm ▸ ((key_eq n).symm ▸ frame n model final_model),
    (site_focus n).symm ▸ ((key_eq n).symm ▸ ((child_exact n).symm ▸ unique n)),ready_at_site n⟩

theorem installation (n : Node) (m : Assignment) (valid : Models final m) :
    InstallationModels final (certificate n) m := by
  have held := plan_holds n m valid
  refine ⟨valid,held,⟨GeneralNominalVersionedPlans231.head_models held,
    classes_empty (final_requests _) (plan n) m⟩,
    classes_empty (no_additional_requests n _) (plan n) m,?_,?_⟩
  · intro _ no; cases no
  · intro old _
    exact classes_empty (no_additional_requests n _) old.plan m

theorem safe_positions (n : Node) : GeneralNominalVersionedCycles232.Safe final (plan n) := by
  refine ⟨?_,fun entry _ => GeneralDepthTwoSafety300.semantic final_model entry.1⟩
  cases n <;> decide +kernel

theorem compatible (n : Node) :
    GeneralNominalCycleSteps.ChoiceCompatible final.core.erased.current (plan n).packet := by
  intro old seen equiv
  change old ∈ [GeneralDepthTwoMiddleContext300.plan.packet,GeneralGeneratedNestedPredictions299.parentPacket] at seen
  simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with rfl|rfl <;> cases n
  · rfl
  · rfl
  · have eq := alias_identity equiv
    have neq : (plan .leaf).packet.site.occurrence.identity ≠
        GeneralDepthTwoMiddleContext300.plan.packet.site.occurrence.identity := by decide +kernel
    exact False.elim (neq eq)
  · rfl
  · rfl
  · have eq := alias_identity equiv
    have neq : (plan .leaf).packet.site.occurrence.identity ≠
        GeneralGeneratedNestedPredictions299.parentPacket.site.occurrence.identity := by decide +kernel
    exact False.elim (neq eq)

theorem alternatives (n : Node) : AlternativesSafe compiled final (plan n).input := by
  intro p _ frame'
  have atSite := ((plan n).input_exact.trans (site_focus n)) ▸ frame'
  rw [paired_frame n p _ atSite]
  exact safe_positions n

theorem replay_schema (p : Plan roles) :
    GeneralNominalVersionedPlans231.emittedSchema (replayPlan p) =
    GeneralNominalVersionedPlans231.emittedSchema p :=
  GeneralNominalVersionedTransport231.emittedSchema_eq ..

theorem current (n : Node) : Current compiled final (demand n) (certificate n) := by
  refine ⟨rfl,rfl,site_focus n,?_,compatible n,safe_positions n,alternatives n,
    ⟨model,installation n model final_model⟩⟩
  cases n
  · change (GeneralNominalVersionedPlans231.emittedSchema
      (extendedPlan _ _ _ (replayPlan GeneralDepthTwoRootPlan300.plan))).unknown = false
    rw [GeneralNominalVersionedTransport231.emittedSchema_eq,replay_schema,GeneralDepthTwoRootPlan300.emitted_schema]
  · change (GeneralNominalVersionedPlans231.emittedSchema (replayPlan (extendedPlan _ _ _ GeneralDepthTwoMiddlePlan300.plan))).unknown = false
    rw [replay_schema,GeneralNominalVersionedTransport231.emittedSchema_eq,GeneralDepthTwoMiddlePlan300.emitted_schema]
  · exact congrArg (fun x => x.unknown) GeneralDepthTwoTerminalPlan300.schema_empty

end Yulang.GeneralDepthTwoFinalCurrent300
