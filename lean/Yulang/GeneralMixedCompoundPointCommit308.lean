import Yulang.GeneralMixedCompoundPointOutcome308
import Yulang.GeneralMixedCompoundCompilerGap308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralMixedCompoundPointCommit308
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundPointFirstPlan308 (pointFirst)
open GeneralMixedCompoundPointViewTrust308 (observed)
open GeneralMixedCompoundPointRoot308 (plan held child_exact frame_plan)
open GeneralMixedCompoundPointSites308 (request_exact equal_outputs raw_sites)
open GeneralMixedCompoundPointChild308 (reachable no_frame)
open GeneralNominalVersionedMixedKernel234 (Committed Installable)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem class_effects (m : Assignment) (valid : Models observed m) :
    GeneralNominalVersionedEffects231.ClassEffects observed.core root plan m := by
  refine ⟨?_,equal_outputs _ root⟩
  intro output member body found
  cases request_exact root output member
  have exactBody : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ :=
    (Option.some.inj found).symm
  subst body
  intro atom present
  cases List.mem_singleton.mp present
  exact GeneralMixedCompoundPointFirstPublic308.output_value m
    (GeneralMixedCompoundPointFirstPublic308.installed_held m
      ((GeneralMixedCompoundPointViewTrust308.models _).mp valid))

theorem current_child_edge :
    (root,childSite.occurrence) ∈ observed.core.erased.current.edges := by
  change (root,childSite.occurrence) ∈
    GeneralNominalVersionedChildren232.edges GeneralMixedCompoundPointFirstPlan308.plan
  exact GeneralNominalVersionedChildren232.child_edge
    (GeneralMixedCompoundPointFirstInstall308.actual_children ▸ List.mem_singleton_self _)

theorem committed : Committed observed plan := by
  refine ⟨fun m valid => ⟨held m valid,class_effects m valid⟩,?_⟩
  intro kid member
  rw [child_exact] at member
  cases List.mem_singleton.mp member
  exact current_child_edge

theorem reached_cases {focus : GeneralSourceDictionaries.Occurrence roles}
    (path : GeneralNominalSaturationState.Generated observed.core.erased.current root focus) :
    focus = root ∨ focus = childSite.occurrence := by
  obtain ⟨raw,member,eq⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
    (GeneralNominalVersionedMixedTrace235.reachable reachable).1 path
  rw [raw_sites] at member
  rcases List.mem_cons.mp member with rfl|rest
  · exact Or.inl eq.symm
  · cases List.mem_singleton.mp rest
    exact Or.inr eq.symm

theorem no_install (e : Effect roles)
    (linked : GeneralNominalSaturationState.Generated observed.core.erased.current root e.plan.packet.site.occurrence)
    (ready : Installable registry observed e) : Committed observed e.plan := by
  have f := e.frame
  rw [ready.registry_eq,ready.snapshot_eq] at f
  rcases reached_cases linked with atRoot|atChild
  · rw [atRoot] at f
    exact (frame_plan f).symm ▸ committed
  · rw [atChild] at f
    exact False.elim (no_frame _ _ f)

end Yulang.GeneralMixedCompoundPointCommit308
