import Yulang.GeneralDepthTwoMiddlePlan300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDepthTwoMiddleContext300
open GeneralGeneratedNestedSource299
open GeneralGeneratedNestedPredictions299 (compiled parentPacket middle terminal)
open GeneralDepthTwoFirstInstall300 (after)
open GeneralDepthTwoRootPlan300 (child child_args child_data)
open GeneralNominalState (sources)
open GeneralNominalIdentities (source source_above_seed source_identity)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedTransport231 (extendedPlan extendedPacket)
open GeneralNominalVersionedInstallation231 (reserved atoms allocated)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedFrame231 (children)
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveInspection (Origin)

abbrev env := after.core.erased.current.context
abbrev res := reserved parentPacket
abbrev updates := atoms parentPacket
abbrev owns := allocated parentPacket
abbrev pendingPlan := GeneralDepthTwoMiddlePlan300.plan
abbrev plan := extendedPlan res updates owns pendingPlan

theorem real_context : plan.packet.context = env := rfl

theorem same_base : env.state.base = snapshot.base := rfl

theorem seed_exact : env.state.seed = snapshot.seed := rfl

theorem prior_updates (m : Assignment) (held : Models after m) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m updates :=
  ((GeneralDictionaryOrdinaryTransport.models_extended ..).mp held.1.1).2

theorem holds (m : Assignment) (held : Models after m) : Holds plan m := by
  have valid := ((GeneralNominalVersionedJournal232.initial_models ..).mp
    ((GeneralDepthTwoFirstInstall300.models m).mp held)).1
  exact (GeneralNominalVersionedTransport231.holds_iff ..).mpr
    ⟨GeneralDepthTwoMiddlePlan300.holds m valid,prior_updates m held⟩

theorem same_children : children plan.packet = [terminal] :=
  (GeneralNominalVersionedTransport231.children_eq ..).trans GeneralGeneratedNestedPredictions299.middle_children

theorem middle_raw_site : GeneralNominalDemandMerging.pointSite middle = child.observed := by
  rw [← child_data.1]
  unfold GeneralNominalDemandMerging.pointSite GeneralNominalCenters.Site.observed
  congr 1
  congr 1
  funext i
  rw [child_args,child_data.2]
  rfl

theorem after_raw_sites : after.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,child.observed] := by
  change _ ++ GeneralNominalVersionedChildren232.rawSites GeneralDepthTwoRootPlan300.plan = _
  rw [GeneralNominalVersionedChildren232.rawSites,GeneralDepthTwoRootPlan300.emitted_sites]
  rfl

theorem after_center_sites : after.core.sites = [GeneralDepthTwoRootPlan300.plan.input,child] := by
  change _ ++ GeneralNominalVersionedChildren232.emitted GeneralDepthTwoRootPlan300.plan = _
  rw [GeneralDepthTwoRootPlan300.emitted_sites]
  rfl

theorem source_support (n : Nat) (hit : n ∈ sources env.state) : n ≤ 2 ∨ n ∈ res := by
  change n ∈ List.ofFn snapshot.base.source ++ List.ofFn snapshot.base.rowSource ++
     ([] ++ res) ++ ([] ++ updates).flatMap GeneralNominalState.atomSources at hit
  simp only [List.nil_append,List.mem_append] at hit
  rcases hit with ((types|rows)|reserved)|atoms
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp types
    change i.val = n at eq
    have bound := i.isLt
    exact .inl (by omega)
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp rows
    change i.val = n at eq
    have bound := i.isLt
    exact .inl (by omega)
  · exact .inr reserved
  · left
    have bounded : ∀ n ∈ updates.flatMap GeneralNominalState.atomSources, n ≤ 2 := by decide +kernel
    exact bounded n atoms

theorem fresh (bs) : GeneralNominalVersionedAllocation231.Fresh env.state compiled middle.identity bs := by
  intro key member collision
  have current := GeneralRebaseDisplayChildFresh276.keys_root member
  rcases source_support _ collision with small|legacy
  · have large : 2 < source env.state.seed key := source_above_seed _ _
    exact False.elim (Nat.not_lt_of_ge small large)
  · obtain ⟨old,inList,eq⟩ := List.mem_map.mp legacy
    have rooted : old.1 = root.identity := GeneralRebaseDisplayChildFresh276.keys_root inList
    have equal : old = key := (source_identity env.state.seed _ _).mp eq
    exact False.elim (GeneralGeneratedNestedPredictions299.different_occurrences.1
      (rooted.symm.trans ((congrArg Prod.fst equal).trans current)))

end Yulang.GeneralDepthTwoMiddleContext300
