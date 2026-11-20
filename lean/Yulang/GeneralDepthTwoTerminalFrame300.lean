import Yulang.GeneralDepthTwoTerminalPlan300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralDepthTwoTerminalFrame300
open GeneralGeneratedNestedSource299
open GeneralGeneratedNestedPredictions299 (compiled parentPacket middle terminal)
open GeneralDepthTwoSecondInstall300 (final leafSite terminal_site emitted_sites)
open GeneralDepthTwoTerminalPlan300
open GeneralDepthTwoMiddleContext300 (after_raw_sites after_center_sites)
open GeneralNominalExamples (intDisplay)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedCandidates231
open GeneralNominalVersionedInstallation231 (reserved atoms)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalRecursiveInspection (Finished)
open GeneralNominalIdentities (source source_identity source_above_seed)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (sources)

abbrev res1 := GeneralDepthTwoMiddleContext300.res
abbrev res2 := reserved GeneralDepthTwoMiddleContext300.plan.packet
abbrev atoms1 := GeneralDepthTwoMiddleContext300.updates
abbrev atoms2 := atoms GeneralDepthTwoMiddleContext300.plan.packet

theorem final_model : Models final model :=
  (GeneralDepthTwoSecondInstall300.models model).mpr GeneralDepthTwoMiddleFrame300.after_model

theorem no_alias_terminal_root : terminal.identity ≠ root.identity := by decide +kernel

theorem source_support (i : Nat) (hit : i ∈ sources env.state) :
    i ≤ 2 ∨ i ∈ res1 ∨ i ∈ res2 := by
  change i ∈ (List.ofFn snapshot.base.source ++ List.ofFn snapshot.base.rowSource ++
    (([] ++ res1) ++ res2) ++ (([] ++ atoms1) ++ atoms2).flatMap GeneralNominalState.atomSources) at hit
  simp only [List.nil_append,List.mem_append,List.flatMap_append] at hit
  rcases hit with ((types|rows)|(old|new))|(first|second)
  · obtain ⟨n,same⟩ := List.mem_ofFn.mp types
    change n.val = i at same
    have high := n.isLt
    exact .inl (by omega)
  · obtain ⟨n,same⟩ := List.mem_ofFn.mp rows
    change n.val = i at same
    have high := n.isLt
    exact .inl (by omega)
  · exact .inr (.inl old)
  · exact .inr (.inr new)
  · left
    have bound : ∀ j ∈ atoms1.flatMap GeneralNominalState.atomSources, j ≤ 2 := by decide +kernel
    exact bound _ first
  · left
    have bound : ∀ j ∈ atoms2.flatMap GeneralNominalState.atomSources, j ≤ 2 := by decide +kernel
    exact bound _ second

theorem terminal_fresh (bs) : GeneralNominalVersionedAllocation231.Fresh env.state compiled terminal.identity bs := by
  intro key member collision
  have own := GeneralRebaseDisplayChildFresh276.keys_root member
  rcases source_support _ collision with small|old|new
  · have big : 2 < source env.state.seed key := source_above_seed _ _
    exact False.elim (Nat.not_lt_of_ge small big)
  · obtain ⟨prior,tracked,eq⟩ := List.mem_map.mp old
    have rootOwn : prior.1 = root.identity := GeneralRebaseDisplayChildFresh276.keys_root tracked
    have exactKey : prior = key := (source_identity env.state.seed _ _).mp eq
    exact False.elim (no_alias_terminal_root
      (own.symm.trans ((congrArg Prod.fst exactKey).symm.trans rootOwn)))
  · obtain ⟨prior,tracked,eq⟩ := List.mem_map.mp new
    have midOwn : prior.1 = middle.identity := GeneralRebaseDisplayChildFresh276.keys_root tracked
    have exactKey : prior = key := (source_identity env.state.seed _ _).mp eq
    exact False.elim (GeneralGeneratedNestedPredictions299.different_occurrences.2
      (midOwn.symm.trans ((congrArg Prod.fst exactKey).trans own)))

theorem located : GeneralNominalRecursiveCandidates.arguments env (inputs terminal) =
    some [((2 : Fin 3),(2 : Fin 3))] := by decide +kernel

theorem terminal_role : terminal.demand.role = 0 := by decide +kernel

theorem point_bounds : ∀ i, (inputs terminal).demand.arguments i = (2,2) := by
  intro i
  have arity : (roles (inputs terminal).demand.role).arity = 1 := by decide +kernel
  have h : i.val < 1 := Eq.mp (congrArg (fun k => i.val < k) arity) i.isLt
  have zero : i.val = 0 := by omega
  have same : i = ⟨0,by decide +kernel⟩ := Fin.ext zero
  subst i
  decide +kernel

theorem linked : GeneralNominalState.Linked env.state (inputs terminal).demand := by
  constructor
  · intro i
    rw [point_bounds]
    have target := GeneralNominalAllocationSupport.slot_source env.state (2 : Fin 3)
    exact ⟨target,target⟩
  · intro output no
    cases no

theorem prepared : Prepared compiled env terminal intDisplay := by
  refine ⟨⟨rfl,GeneralDepthTwoRootFrame300.metadata.2⟩,linked,[((2 : Fin 3),(2 : Fin 3))],
    located,terminal_fresh _,?_,model,?_⟩
  · change Finished (GeneralNominalPacketSupport.report packet)
    rw [report_exact]
    exact ⟨rfl,rfl,rfl⟩
  · have valid : GeneralNominalVersionedPlans231.Holds plan model := holds model final_model
    have hp : GeneralNominalVersionedPlans231.HeadModels packet model :=
      GeneralNominalVersionedPlans231.head_models (plan := plan) (model := model) valid
    have source := (headModels_packet_iff packet model).mpr hp
    change HeadModels compiled env leafSite.occurrence intDisplay [((2 : Fin 3),(2 : Fin 3))] model at source
    exact Eq.mp (congrArg (fun o => HeadModels compiled env o intDisplay [((2 : Fin 3),(2 : Fin 3))] model) terminal_site) source

theorem raw_sites : final.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,GeneralDepthTwoRootPlan300.child.observed,leafSite.observed] := by
  change GeneralDepthTwoFirstInstall300.after.core.erased.current.sites ++
    GeneralNominalVersionedChildren232.rawSites GeneralDepthTwoMiddleContext300.plan = _
  rw [after_raw_sites,GeneralNominalVersionedChildren232.rawSites,emitted_sites]
  rfl

theorem center_sites : final.core.sites =
    [GeneralDepthTwoRootPlan300.plan.input,GeneralDepthTwoRootPlan300.child,leafSite] := by
  change GeneralDepthTwoFirstInstall300.after.core.sites ++
    GeneralNominalVersionedChildren232.emitted GeneralDepthTwoMiddleContext300.plan = _
  rw [after_center_sites,emitted_sites]
  rfl

theorem frame : Frame compiled final.core terminal 3 plan := by
  refine ⟨rfl,rfl,terminal_site,rfl,?_,?_,List.mem_cons_self ..,terminal_role.symm,located,prepared⟩
  · rw [raw_sites]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · rw [center_sites]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end Yulang.GeneralDepthTwoTerminalFrame300
