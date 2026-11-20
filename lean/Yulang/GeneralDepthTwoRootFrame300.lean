import Yulang.GeneralDepthTwoRootPlan300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDepthTwoRootFrame300
open GeneralGeneratedNestedSource299
open GeneralGeneratedNestedInitial299 (initial_source)
open GeneralGeneratedNestedPredictions299
open GeneralDepthTwoRootPlan300 (plan holds bindings child)
open GeneralNominalExamples (registry intDisplay)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Effect)
open GeneralNominalVersionedCandidates231
open GeneralNominalVersionedPlans231 (head_models)
open GeneralSourceDictionaries
open GeneralDeclarations

theorem metadata : GeneralNominalRecursiveCandidates.Metadata compiled context :=
  ⟨rfl,initial_source.metadata.2⟩

theorem root_known : ¬ GeneralNominalState.RootPending snapshot (inputs root).demand := by
  rintro ⟨i,absent⟩
  exact absent ⟨(0 : Fin 3),rfl,Or.inr ⟨listDescriptor 1,rfl⟩⟩

theorem root_fresh (bs) : GeneralNominalVersionedAllocation231.Fresh snapshot compiled root.identity bs := by
  intro key _ overlaps
  have high := GeneralNominalIdentities.source_above_seed snapshot.seed key
  have low := initial_source.below_seed _ overlaps
  exact False.elim (Nat.not_lt_of_ge low high)

theorem root_located : GeneralNominalRecursiveCandidates.arguments context (inputs root) = some [(0,0)] := by
  decide +kernel

theorem prepared : Prepared compiled context root display := by
  refine ⟨metadata,initial_source.linked,[(0,0)],root_located,root_fresh _,?_,model,?_⟩
  · rw [root_report]
    exact ⟨rfl,rfl,rfl⟩
  · exact head_models (holds model snapshot_model)

theorem wrong_failed : Failed compiled context root intDisplay := by
  refine ⟨metadata,[(0,0)],root_located,root_fresh _,?_,?_,Or.inl ?_⟩
  all_goals decide +kernel

theorem wrong_not_prepared : ¬ Prepared compiled context root intDisplay := by
  rintro ⟨_,_,bounds,loc,_,done,_⟩
  cases Option.some.inj (loc.symm.trans root_located)
  exact (by decide +kernel : (GeneralNominalRecursiveCandidates.report context intDisplay
    [((0 : Fin 3),0)]).conflicts ≠ []) done.2.1

theorem frame : GeneralNominalVersionedEvidence231.Frame compiled initial.core root 1 plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,
    List.mem_cons_of_mem _ (List.mem_cons_self ..),rfl,root_located,prepared⟩

theorem survivor : Survivor compiled context root 1 [middle] :=
  ⟨root_known,display,List.mem_cons_of_mem _ (List.mem_cons_self ..),display_checked,rfl,rfl,
    [(0,0)],root_located,prepared,parent_children.symm⟩

theorem unique : Unique compiled context root 1 [middle] := by
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,id,role,_,_,ready,_⟩ := other
  rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
  · exact False.elim (wrong_not_prepared ready)
  · subst key
    exact ⟨rfl,survivor_children_functional GeneralRebaseCompiledDisplay277.compiled_checked copy survivor⟩

theorem initial_requests (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests initial.core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output h
  obtain ⟨site,listed,_,member⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp h
  change site ∈ [GeneralNominalDemandMerging.pointSite root] at listed
  cases List.mem_singleton.mp listed
  cases member

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready initial.core root plan := by
  intro output shown
  rw [initial_requests] at shown
  cases shown

def effect : Effect roles :=
  ⟨compiled,initial.core,plan,frame,parent_children.symm ▸ unique,ready⟩

end Yulang.GeneralDepthTwoRootFrame300
