import Yulang.GeneralDepthTwoMiddleContext300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDepthTwoMiddleFrame300
open GeneralGeneratedNestedSource299
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoFirstInstall300 (after models requests)
open GeneralDepthTwoMiddleContext300
open GeneralDepthTwoRootPlan300 (child)
open GeneralNominalExamples (intDisplay)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalVersionedJournal232 (Models Effect)
open GeneralNominalVersionedCandidates231
open GeneralNominalVersionedPlans231 (head_models)
open GeneralDeclarations

theorem after_model : Models after model := (models model).mpr initial_model

theorem metadata : GeneralNominalRecursiveCandidates.Metadata compiled env :=
  ⟨rfl,GeneralDepthTwoRootFrame300.metadata.2⟩

theorem located : GeneralNominalRecursiveCandidates.arguments env (inputs middle) = some [((1 : Fin 3),(1 : Fin 3))] := by
  decide +kernel

theorem middle_role : middle.demand.role = 0 := by decide +kernel

theorem input_bounds : ∀ i, (inputs middle).demand.arguments i = (1,1) := by
  intro i
  have arity : (roles (inputs middle).demand.role).arity = 1 := by decide +kernel
  have h : i.val < 1 := Eq.mp (congrArg (fun k => i.val < k) arity) i.isLt
  have iz : i.val = 0 := by omega
  have same : i = ⟨0,by decide +kernel⟩ := Fin.ext iz
  subst i
  decide +kernel

theorem known : ¬ GeneralNominalState.RootPending env.state (inputs middle).demand := by
  rintro ⟨i,absent⟩
  rw [input_bounds] at absent
  exact absent ⟨(1 : Fin 3),rfl,Or.inr ⟨listDescriptor 2,rfl⟩⟩

theorem linked : GeneralNominalState.Linked env.state (inputs middle).demand := by
  constructor
  · intro i
    rw [input_bounds]
    have target := GeneralNominalAllocationSupport.slot_source env.state (1 : Fin 3)
    exact ⟨target,target⟩
  · intro output no
    cases no

theorem prepared : Prepared compiled env middle display := by
  refine ⟨metadata,linked,[((1 : Fin 3),(1 : Fin 3))],located,fresh _,?_,model,?_⟩
  · change GeneralNominalRecursiveInspection.Finished
      (GeneralNominalRecursiveCandidates.report
        (GeneralDictionaryOrdinaryTransport.extend context res updates owns) display [((1 : Fin 3),(1 : Fin 3))])
    rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
      GeneralDictionaryOrdinaryTransport.report]
    rw [GeneralGeneratedNestedPredictions299.middle_report]
    exact ⟨rfl,rfl,rfl⟩
  · exact head_models (holds model after_model)

theorem wrong_failed : Failed compiled env middle intDisplay := by
  refine ⟨metadata,[((1 : Fin 3),(1 : Fin 3))],located,fresh _,?_,?_,Or.inl ?_⟩
  all_goals decide +kernel

theorem wrong_not_prepared : ¬ Prepared compiled env middle intDisplay := by
  rintro ⟨_,_,bounds,loc,_,done,_⟩
  cases Option.some.inj (loc.symm.trans located)
  exact (by decide +kernel : (GeneralNominalRecursiveCandidates.report env intDisplay [((1 : Fin 3),(1 : Fin 3))]).conflicts ≠ []) done.2.1

theorem outputs_empty : middle.demand.outputs = [] := by decide +kernel

theorem inputs_eq_when_blank (o : GeneralSourceDictionaries.Occurrence roles) (empty : o.demand.outputs = []) :
    inputs o = o := by
  cases o with
  | mk id demand =>
    cases demand with
    | mk role args outs evidence =>
      change outs = [] at empty
      subst outs
      rfl

theorem point_inputs : GeneralNominalDemandMerging.pointSite (inputs middle) =
    GeneralNominalDemandMerging.pointSite middle := by
  rw [inputs_eq_when_blank middle outputs_empty]

theorem frame : GeneralNominalVersionedEvidence231.Frame compiled after.core middle 1 plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,List.mem_cons_of_mem _ (List.mem_cons_self ..),middle_role.symm,located,prepared⟩
  · rw [after_raw_sites]
    change GeneralNominalDemandMerging.pointSite middle ∈ _
    rw [middle_raw_site]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · rw [after_center_sites]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem survivor : Survivor compiled env middle 1 [terminal] := by
  refine ⟨known,display,List.mem_cons_of_mem _ (List.mem_cons_self ..),display_checked,
    rfl,middle_role.symm,[((1 : Fin 3),(1 : Fin 3))],located,prepared,?_⟩
  unfold children
  rw [point_inputs]
  exact same_children.symm

theorem unique : Unique compiled env middle 1 [terminal] := by
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,id,role,_,_,ready,_⟩ := other
  rcases GeneralRebaseCompiledDisplay277.compiled_members visible (role.trans middle_role) with rfl|rfl
  · exact False.elim (wrong_not_prepared ready)
  · subst key
    exact ⟨rfl,survivor_children_functional GeneralRebaseCompiledDisplay277.compiled_checked copy survivor⟩

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready after.core middle plan := by
  intro output shown
  rw [requests] at shown
  cases shown

def effect : Effect roles := ⟨compiled,after.core,plan,frame,same_children.symm ▸ unique,ready⟩

end Yulang.GeneralDepthTwoMiddleFrame300
