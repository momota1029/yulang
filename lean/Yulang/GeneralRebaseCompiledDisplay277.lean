import Yulang.GeneralRebaseCompiledRetag277

set_option maxRecDepth 28000
set_option maxHeartbeats 9000000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompiledDisplay277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalExamples (registry context state model displayRoot displayChild intDisplay registry_checked)
open GeneralDeclarationExamples (roles display wrap display_checked)
open GeneralNominalVersionedCandidates231
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralRebaseDisplayFrame276 (before source_ids)
open GeneralRebaseCompiledRetag277
open GeneralNominalVersionedJournal232

abbrev compiled : Registry := GeneralNominalCenteredHeadAllocEncoding.registry registry
abbrev compiledWrap : Declaration := GeneralNominalCenteredHeadAllocEncoding.declaration wrap
abbrev parent : Plan roles := retag GeneralNominalNonleafPlan193.plan compiled rfl

theorem compiled_checked : Checked compiled :=
  GeneralNominalCenteredHeadAllocEncoding.registry_checked registry_checked

theorem compiled_members {d : Declaration} (present : d ∈ compiled.declarations)
    (role : d.role = 0) : d = intDisplay ∨ d = display := by
  change d ∈ [intDisplay,display,compiledWrap] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · cases role

theorem fresh {id bindings} :
    GeneralNominalVersionedAllocation231.Fresh (state true) compiled id bindings := by
  intro key _ collides
  have high := GeneralNominalIdentities.source_above_seed (state true).seed key
  have low := source_ids _ collides
  change 1 < _ at high
  omega

theorem prepared_parent : Prepared compiled (context true) displayRoot display := by
  obtain ⟨metadata,linked,bounds,found,_,finished,w,valid⟩ := GeneralRebaseDisplayFrame276.prepared
  have validPacket : GeneralNominalVersionedPlans231.HeadModels
      (⟨registry,context true,GeneralNominalDemandMerging.pointSite (inputs displayRoot),display,display_checked,bounds⟩ :
        GeneralNominalSaturationState.Packet roles) w := valid
  exact ⟨metadata,linked,bounds,found,fresh,finished,w,
     (headModels _ compiled rfl w).mpr validPacket⟩

theorem wrong_failed : Failed compiled (context true) displayRoot intDisplay := by
  refine ⟨GeneralNominalNonleafLocal193.prepared.1,[(0,0)],rfl,fresh,?_,?_,Or.inl ?_⟩
  all_goals decide +kernel

theorem wrong_not_prepared : ¬ Prepared compiled (context true) displayRoot intDisplay := by
  rintro ⟨_,_,bounds,loc,_,finished,_⟩
  have same : bounds = [((0 : Fin 2),(0 : Fin 2))] := Option.some.inj loc.symm
  subst bounds
  exact (by decide +kernel : (GeneralNominalRecursiveCandidates.report (context true) intDisplay [(0,0)]).conflicts ≠ [])
    finished.2.1

theorem children : GeneralNominalVersionedFrame231.children parent.packet = [displayChild] :=
  (children_eq GeneralNominalNonleafPlan193.packet compiled rfl).trans GeneralRebaseDisplayPacket276.children

theorem frame_parent : GeneralNominalVersionedEvidence231.Frame compiled before.core displayRoot 1 parent :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,by exact List.mem_cons_of_mem _ (List.mem_cons_self ..),rfl,rfl,prepared_parent⟩

theorem survivor_parent : Survivor compiled (context true) displayRoot 1 [displayChild] :=
  ⟨GeneralNominalNonleafLocal193.known,display,by exact List.mem_cons_of_mem _ (List.mem_cons_self ..),
   display_checked,rfl,rfl,[(0,0)],rfl,prepared_parent,children.symm⟩

theorem unique_parent : Unique compiled (context true) displayRoot 1 [displayChild] := by
  refine ⟨survivor_parent,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,check,identity,role,bounds,loc,ready,_⟩ := other
  rcases compiled_members visible role with rfl|rfl
  · exact False.elim (wrong_not_prepared ready)
  · subst key
    exact ⟨rfl,survivor_children_functional compiled_checked copy survivor_parent⟩

noncomputable def effect : Effect roles :=
  ⟨compiled,before.core,parent,frame_parent,children ▸ unique_parent,GeneralRebaseDisplayFrame276.ready⟩

noncomputable def after := GeneralNominalVersionedInstall232.install before effect
end Yulang.GeneralRebaseCompiledDisplay277
