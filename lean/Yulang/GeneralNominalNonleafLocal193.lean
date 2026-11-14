import Yulang.GeneralNominalCenteredExamples
import Yulang.GeneralNominalNonleafPlan193
import Yulang.GeneralNominalHeadLeafPlan189

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalNonleafLocal193
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs
open GeneralNominalNonleafPlan193
open GeneralNominalExamples (registry context state displayRoot displayChild model state_models)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalCenteredHeadCandidates

theorem prepared : Prepared registry (context true) displayRoot display :=
  old_prepared_head GeneralDictionarySupportRecursiveExample.enabled.1.2.2.2.2.2.2.1

theorem frame : Frame registry start.core displayRoot 1 plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,by simp,rfl,rfl,prepared⟩

theorem known : ¬ GeneralNominalState.RootPending (state true) displayRoot.demand :=
  GeneralNominalRecursiveExamples.display_survivor.1

theorem survivor : Survivor registry (context true) displayRoot 1 [displayChild] :=
  old_survivor_head GeneralNominalRecursiveExamples.display_survivor

theorem wrong_failed : Failed registry (context true) displayRoot GeneralNominalExamples.intDisplay := by
  refine ⟨prepared.1,prepared.2.2.1,[(0,0)],rfl,?_,?_,Or.inl ?_⟩ <;> decide +kernel

theorem unique : Unique registry (context true) displayRoot 1 [displayChild] := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,check,identity,role,bounds,located,ready,_⟩ := found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · obtain ⟨_,_,_,bs,loc,finished,_⟩ := ready
    have equal := Option.some.inj (loc.symm.trans located)
    subst bs
    have equal := Option.some.inj located
    subst bounds
    have bad := finished.2.1
    exact False.elim ((by decide +kernel : (GeneralNominalRecursiveCandidates.report (context true) GeneralNominalExamples.intDisplay [(0,0)]).conflicts ≠ []) bad)
  · have same : key = 1 := identity.symm
    subst key
    exact ⟨rfl,survivor_children_functional GeneralNominalExamples.registry_checked copy survivor⟩
  · contradiction

theorem requests_empty : requests start.core displayRoot = [] :=
  GeneralNominalHeadInitialEffects188.initial_requests (context true)

theorem effects_ready : EffectsReady start.core displayRoot plan :=
  GeneralNominalHeadInitialEffects188.empty_effects_ready requests_empty plan

theorem no_output_conflict : ¬ GeneralNominalCenteredHeadStepBoundary.OutputConflict registry start displayRoot 1 := by
  intro conflict
  apply conflict.2
  refine ⟨model,(source_models model).mpr (state_models true),⟨[displayChild],unique⟩,plan,frame,effects_ready,?_,?_⟩
  · have eqs := equations model (state_models true)
    exact ⟨eqs.1,fun name member => eqs.2.1 name (Or.inl member),eqs.2.2.1⟩
  · exact GeneralNominalHeadLeafPlan189.output_equations_empty plan requests_empty model

theorem safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry start displayRoot := by
  have old := GeneralNominalCenteredExamples.display_selected
  cases old with
  | selected oldSafe oldUnique =>
    refine ⟨known,oldSafe.2.1,?_,?_⟩
    · rintro (raw | ⟨_,_,_,_,_,_,_,_,_,_,_,cycle⟩)
      · exact oldSafe.2.2.1 (Or.inl raw)
      · exact GeneralNominalCenteredSteps.initial_acyclic _ _
          (GeneralNominalActualInspectionExamples.acyclic false) _ cycle
    · rintro (⟨_,d,visible,role,notFailed,notPrepared⟩ | legacy | decision | admin)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
        rcases visible with rfl | rfl | rfl
        · exact notFailed wrong_failed
        · exact notPrepared prepared
        · contradiction
      · exact oldSafe.2.2.2 (Or.inl (Or.inr legacy))
      · exact oldSafe.2.2.2 (Or.inr decision)
      · exact admin (GeneralNominalCenteredAdministrativeLocal.initial_ready (context true) displayRoot)

theorem selected : GeneralNominalCenteredHeadWFBoundary.Local registry start displayRoot (.selected 1 [displayChild]) :=
  .selected safe unique no_output_conflict

end Yulang.GeneralNominalNonleafLocal193
