import Yulang.GeneralNominalSaturationInstallation
import Yulang.GeneralNominalRecursiveRegressions

/-! Real nominal selection and pending same-input merging. The merge example
retains two distinct output targets and equates them before either root is ready. -/
namespace Yulang.GeneralNominalSaturationExamples

open GeneralNominalSaturationState GeneralNominalSaturationSteps
open GeneralNominalDemandMerging GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection
open GeneralDeclarations GeneralDeclarationPatterns

private theorem display_prepared : Prepared GeneralNominalExamples.registry (GeneralNominalExamples.context true)
    GeneralNominalExamples.displayRoot GeneralDeclarationExamples.display GeneralDeclarationExamples.display_checked := by
  obtain ⟨_,declaration,visible,checked,identity,_,_,_,prepared,_⟩ := GeneralNominalRecursiveExamples.display_survivor
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · contradiction
  · exact prepared
  · contradiction

private theorem display_inspected :
    (report (GeneralNominalExamples.context true) GeneralDeclarationExamples.display [(0,0)]).inspected = [(0,0)] := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,inspectMany,inspect,
    typeArguments,Report.visit,Report.append]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_1]
  rfl

private theorem display_not_recursive : ¬ GeneralNominalMixedRecurrence.RecursAt (GeneralNominalExamples.state true) 0 :=
  GeneralNominalMixedRecurrence.nominal_not_recursive _ _ GeneralNominalExamples.listDescriptor rfl

theorem display_selected : GeneralNominalLocalBoundary.Local
    (GeneralNominalLocalBoundary.recursiveFields GeneralDeclarationExamples.roles)
    GeneralNominalExamples.registry (GeneralNominalExamples.context true) GeneralNominalExamples.displayRoot
    (.selected 1 [GeneralNominalExamples.displayChild]) := by
  have located : arguments (GeneralNominalExamples.context true) GeneralNominalExamples.displayRoot = some [(0,0)] := by decide +kernel
  refine .selected ⟨GeneralNominalRecursiveExamples.display_survivor.1,?_,?_,?_⟩ ⟨GeneralNominalRecursiveExamples.display_survivor,?_⟩
  · rintro ⟨_,_,index,slot,equal,recursive⟩
    have same : slot = 0 := Fin.ext equal
    subst slot; exact display_not_recursive recursive
  · rintro ⟨_,declaration,visible,_,role,ready,bounds,found,visited,member,recursive⟩
    have same := Option.some.inj (located.symm.trans found); subst bounds
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl | rfl
    · obtain ⟨_,_,_,other,found,finished,_⟩ := ready
      have same := Option.some.inj (located.symm.trans found); subst other
      have conflict := finished.2.1
      rw [GeneralNominalRecursiveRegressions.int_head_conflicts] at conflict
      cases conflict
    · rw [display_inspected] at member
      have same := List.mem_singleton.mp member; subst visited
      exact display_not_recursive recursive
    · contradiction
  · rintro ⟨_,declaration,visible,checked,role,notFailed,notPrepared⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl | rfl
    · apply notFailed
      refine ⟨display_prepared.1,display_prepared.2.2.1,[(0,0)],located,?_,?_,Or.inl ?_⟩
      · decide +kernel
      · decide +kernel
      · rw [GeneralNominalRecursiveRegressions.int_head_conflicts]; simp
    · exact notPrepared display_prepared
    · contradiction
  · intro key children survivor
    exact (GeneralNominalRecursiveRegressions.display_exactly_one key children).mp survivor

theorem display_installs_all_children :
    ∃ packet : Packet GeneralDeclarationExamples.roles,
      packet.registry = GeneralNominalExamples.registry ∧ packet.context = GeneralNominalExamples.context true ∧
      packet.site.occurrence = GeneralNominalExamples.displayRoot ∧ packet.declaration.id = 1 ∧
      packet.children = [GeneralNominalExamples.displayChild] ∧
      Step GeneralNominalExamples.registry GeneralNominalExamples.displayRoot
        (initial (GeneralNominalExamples.context true) GeneralNominalExamples.displayRoot)
        (install (initial (GeneralNominalExamples.context true) GeneralNominalExamples.displayRoot) packet (pointEmitted packet)) := by
  obtain ⟨packet,registry,context,root,key,children,step,_,_⟩ :=
    GeneralNominalSaturationInstallation.initial_selected_installation _ _ _ _ _ display_selected (by intro empty; cases empty)
  exact ⟨packet,registry,context,root,key,children,step⟩

abbrev indexFirst : GeneralSourceDictionaries.Occurrence GeneralSourceStateExamples.roles :=
  ⟨100,GeneralSourceStateExamples.indexDemand⟩
abbrev indexLast : GeneralSourceDictionaries.Occurrence GeneralSourceStateExamples.roles :=
  ⟨101,{ GeneralSourceStateExamples.indexDemand with
    outputs := [⟨0,3⟩]
    declared := by intro output member; have same := List.mem_singleton.mp member; subst output; exact ⟨none,rfl⟩ }⟩
abbrev firstSite := pointSite indexFirst
abbrev lastSite := pointSite indexLast
abbrev indexContext : GeneralNominalCandidates.Context :=
  ⟨GeneralNominalState.extend GeneralNominalRegressions.indexState' [3] [],GeneralNominalExamples.interpretation⟩
abbrev pendingState : State GeneralSourceStateExamples.roles :=
  { context := indexContext, sites := [firstSite,lastSite] }

theorem pending_inputs_same : SameInputs (Models pendingState) firstSite lastSite := by
  refine ⟨rfl,?_⟩
  change All₂ (Related (Models pendingState)) [some (Origin.source 0),some (Origin.source 1)] [some (Origin.source 0),some (Origin.source 1)]
  exact .cons ⟨_,_,rfl,rfl,source_same _ _⟩ (.cons ⟨_,_,rfl,rfl,source_same _ _⟩ .nil)

private theorem empty_alias_equal {state : State roles} (empty : state.aliases = [])
    (alias : Alias state first last) : first = last := by
  induction alias with
  | refl => rfl
  | edge member => rw [empty] at member; cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem pending_merge_step (registry : Registry) :
    GeneralNominalState.RootPending pendingState.context.state indexFirst.demand ∧
      Step registry indexFirst pendingState (merge pendingState firstSite lastSite) := by
  refine ⟨GeneralNominalRegressions.index_pending,indexFirst,.root,?_⟩
  apply At.merge firstSite lastSite (by simp) (by simp) pending_inputs_same
  intro alias
  have impossible : (100 : Nat) = 101 := empty_alias_equal rfl alias
  contradiction

abbrev indexModel := GeneralNominalCommonBridge.lift (GeneralSourceStateExamples.indexModel (.base .int))

def associatedInt : AssociatedMeaning where
  value := fun _ _ _ => .base .int
  congruent := by intro _ _ _ _ _; exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem pending_merge_preserves_model : Models (merge pendingState firstSite lastSite) indexModel := by
  have original : Models pendingState indexModel := by
    refine ⟨?_,?_,?_⟩
    · apply (GeneralNominalState.extend_models ..).mpr
      exact ⟨GeneralNominalRegressions.index_all_common_assignments (.base .int),by intro atom member; cases member⟩
    · intro packet member; cases member
    · intro site member
      rcases List.mem_cons.mp member with rfl | member
      · exact point_holds indexFirst indexModel
      · have same := List.mem_singleton.mp member; subst site; exact point_holds indexLast indexModel
  apply merge_dictionary_models pendingState firstSite lastSite pending_inputs_same associatedInt indexModel original
  · refine ⟨[.base .str,.base .int],?_,?_⟩
    · exact .cons ⟨_,rfl,.source 0⟩ (.cons ⟨_,rfl,.source 1⟩ .nil)
    · intro output member
      have same := List.mem_singleton.mp member; subst output
      exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · refine ⟨[.base .str,.base .int],?_,?_⟩
    · exact .cons ⟨_,rfl,.source 0⟩ (.cons ⟨_,rfl,.source 1⟩ .nil)
    · intro output member
      have same := List.mem_singleton.mp member; subst output
      exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem pending_merge_output_equation (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models (merge pendingState firstSite lastSite) model) :
    CommonNominalFullCarrier.Equivalent (model 2).1 (model 3).1 :=
  ((output_atoms_exact firstSite lastSite model).mp ((merge_models ..).mp valid).2)
    ⟨0,2⟩ (List.mem_singleton_self _) ⟨0,3⟩ (List.mem_singleton_self _) rfl

end Yulang.GeneralNominalSaturationExamples
