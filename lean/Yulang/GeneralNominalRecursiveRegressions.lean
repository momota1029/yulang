import Yulang.GeneralNominalRecursiveExamples
import Yulang.GeneralNominalRecursiveBoundary

/-! Regression tests on the recursive, projection-aware candidate predicates. -/
namespace Yulang.GeneralNominalRecursiveRegressions

open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalRegressions GeneralDeclarations GeneralDeclarationPatterns

theorem index_pending_not_K2 :
    GeneralNominalState.RootPending indexState' GeneralSourceStateExamples.indexDemand ∧
      ¬ GeneralNominalMixedRecurrence.RootK2 indexState' GeneralSourceStateExamples.indexDemand :=
  ⟨index_pending,GeneralNominalMixedRecurrence.pending_excludes_K2 _ _ index_pending⟩

theorem shadow_not_K2 : ¬ GeneralNominalMixedRecurrence.RootK2 shadowState'
    GeneralSourceStateExamples.loopDemand :=
  GeneralNominalMixedRecurrence.pending_excludes_K2 _ _ shadow_pending

theorem loop_K2 : GeneralNominalMixedRecurrence.RootK2 loopState' GeneralSourceStateExamples.loopDemand :=
  GeneralNominalMixedRecurrence.old_rootK2 _ _ GeneralNominalIntervalExamples.loop_K2

theorem unresolved_payload_blocks :
    (report (GeneralNominalExamples.context false) concreteList [(0,0)]).blocked = [(1,1)] := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,inspectMany,inspect,
    typeArguments,Report.visit,Report.append]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_3]
  simp [Report.append,Report.visit,block]

theorem inspection_pending : InspectionPending concreteRegistry (GeneralNominalExamples.context false)
    GeneralNominalExamples.displayRoot := by
  have ready : ¬ GeneralNominalState.RootPending (GeneralNominalExamples.context false).state
      GeneralNominalExamples.displayRoot.demand := by
    rintro ⟨index,unknown⟩
    exact unknown ⟨0,rfl,Or.inr ⟨GeneralNominalExamples.listDescriptor,rfl⟩⟩
  apply GeneralNominalRecursiveCandidates.blocked_defers _ _ _ ready concreteList (by simp)
    concrete_checked rfl [(0,0)] (by decide +kernel)
  rw [unresolved_payload_blocks]
  simp

theorem repeated_bindings : bindings conflictState
    (report conflictContext GeneralCandidateConflictExamples.repeated [(0,0),(1,1)]) = conflicting := by
  simp [bindings,report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,inspectMany,inspect,Report.append]

theorem no_conflict_survivors (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles)) :
    ¬ Survivor GeneralCandidateConflictExamples.registry conflictContext GeneralCandidateConflictExamples.root key children := by
  rintro ⟨_,declaration,visible,checked,_,_,_,_,prepared,_⟩
  have same := List.mem_singleton.mp visible
  subst declaration
  obtain ⟨_,_,_,bounds,located,_,_,model,models⟩ := prepared
  have located' : arguments conflictContext GeneralCandidateConflictExamples.root = some [(0,0),(1,1)] := by decide +kernel
  have same := Option.some.inj (located'.symm.trans located)
  subst bounds
  have sound := branch_interval_sound _ _ _ _ _ _ model models
  have compatible : GeneralNominalAllocation.Compatible (bindings conflictState
      (report conflictContext GeneralCandidateConflictExamples.repeated [(0,0),(1,1)])) model := sound.2.1
  rw [repeated_bindings] at compatible
  exact cross_conflict ⟨model,sound.1,compatible⟩

abbrev coarseFirst : Capture GeneralNominalIntervalExamples.source :=
  ⟨7,(2,3),some (.nominal (.source 0) 0 0)⟩
abbrev coarseLast : Capture GeneralNominalIntervalExamples.source :=
  ⟨7,(2,3),some (.nominal (.source 1) 0 0)⟩

theorem coarse_actual_conflict : ¬ ProjectionModels GeneralNominalIntervalExamples.source
    { captures := [coarseFirst,coarseLast] } (GeneralNominalIntervalExamples.model .int .str) := by
  intro models
  have equal := models.2.2.2 coarseFirst (by simp) coarseLast (by simp) rfl _ _ rfl rfl
    (.base .int) (.base .str)
    (.nominal (.source 0) ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩ rfl)
    (.nominal (.source 1) ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩ rfl)
  have old := (CommonNominalFullModelMap.subtype_exact (.base .int) (.base .str)).mp equal.1
  cases (CommonRigidHeadInspection.base_iff .int .str).mp old

theorem len_not_rootK2 : ¬ GeneralNominalMixedRecurrence.RootK2 GeneralNominalMixedExamples.state
    GeneralNominalRecursiveExamples.lenRoot.demand := by
  rintro ⟨_,_,index,slot,equal,recursive⟩
  have slotEq : slot = 1 := Fin.ext equal
  subst slot
  exact GeneralNominalMixedExamples.list_not_recursive recursive

theorem int_head_conflicts : (report (GeneralNominalExamples.context true) GeneralNominalExamples.intDisplay [(0,0)]).conflicts = [(0,0)] := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,inspectMany,inspect,Report.visit,Report.append]

theorem display_exactly_one (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles)) :
    Survivor GeneralNominalExamples.registry (GeneralNominalExamples.context true) GeneralNominalExamples.displayRoot key children ↔
      key = 1 ∧ children = [GeneralNominalExamples.displayChild] := by
  have located' : arguments (GeneralNominalExamples.context true) GeneralNominalExamples.displayRoot = some [(0,0)] := by decide +kernel
  constructor
  · intro survivor
    have original := survivor
    obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,_⟩ := survivor
    have equal := Option.some.inj (located'.symm.trans located)
    subst bounds
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl | rfl
    · obtain ⟨_,_,_,other,found,finished,_⟩ := prepared
      have equal := Option.some.inj (located'.symm.trans found)
      subst other
      have bad : (report (GeneralNominalExamples.context true) GeneralNominalExamples.intDisplay [(0,0)]).conflicts = [] := finished.2.1
      rw [int_head_conflicts] at bad
      cases bad
    · have keySame : key = 1 := identity.symm
      subst key
      exact ⟨rfl,survivor_children_functional _ GeneralNominalExamples.registry_checked _ _ 1 children
        [GeneralNominalExamples.displayChild] original GeneralNominalRecursiveExamples.display_survivor⟩
    · contradiction
  · rintro ⟨rfl,rfl⟩
    exact GeneralNominalRecursiveExamples.display_survivor

theorem nonpoint_unresolved_payload_blocks :
    (report GeneralNominalRecursiveExamples.nonpointContext concreteList [(0,0)]).blocked = [(2,3)] := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,inspectMany,inspect,
    typeArguments,Report.visit,Report.append]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_3]
  simp [Report.append,Report.visit,block]

theorem nonpoint_inspection_pending : InspectionPending concreteRegistry GeneralNominalRecursiveExamples.nonpointContext
    GeneralNominalRecursiveExamples.nonpointRoot := by
  have ready := (GeneralNominalRecursiveExamples.nonpoint_survivor .int .str).1
  apply GeneralNominalRecursiveCandidates.blocked_defers _ _ _ ready concreteList (by simp)
    concrete_checked rfl [(0,0)] (by decide +kernel)
  rw [nonpoint_unresolved_payload_blocks]
  simp

theorem len_inspected :
    (report GeneralNominalMixedExamples.context GeneralNominalRecursiveExamples.len [(1,1)]).inspected = [(1,1)] := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,inspectMany,inspect,
    typeArguments,Report.visit,Report.append]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_1]
  rfl

theorem len_not_candidateK2 : ¬ CandidateK2 GeneralNominalRecursiveExamples.lenRegistry
    GeneralNominalMixedExamples.context GeneralNominalRecursiveExamples.lenRoot := by
  rintro ⟨_,declaration,visible,_,_,_,bounds,located,visited,member,recursive⟩
  have same := List.mem_singleton.mp visible; subst declaration
  have found : arguments GeneralNominalMixedExamples.context GeneralNominalRecursiveExamples.lenRoot = some [(1,1)] := by decide +kernel
  have same := Option.some.inj (found.symm.trans located); subst bounds
  have member' : visited ∈ (report GeneralNominalMixedExamples.context GeneralNominalRecursiveExamples.len [(1,1)]).inspected := member
  rw [len_inspected] at member'
  have same := List.mem_singleton.mp member'; subst visited
  exact GeneralNominalMixedExamples.list_not_recursive recursive

theorem len_not_inspection_pending : ¬ InspectionPending GeneralNominalRecursiveExamples.lenRegistry
    GeneralNominalMixedExamples.context GeneralNominalRecursiveExamples.lenRoot := by
  rintro ⟨_,declaration,visible,checked,_,_,unprepared⟩
  have same := List.mem_singleton.mp visible; subst declaration
  obtain ⟨_,other,member,_,_,_,_,_,prepared,_⟩ := GeneralNominalRecursiveExamples.len_list_survivor
  have same := List.mem_singleton.mp member; subst other
  exact unprepared prepared

theorem len_selected : GeneralNominalLocalBoundary.Local
    (GeneralNominalLocalBoundary.recursiveFields GeneralDeclarationExamples.roles)
    GeneralNominalRecursiveExamples.lenRegistry GeneralNominalMixedExamples.context
    GeneralNominalRecursiveExamples.lenRoot (.selected 30 []) := by
  refine .selected ⟨GeneralNominalRecursiveExamples.len_list_survivor.1,len_not_rootK2,
    len_not_candidateK2,len_not_inspection_pending⟩ ⟨GeneralNominalRecursiveExamples.len_list_survivor,?_⟩
  intro key children survivor
  have original := survivor
  obtain ⟨_,declaration,visible,_,identity,_⟩ := survivor
  have same := List.mem_singleton.mp visible; subst declaration
  have keySame : key = 30 := identity.symm; subst key
  refine ⟨rfl,survivor_children_functional _ ?_ _ _ 30 children [] original GeneralNominalRecursiveExamples.len_list_survivor⟩
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  have same := List.mem_singleton.mp member; subst declaration
  exact GeneralNominalRecursiveExamples.len_checked

end Yulang.GeneralNominalRecursiveRegressions
