import Yulang.GeneralNominalCycleWrapper

/-! The cycle-based rule rejects a list node on its own argument cycle,
while a separate outer list around a recursive record remains selectable. -/
namespace Yulang.GeneralNominalCycleRegressions

open GeneralNominalCycleK2
open GeneralSourceDictionaries GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveExamples (len lenRegistry lenRoot len_checked)

theorem loop_K2 : RootK2 GeneralNominalRegressions.loopState' GeneralSourceStateExamples.loopDemand := by
  have old := GeneralNominalRegressions.loop_K2
  refine ⟨old.1,old.2.1,⟨0,by decide +kernel⟩,0,rfl,Or.inl ?_⟩
  exact ⟨0,Or.inl ⟨0,(fun _ => 0),rfl,⟨0,by decide +kernel⟩,rfl⟩,.nil _⟩

theorem shadow_not_K2 : ¬ RootK2 GeneralNominalRegressions.shadowState' GeneralSourceStateExamples.loopDemand :=
  pending_excludes_K2 _ _ GeneralNominalRegressions.shadow_pending

theorem index_pending_not_K2 :
    GeneralNominalState.RootPending GeneralNominalRegressions.indexState' GeneralSourceStateExamples.indexDemand ∧
      ¬ RootK2 GeneralNominalRegressions.indexState' GeneralSourceStateExamples.indexDemand :=
  ⟨GeneralNominalRegressions.index_pending,pending_excludes_K2 _ _ GeneralNominalRegressions.index_pending⟩

theorem nominal_cycle_K2 (invocation : Nat) :
    RootK2 GeneralNominalProgressObstruction.state (GeneralNominalProgressObstruction.root invocation).demand := by
  refine ⟨?_,(GeneralNominalProgressObstruction.survivor invocation).1,⟨0,by change 0 < 1; decide +kernel⟩,0,rfl,Or.inl ?_⟩
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  · exact ⟨0,Or.inr ⟨GeneralNominalProgressObstruction.descriptor,rfl,0,rfl⟩,.nil _⟩

theorem nominal_candidate_K2 (invocation : Nat) : CandidateK2 GeneralNominalProgressObstruction.registry
    GeneralNominalProgressObstruction.context (GeneralNominalProgressObstruction.root invocation) := by
  have survivor := GeneralNominalProgressObstruction.survivor invocation
  have ready := survivor.1
  obtain ⟨_,declaration,visible,checked,_,role,bounds,located,prepared,_⟩ := survivor
  have same := List.mem_singleton.mp visible; subst declaration
  have found : GeneralNominalRecursiveCandidates.arguments GeneralNominalProgressObstruction.context
      (GeneralNominalProgressObstruction.root invocation) = some [(0,0)] := by
    change GeneralNominalRecursiveCandidates.arguments GeneralNominalProgressObstruction.context
      (GeneralNominalProgressObstruction.root 0) = some [(0,0)]
    decide +kernel
  have same := Option.some.inj (found.symm.trans located); subst bounds
  apply prepared_cycle _ _ _ ready GeneralDeclarationExamples.display visible checked role prepared [(0,0)] located (0,0)
    (by decide +kernel)
  exact Or.inr ⟨⟨0,Or.inr GeneralNominalProgressObstruction.actual_self_edge,.nil _⟩,
    _,GeneralNominalProgressObstruction.state_models⟩

theorem nominal_display_rejected (invocation : Nat) : Local GeneralNominalProgressObstruction.registry
    GeneralNominalProgressObstruction.context (GeneralNominalProgressObstruction.root invocation) .rejected :=
  root_rejected _ _ _ (nominal_cycle_K2 invocation)

theorem obstruction_child_accessible (invocation : Nat) :
    Acc (CommonRoleOutermostResolver.Child (Local GeneralNominalProgressObstruction.registry GeneralNominalProgressObstruction.context))
      (GeneralNominalProgressObstruction.root invocation) := rejected_accessible (nominal_display_rejected invocation)

abbrev nominalLenRoot : Occurrence roles := ⟨200,⟨3,fun _ => (0,0),[],by intro _ member; cases member⟩⟩

theorem nominal_len_K2 : RootK2 GeneralNominalProgressObstruction.state nominalLenRoot.demand := by
  refine ⟨?_,?_,⟨0,by decide +kernel⟩,0,rfl,Or.inr ⟨?_,_,GeneralNominalProgressObstruction.state_models⟩⟩
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  · rintro ⟨index,unknown⟩
    exact unknown ⟨0,rfl,Or.inr ⟨GeneralNominalProgressObstruction.descriptor,rfl⟩⟩
  · exact ⟨0,Or.inr GeneralNominalProgressObstruction.actual_self_edge,.nil _⟩

theorem nominal_len_rejected : Local lenRegistry GeneralNominalProgressObstruction.context nominalLenRoot .rejected :=
  root_rejected _ _ _ nominal_len_K2

/-- The earlier mixed fixture has both nodes on the cycle. Its list node now
rejects too; it is distinct from the separate wrapper used below. -/
theorem mixed_list_root_K2 : RootK2 GeneralNominalMixedExamples.state GeneralNominalMixedExamples.showRoot.demand := by
  refine ⟨?_,?_,⟨0,by decide +kernel⟩,1,rfl,Or.inl ?_⟩
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  · rintro ⟨index,unknown⟩
    exact unknown ⟨1,rfl,Or.inr ⟨GeneralNominalMixedExamples.descriptor,rfl⟩⟩
  · refine ⟨0,Or.inr ⟨GeneralNominalMixedExamples.descriptor,rfl,0,rfl⟩,?_⟩
    exact .cons (Or.inl GeneralNominalMixedExamples.structural_edge) (.nil _)

open GeneralNominalCycleWrapper in
private theorem wrapper_prepared : GeneralNominalRecursiveCandidates.Prepared lenRegistry context lenRoot len len_checked := by
  have query : GeneralNominalInspection.queries state context.interpretation len = [.nominal 0 [.variables [0]]] := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
      GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]
  have calculated := GeneralNominalUnaryCaptureFacts.report_exact context len 1 descriptor rfl 0 (0,0) rfl query
  have branch := GeneralNominalUnaryCaptureFacts.private_models context lenRegistry lenRoot len 1 descriptor rfl 0 rfl
    (0,0) rfl query model state_models
  have schema : GeneralNominalRecursiveCandidates.generated lenRegistry context lenRoot len len_checked [(1,1)] = {} := by
    unfold GeneralNominalRecursiveCandidates.generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
      len,List.mergeSort_nil]
    rfl
  refine ⟨?_,?_,GeneralNominalUnaryCaptureFacts.initial_fresh state lenRegistry 200 (by decide +kernel),
    [(1,1)],by decide +kernel,?_,?_,model,branch.1,branch.2,?_⟩
  · refine ⟨rfl,?_⟩
    intro name primitive recorded
    by_cases two : name = 2
    · subst name
      have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
      subst primitive; exact ⟨⟨[],2⟩,rfl,rfl⟩
    · simp [two] at recorded
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  · rw [calculated]; exact ⟨rfl,rfl,rfl⟩
  · exact ⟨(by intro output member; cases member),(by rw [schema])⟩
  · rw [schema]; exact GeneralNominalMaterialization.empty_models ..

open GeneralNominalCycleWrapper in
theorem wrapper_len_survivor : GeneralNominalRecursiveCandidates.Survivor lenRegistry context lenRoot 30 [] := by
  refine ⟨?_,len,by simp,len_checked,rfl,rfl,[(1,1)],by decide +kernel,wrapper_prepared,?_⟩
  · rintro ⟨index,unknown⟩; exact unknown ⟨1,rfl,Or.inr ⟨descriptor,rfl⟩⟩
  · unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
    simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
      GeneralDeclarationDemands.emitAll]

open GeneralNominalCycleWrapper in
theorem wrapper_len_not_K2 : ¬ RootK2 state lenRoot.demand := by
  rintro ⟨_,_,index,slot,equal,cycle⟩
  have one : slot = 1 := Fin.ext equal; subst slot
  exact list_off_cycle (recurs_cycle _ _ cycle)

open GeneralNominalCycleWrapper in
private theorem wrapper_inspected : (GeneralNominalRecursiveCandidates.report context len [(1,1)]).inspected = [(1,1)] := by
  simp [GeneralNominalRecursiveCandidates.report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,GeneralNominalRecursiveInspection.inspectMany,
    GeneralNominalRecursiveInspection.inspect,GeneralNominalRecursiveInspection.typeArguments,
    GeneralNominalRecursiveInspection.Report.visit,GeneralNominalRecursiveInspection.Report.append]
  rw [GeneralNominalRecursiveInspection.inspectMany.eq_2,GeneralNominalRecursiveInspection.inspectMany.eq_1,
    GeneralNominalRecursiveInspection.inspect.eq_1]
  rfl

open GeneralNominalCycleWrapper in
theorem wrapper_len_selected : Local lenRegistry context lenRoot (.selected 30 []) := by
  refine .selected ⟨wrapper_len_survivor.1,wrapper_len_not_K2,?_,?_⟩ ⟨wrapper_len_survivor,?_⟩
  · rintro ⟨_,declaration,visible,_,_,_,bounds,located,visited,member,cycle⟩
    have same := List.mem_singleton.mp visible; subst declaration
    have found : GeneralNominalRecursiveCandidates.arguments context lenRoot = some [(1,1)] := by decide +kernel
    have same := Option.some.inj (found.symm.trans located); subst bounds
    rw [wrapper_inspected] at member
    have same := List.mem_singleton.mp member; subst visited
    exact list_off_cycle (recurs_cycle _ _ cycle)
  · rintro (old | ⟨_,old⟩)
    · obtain ⟨_,declaration,visible,_,_,_,notPrepared⟩ := old
      have same := List.mem_singleton.mp visible; subst declaration; exact notPrepared wrapper_prepared
    · rcases old with ⟨old,_⟩ | ⟨old,_⟩
      · obtain ⟨_,_,index,slot,equal,cycle⟩ := old
        have same : slot = 1 := Fin.ext equal; subst slot
        exact GeneralNominalMixedRecurrence.nominal_not_recursive state 1 descriptor rfl cycle
      · obtain ⟨_,declaration,visible,_,_,_,bounds,located,visited,member,cycle⟩ := old
        have same := List.mem_singleton.mp visible; subst declaration
        have found : GeneralNominalRecursiveCandidates.arguments context lenRoot = some [(1,1)] := by decide +kernel
        have same := Option.some.inj (found.symm.trans located); subst bounds
        rw [wrapper_inspected] at member
        have same := List.mem_singleton.mp member; subst visited
        exact GeneralNominalMixedRecurrence.nominal_not_recursive state 1 descriptor rfl cycle
  · intro key children survivor
    have original := survivor
    obtain ⟨_,declaration,visible,_,identity,_⟩ := survivor
    have same := List.mem_singleton.mp visible; subst declaration
    have same : key = 30 := identity.symm; subst key
    refine ⟨rfl,GeneralNominalRecursiveCandidates.survivor_children_functional _ ?_ _ _ _ _ _ original wrapper_len_survivor⟩
    exact ⟨by decide +kernel,by intro d hd; have same := List.mem_singleton.mp hd; subst d; exact len_checked⟩

end Yulang.GeneralNominalCycleRegressions
