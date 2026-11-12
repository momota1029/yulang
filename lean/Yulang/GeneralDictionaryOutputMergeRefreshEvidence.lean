import Yulang.GeneralDictionaryOutputMergeRefresh

/-! Full root evidence in the actual enlarged post-refresh context. -/
namespace Yulang.GeneralDictionaryOutputMergeRefreshEvidence
open GeneralDictionaryOutputMergeRefresh GeneralDictionaryOutputMergeSuccess
open GeneralNominalExamples (displayRoot listDescriptor)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open GeneralNominalSaturationState GeneralDeclarations GeneralDeclarationPatterns
open GeneralNominalCommonBridge (Assignment)

theorem query : GeneralNominalInspection.queries snapshot refreshedContext.interpretation declaration =
    [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem schema : generated registry refreshedContext displayRoot declaration checked [((0 : Fin 4),0)] =
    {tests := [(.source (outputTarget 10),.scalar .int),(.source (outputTarget 11),.scalar .int)]} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration from (by simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,declaration,List.mergeSort_pair])]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,normalize,normalizeArgs,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,outputTarget,GeneralNominalAllocation.allocation,
    GeneralDeclarationDemands.outputTarget,Declaration.outputNames]
  exact ⟨rfl,rfl⟩

theorem parent_branch (m : Assignment) (valid : Models refreshed.current m) :
    BranchModels registry refreshedContext displayRoot declaration checked [((0 : Fin 4),0)] m := by
  have p := private_models refreshedContext registry displayRoot declaration 0 descriptor rfl 0 rfl (1,1) rfl query m valid.1
  refine ⟨p.1,p.2,?_⟩
  rw [schema]
  refine ⟨?_,by simp,by simp,by simp⟩
  intro test member
  rcases List.mem_cons.mp member with eq | member
  · rw [eq]
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed; cases observed
    exact GeneralDictionaryOutputMergeAllModels.output_scalar m
      ((GeneralDictionaryOutputMergeFeedback.next_models m).mp ((models_exact m).mp valid)) 10 (Or.inl rfl)
  · rw [List.mem_singleton.mp member]
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed; cases observed
    exact GeneralDictionaryOutputMergeAllModels.output_scalar m
      ((GeneralDictionaryOutputMergeFeedback.next_models m).mp ((models_exact m).mp valid)) 11 (Or.inr rfl)

theorem parent_report : report refreshedContext declaration [((0 : Fin 4),0)] =
    captured snapshot (0 : Fin 4) 0 0 (1,1) :=
  report_exact refreshedContext declaration 0 descriptor rfl 0 (1,1) rfl query

theorem parent_instance (m : Assignment) (valid : Models refreshed.current m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext m displayRoot 1 [child 10,child 11] := by
  refine ⟨declaration,by simp,checked,rfl,rfl,[((0 : Fin 4),0)],?_,?_,?_,?_,?_,parent_branch m valid⟩
  · decide +kernel
  · rw [parent_report]; exact ⟨rfl,rfl,rfl⟩
  · refine ⟨(by intro _ h; cases h),?_⟩; rw [schema]
  · unfold GeneralNominalAllocation.children
    rw [parent_report]
    have old := children_exact.symm
    unfold children GeneralNominalAllocation.children at old
    rw [report_exact (GeneralNominalExamples.context true) declaration 0 listDescriptor rfl 0 (1,1) rfl GeneralDictionaryOutputMergeSuccess.query] at old
    exact old
  · exact prepared.1

open GeneralDictionaryRecursiveEvidence (Instance)
theorem refreshed_terminal_report :
    report refreshedContext terminal [((1 : Fin 4),1)] =
      {captures := [⟨0,(1,1),none⟩],checked := [(1,1),(1,1)]} := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,inspectMany,inspect,Report.append]

theorem refreshed_terminal_schema (n : Nat) :
    generated registry refreshedContext (child n) terminal terminal_checked [((1 : Fin 4),1)] =
      {tests := [(.source (outputTarget n),.scalar .int)]} := by
  unfold generated GeneralNominalMaterialization.requests
  rw [GeneralDictionaryJointMergeExample.emissions_empty]
  simp [GeneralNominalMaterialization.rootRequests,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,normalize,normalizeArgs,
    GeneralNominalExamples.interpretation]

theorem terminal_branch (m : Assignment) (valid : Models refreshed.current m)
    (n : Nat) (which : n = 10 ∨ n = 11) :
    BranchModels registry refreshedContext (child n) terminal terminal_checked [((1 : Fin 4),1)] m := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [refreshed_terminal_report]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨valid.1,?_,?_⟩
      · intro first one last two _
        have a := List.mem_singleton.mp one
        have b := List.mem_singleton.mp two
        subst first; subst last
        exact CommonNominalFullCarrier.subtype_refl _
      · simp [GeneralNominalAllocation.merges,bindings,GeneralNominalAllocation.occurrences,
          Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All,PresenceNormalForm.Atom.Holds,
        CommonNominalFullCarrier.model,CommonNominalFullCarrier.subtype_refl]
  · rw [refreshed_terminal_report]
    simp [ProjectionModels]
  · rw [refreshed_terminal_schema]
    refine ⟨?_,by simp,by simp,by simp⟩
    intro test member
    have eq := List.mem_singleton.mp member; subst test
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observation
    cases observation
    exact GeneralDictionaryOutputMergeAllModels.output_scalar m
      ((GeneralDictionaryOutputMergeFeedback.next_models m).mp ((models_exact m).mp valid)) n which

theorem terminal_instance (m : Assignment) (valid : Models refreshed.current m)
    (n : Nat) (which : n = 10 ∨ n = 11) :
    Instance registry refreshedContext m (child n) 7 [] := by
  refine ⟨terminal,by simp,terminal_checked,rfl,rfl,[((1 : Fin 4),1)],?_,?_,?_,?_,prepared.1,
    terminal_branch m valid n which⟩
  · change arguments refreshedContext (GeneralDictionaryJointMergeExample.root 0 0) = some [((1 : Fin 4),1)]
    decide +kernel
  · rw [refreshed_terminal_report]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      have eq := List.mem_singleton.mp member; subst output
      exact ⟨GeneralDictionaryJointMergeExample.outputEquation,by simp,rfl⟩
    · rw [refreshed_terminal_schema]
  · unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
    rw [GeneralDictionaryJointMergeExample.emissions_empty]
    rfl




/-- All three ordered source dictionary nodes remain valid for every model,
now in the actual post-refresh context, not just the historical context. -/
theorem full_dictionary (m : Assignment) (valid : Models refreshed.current m) :
    GeneralDictionaryRecursiveEvidence.Evidence registry refreshedContext m displayRoot
      GeneralDictionaryOutputMergeRootEvidence.rootPayload := by
  apply GeneralDictionaryRecursiveEvidence.evidence_node registry refreshedContext m displayRoot 1
    [child 10,child 11] [.node 7 [],.node 7 []] (parent_instance m valid)
  exact .cons (GeneralDictionaryRecursiveEvidence.evidence_node registry refreshedContext m (child 10) 7 [] []
      (terminal_instance m valid 10 (Or.inl rfl)) .nil)
    (.cons (GeneralDictionaryRecursiveEvidence.evidence_node registry refreshedContext m (child 11) 7 [] []
      (terminal_instance m valid 11 (Or.inr rfl)) .nil) .nil)


/-- Reachability, exact model preservation, simultaneous output observations,
and the complete source dictionary coexist at the actual enlarged context. -/
theorem reachable_refresh_full_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
      registry displayRoot refreshed ∧
    GeneralNominalSupportSteps.SourceFormed registry displayRoot refreshed ∧
    Models refreshed.current GeneralNominalExamples.model ∧
    GeneralNominalState.Known snapshot (outputTarget 10) ∧
    GeneralNominalState.Known snapshot (outputTarget 11) ∧
    (∀ m, Models refreshed.current m ↔ Models GeneralDictionaryOutputMergeFeedback.next.current m) ∧
    ∀ m, Models refreshed.current m → GeneralDictionaryRecursiveEvidence.Evidence registry
      refreshed.current.context m displayRoot GeneralDictionaryOutputMergeRootEvidence.rootPayload :=
  ⟨GeneralDictionaryOutputMergeRefresh.reachable,sourceformed,inhabited,output_known,output_known11,
    models_exact,full_dictionary⟩

end Yulang.GeneralDictionaryOutputMergeRefreshEvidence
