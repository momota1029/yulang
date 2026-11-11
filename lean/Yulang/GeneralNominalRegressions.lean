import Yulang.GeneralNominalExamples

/-! Existing unresolved, normalized-shadow and recursive examples transported
to the full nominal state. Unsupported nominal parameter observations remain
pending rather than being converted into an empty-candidate rejection. -/
namespace Yulang.GeneralNominalRegressions


open GeneralSourceStateExamples GeneralSourceK2Examples

abbrev constructors := GeneralDeclarationExamples.constructors
abbrev indexState' := GeneralNominalState.embed indexState indexView constructors
abbrev loopState' := GeneralNominalState.embed loopState loopView constructors
abbrev shadowState' := GeneralNominalState.embed shadowState shadowView constructors

theorem index_pending : GeneralNominalState.RootPending indexState' indexDemand := by
  apply (GeneralNominalState.embed_pending ..).mpr
  obtain ⟨index, _, unknown⟩ := index_pending_not_rootK2.2.2.1
  exact ⟨index,GeneralDeclarationDemands.every_input_needed indexDemand index,unknown⟩

theorem index_not_K2 : ¬ GeneralNominalState.RootK2 indexState' indexDemand :=
  GeneralNominalState.pending_excludes_K2 _ _ index_pending

theorem index_all_common_assignments (key : Common.Ty) :
    GeneralNominalState.Models indexState' (GeneralNominalCommonBridge.lift (indexModel key)) :=
  (GeneralNominalState.embed_models ..).mpr (index_pending_not_rootK2.2.1 key)

theorem shadow_pending : GeneralNominalState.RootPending shadowState' loopDemand := by
  apply (GeneralNominalState.embed_pending ..).mpr
  obtain ⟨index, _, unknown⟩ := shadow_not_rootK2.2.2.1
  exact ⟨index,GeneralDeclarationDemands.every_input_needed loopDemand index,unknown⟩

theorem shadow_not_K2 : ¬ GeneralNominalState.RootK2 shadowState' loopDemand :=
  GeneralNominalState.pending_excludes_K2 _ _ shadow_pending

theorem loop_K2 : GeneralNominalState.RootK2 loopState' loopDemand := by
  refine ⟨GeneralNominalState.linked_embed _ _ _ _ loop_rootK2.1, ?_, ?_⟩
  · rintro ⟨index,unknown⟩
    apply unknown
    refine ⟨⟨0,by decide +kernel⟩,rfl,Or.inl ?_⟩
    simp [loopState', GeneralNominalState.embed, GeneralNormalizedObservation.Snapshot.graph, GeneralNormalizedObservation.Head.node]
  · obtain ⟨_,_,_,index,slot,equal,complete,cycle⟩ := loop_rootK2.2.2.1
    exact ⟨index,slot,equal,complete,cycle⟩

theorem loop_model : GeneralNominalState.Models loopState'
    (GeneralNominalCommonBridge.lift loopModel) :=
  (GeneralNominalState.embed_models ..).mpr loop_rootK2.2.1

theorem shadow_normalization_full (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models shadowState' model) :
    GeneralNominalCommonBridge.ObservationModels shadowView model :=
  GeneralNominalState.normalized_models _ _ models

open GeneralDeclarations GeneralDeclarationPatterns
open GeneralNominalExamples (state context displayRoot)

abbrev concreteList : Declaration := ⟨4,0,[.app 0 [.app 2 []]],[],[],[]⟩
abbrev concreteRegistry : Registry := ⟨constructors,GeneralDeclarationExamples.roles,[concreteList]⟩

theorem concrete_checked : DeclarationChecked constructors GeneralDeclarationExamples.roles concreteList := by
  constructor
  · simp [Declaration.Signature, GeneralDeclarationExamples.roles, GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames]
  · simp [Declaration.Scoped, Declaration.inputNames, Declaration.outputNames, normalizeArgs, normalize,
      variablesArgs, Pattern.variables]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped, constructors,
      GeneralDeclarationExamples.constructors]
  · simp
  · simp
  · simp
  · simp

theorem unresolved_payload_report : GeneralNominalCandidates.report (context false) concreteList [(0,0)] =
    { inspected := [(0,0),(0,0),(1,1)], blocked := [(1,1)] } := by
  unfold GeneralNominalCandidates.report
  have translated : GeneralNominalInspection.queries (state false) GeneralNominalExamples.interpretation concreteList =
      [.nominal 0 [.scalar .int]] := by
    simp [GeneralNominalInspection.queries, Declaration.normalHead, normalizeArgs, normalize,
      GeneralNominalInspection.translate, GeneralNominalExamples.interpretation]
  rw [translated]
  repeat first
    | rw [GeneralNominalInspection.inspectMany.eq_2]
    | rw [GeneralNominalInspection.inspectMany.eq_1]
    | rw [GeneralNominalInspection.inspect.eq_3]
    | rw [GeneralNominalInspection.inspect.eq_4]
    | simp [GeneralNominalInspection.typeArguments, GeneralNominalInspection.Report.visit,
        GeneralNominalInspection.Report.append, GeneralNominalInspection.block]

theorem inspection_pending : GeneralNominalCandidates.InspectionPending concreteRegistry (context false) displayRoot := by
  have ready : ¬ GeneralNominalState.RootPending (state false) displayRoot.demand := by
    rintro ⟨index,unknown⟩
    exact unknown ⟨0,rfl,Or.inr ⟨GeneralNominalExamples.listDescriptor,rfl⟩⟩
  have located : GeneralNominalCandidates.arguments (context false) displayRoot = some [(0,0)] := by decide +kernel
  refine ⟨ready,concreteList,by simp,concrete_checked,rfl,?_,?_⟩
  · rintro ⟨_,_,bounds,found,blocked,_⟩
    have same := Option.some.inj (located.symm.trans found)
    subst bounds
    rw [unresolved_payload_report] at blocked
    cases blocked
  · rintro ⟨_,_,_,bounds,found,finished,_⟩
    have same := Option.some.inj (located.symm.trans found)
    subst bounds
    rw [unresolved_payload_report] at finished
    cases finished.1

theorem different_parameter_endpoints_defer (first last : Fin slots) (different : first ≠ last) :
    GeneralNominalInspection.typeArguments [.type (first,last)] = none := by
  simp [GeneralNominalInspection.typeArguments,different]

abbrev conflictState := GeneralNominalState.embed indexAfter GeneralCandidateConflictExamples.afterView constructors
abbrev conflictContext : GeneralNominalCandidates.Context := ⟨conflictState,GeneralNominalExamples.interpretation⟩
abbrev conflicting : GeneralNominalAllocation.Bindings := [(0,(0,0)),(0,(1,1))]

theorem cross_conflict : ¬ ∃ model, GeneralNominalState.Models conflictState model ∧
    GeneralNominalAllocation.Compatible conflicting model := by
  rintro ⟨model,models,compatible⟩
  have str := models.1.2.1 (0 : Fin 3) (.base .str) rfl
  have int := models.1.2.1 (1 : Fin 3) (.base .int) rfl
  have cross := compatible (0,(0,0)) (by decide +kernel) (0,(1,1)) (by decide +kernel) rfl
  have impossible : CommonNominalFullCarrier.Subtype (.base .str) (.base .int) :=
    CommonNominalFullCarrier.subtype_trans str.2 (CommonNominalFullCarrier.subtype_trans cross int.1)
  have old : Common.Subtype (.base .str) (.base .int) :=
    (CommonNominalFullModelMap.subtype_exact _ _).mp impossible
  cases (CommonRigidHeadInspection.base_iff .str .int).mp old

theorem repeated_captures : GeneralNominalInspection.bindings conflictState
    (GeneralNominalCandidates.report conflictContext GeneralCandidateConflictExamples.repeated ([(0,0),(1,1)] : List (Fin 3 × Fin 3))) = conflicting := by
  simp [GeneralNominalInspection.bindings, GeneralNominalCandidates.report, GeneralNominalInspection.queries,
    Declaration.normalHead, normalizeArgs, normalize, GeneralNominalInspection.translate]
  repeat first
    | rw [GeneralNominalInspection.inspectMany.eq_2]
    | rw [GeneralNominalInspection.inspectMany.eq_1]
    | rw [GeneralNominalInspection.inspect.eq_1]
  rfl

theorem no_conflict_survivors (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles)) :
    ¬ GeneralNominalCandidates.Survivor GeneralCandidateConflictExamples.registry conflictContext
      GeneralCandidateConflictExamples.root key children := by
  rintro ⟨_,declaration,visible,checked,_,_,_,_,prepared,_⟩
  have same := List.mem_singleton.mp visible
  subst declaration
  obtain ⟨_,_,_,bounds,located,_,_,consistent,_⟩ := prepared
  obtain ⟨model,models⟩ := consistent
  have located' : GeneralNominalCandidates.arguments conflictContext GeneralCandidateConflictExamples.root =
      some ([(0,0),(1,1)] : List (Fin 3 × Fin 3)) := by decide +kernel
  have same := Option.some.inj (located'.symm.trans located)
  subst bounds
  have valid := (GeneralNominalAllocation.propagate_models ..).mp models
  apply cross_conflict
  refine ⟨model,valid.1,?_⟩
  have compatible := valid.2.1
  rw [repeated_captures] at compatible
  exact compatible

end Yulang.GeneralNominalRegressions
