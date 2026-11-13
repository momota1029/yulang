import Yulang.GeneralDictionaryScalarChildIntervals
import Yulang.GeneralDictionaryMixedCatalogInhabited

/-! A checked scalar compound child with a real emitted two-endpoint demand
and a positive packet model. This example does not assert operational reachability. -/
namespace Yulang.GeneralDictionaryScalarChildExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot interpretation)
abbrev clause : Clause := ⟨10,0,[.app 2 []],[]⟩
abbrev declaration : Declaration := { GeneralDeclarationExamples.display with requirements := [clause] }
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro c h; have eq := List.mem_singleton.mp h; subst c; exact ⟨rfl,rfl⟩
  · intro c h; have eq := List.mem_singleton.mp h; subst c
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro c h; have eq := List.mem_singleton.mp h; subst c
    unfold ConservativeSmaller; decide +kernel
  · intro c h; have eq := List.mem_singleton.mp h; subst c
    intro capture
    simp [Smaller,counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size,Roles.argsOccurrences,Roles.Term.occurrences]
    cases (normalize (capture 0)).encode <;> simp [Roles.Term.size] <;> omega

abbrev packet : Packet roles := ⟨registry,context true,GeneralNominalDemandMerging.pointSite displayRoot,declaration,checked,[(0,0)]⟩
abbrev signature : clause.Signature roles := checked.signature.2.2.2 clause (by simp)
abbrev child := GeneralNominalFeedbackSites.clauseChild packet clause signature

abbrev endpoint (purpose : Nat) : Nat := GeneralNominalAllocation.source (state true) registry 100
  (GeneralNominalAllocation.origin 100 1 purpose 10 0)

theorem endpoint_nonzero (purpose : Nat) : endpoint purpose ≠ 0 := by
  have positive := GeneralNominalIdentities.source_above_seed (state true).seed
    (GeneralNominalAllocation.origin 100 1 purpose 10 0)
  unfold endpoint GeneralNominalAllocation.source
  omega

theorem endpoints_distinct : endpoint 3 ≠ endpoint 4 := by
  intro eq
  have same := (GeneralNominalAllocation.source_identity (state true) registry 100 _ _).mp eq
  have := congrArg (fun o : GeneralNominalAllocation.Origin => o.2.2.1) same
  contradiction

theorem query : GeneralNominalInspection.queries (state true) interpretation declaration = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation]

theorem schema_exact : GeneralNominalPacketSupport.namedSchema packet =
    { tests := [(.source (endpoint 3),.scalar .int),(.source (endpoint 4),.scalar .int)] } := by
  unfold GeneralNominalPacketSupport.namedSchema generated GeneralNominalMaterialization.requests
  unfold GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration from (by simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,declaration])]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,normalize,normalizeArgs,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,interpretation,GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,
    GeneralNominalAllocation.allocation,endpoint,GeneralNominalDemandMerging.pointSite,displayRoot]

theorem branch : packet.Holds model := by
  have privateModel := private_models (context true) registry displayRoot declaration 0 listDescriptor rfl 0 rfl
    (1,1) rfl query model (state_models true)
  refine ⟨privateModel.1,privateModel.2,?_⟩
  change GeneralNominalMaterialization.Models (state true) declaration (GeneralNominalPacketSupport.capture packet)
    (report (context true) declaration [(0,0)]) (GeneralNominalPacketSupport.namedSchema packet) model
  rw [schema_exact]
  refine ⟨?_,by simp,by simp,by simp⟩
  intro test member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed; cases observed
    simp only [Test.Holds,endpoint_nonzero]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem actual_child_order (index : Fin (roles child.demand.role).arity) :
    CommonNominalFullCarrier.Subtype (model (child.demand.arguments index).1).1
      (model (child.demand.arguments index).2).1 :=
  GeneralDictionaryScalarChildIntervals.clause_scalar_order packet clause (by simp) signature index .int 2
    (by have eq : index.val = 0 := Fin.val_eq_zero (show Fin 1 from index); simp [eq,clause,normalize,normalizeArgs]) rfl model branch

theorem child_member : child ∈ packet.children := by
  apply List.mem_map.mpr
  refine ⟨_,?_,rfl⟩
  apply (GeneralCanonicalChildOrder.canonicalEmit_perm ..).mem_iff.mp
  exact List.mem_map.mpr ⟨⟨clause,by simp⟩,by simp,rfl⟩

theorem endpoints_exact (index : Fin (roles child.demand.role).arity) :
    child.demand.arguments index = (endpoint 3,endpoint 4) := by
  have eq : index.val = 0 := Fin.val_eq_zero (show Fin 1 from index)
  simp [child,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,clause,normalize,normalizeArgs,eq,
    GeneralNominalFeedbackSites.frame,GeneralNominalAllocation.frame,GeneralNominalAllocation.allocation,endpoint,GeneralNominalDemandMerging.pointSite,displayRoot]

theorem nonvacuous_emitted_order : packet.Holds model ∧ child ∈ packet.children ∧
    ∀ index, (child.demand.arguments index).1 ≠ (child.demand.arguments index).2 ∧
      CommonNominalFullCarrier.Subtype (model (child.demand.arguments index).1).1
        (model (child.demand.arguments index).2).1 := by
  refine ⟨branch,child_member,?_⟩
  intro index
  exact ⟨by rw [endpoints_exact]; exact endpoints_distinct,actual_child_order index⟩

end Yulang.GeneralDictionaryScalarChildExample
