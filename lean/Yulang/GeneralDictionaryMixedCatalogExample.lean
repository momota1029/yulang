import Yulang.GeneralDictionaryRequestCatalog
import Yulang.GeneralDictionaryVariableJournalMerge
import Yulang.GeneralDictionaryOutputMergeSuccess
/-! Nonempty repeated-binder historical packet example. The exhibited assignment
uses int at both outputs; no source-formed reachability is claimed. -/
namespace Yulang.GeneralDictionaryMixedCatalogExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot interpretation)
abbrev firstClause : Clause := ⟨10,1,[.var 0],[⟨30,0,.app 2 []⟩]⟩
abbrev secondClause : Clause := ⟨11,1,[.var 0],[⟨31,0,.var 0⟩]⟩
abbrev declaration : Declaration := { GeneralDeclarationExamples.display with
  requirements := [firstClause, secondClause] }
abbrev terminal := GeneralDictionaryJointMergeExample.terminal
abbrev terminal_checked := GeneralDictionaryJointMergeExample.terminal_checked
abbrev registry : Registry := ⟨constructors, roles, [declaration,terminal]⟩

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,by simp,?_,?_⟩
    · intro name body impossible; cases impossible
    · intro clause member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      all_goals
        refine ⟨rfl,?_⟩
        intro equation member
        have eq := List.mem_singleton.mp member; subst equation
        exact ⟨none,rfl⟩
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames]
  · simp [Declaration.Scoped, Declaration.inputNames, Declaration.outputNames, normalizeArgs, normalize, variablesArgs, Pattern.variables]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped, constructors]
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact ⟨rfl,rfl⟩
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> (unfold ConservativeSmaller; decide +kernel)
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact unary_descent 0 0


abbrev packet : Packet roles :=
  ⟨registry,context true,GeneralNominalDemandMerging.pointSite displayRoot,declaration,checked,[(0,0)]⟩
abbrev journal : State roles := ⟨context true,[packet],[],[],[]⟩
abbrev tracked : GeneralNominalSupport.Tracked roles := ⟨context true,journal,[]⟩
abbrev target (clause : Nat) : Nat := GeneralNominalAllocation.source (state true) registry 100
  (GeneralNominalAllocation.origin 100 1 5 (clause+20) 0)
abbrev closedRequest : GeneralNominalMaterialization.Request := ⟨.app 2 [],target 10,.actual⟩
abbrev openRequest : GeneralNominalMaterialization.Request := ⟨.var 0,target 11,.actual⟩

theorem emissions : GeneralDictionaryReachableRequestHistory.emitted packet = [closedRequest,openRequest] := by
  unfold GeneralDictionaryReachableRequestHistory.emitted GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration from (by simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,declaration,List.mergeSort_pair])]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,normalize,
    target,GeneralNominalAllocation.allocation,GeneralDeclarationDemands.outputTarget,Declaration.outputNames,
    closedRequest,openRequest,GeneralNominalDemandMerging.pointSite,displayRoot]

theorem closed : (GeneralNominalMaterialization.generated (state true) interpretation [closedRequest]).variables = [] := by
  simp [GeneralNominalMaterialization.generated,closedRequest,GeneralNominalInspection.translate,
    interpretation,normalize,normalizeArgs,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append]

theorem mixed : (GeneralNominalPacketSupport.namedSchema packet).variables ≠ [] := by
  change (GeneralNominalMaterialization.generated (state true) interpretation
    (GeneralDictionaryReachableRequestHistory.emitted packet)).variables ≠ []
  rw [emissions]
  simp [GeneralNominalMaterialization.generated,closedRequest,openRequest,
    GeneralNominalInspection.translate,interpretation,normalize,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append]

theorem old_catalog_empty : GeneralDictionaryReachableRequestHistory.safeCatalog tracked = [] := by
  simp [GeneralDictionaryReachableRequestHistory.safeCatalog,
    GeneralDictionaryReachableRequestHistory.eligible,mixed]

theorem new_catalog_contains : closedRequest ∈ GeneralDictionaryRequestCatalog.catalog tracked := by
  apply (GeneralDictionaryRequestCatalog.member_iff tracked closedRequest).mpr
  exact ⟨packet,by simp,by rw [emissions]; exact List.mem_cons_self,closed⟩

theorem generated_exact : GeneralNominalPacketSupport.namedSchema packet =
    {variables := [⟨0,.source (target 11),.actual⟩],
     tests := [(.source (target 10),.scalar .int)]} := by
  change GeneralNominalMaterialization.generated (state true) interpretation
    (GeneralDictionaryReachableRequestHistory.emitted packet) = _
  rw [emissions]
  simp [GeneralNominalMaterialization.generated,closedRequest,openRequest,
    GeneralNominalInspection.translate,interpretation,normalize,normalizeArgs,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append]

/-- A checked mixed packet is a concrete witness to strict syntactic coverage.
This example asserts no operational reachability of the constructed journal. -/
theorem strict_coverage :
    closedRequest ∈ GeneralDictionaryRequestCatalog.catalog tracked ∧
    closedRequest ∉ GeneralDictionaryReachableRequestHistory.safeCatalog tracked := by
  exact ⟨new_catalog_contains,by rw [old_catalog_empty]; simp⟩
end Yulang.GeneralDictionaryMixedCatalogExample
