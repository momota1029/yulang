import Yulang.GeneralDictionarySemanticCollapseAllocationExample
import Yulang.GeneralDictionarySemanticCollapseBranch

/-! Full terminal branch replay with a positive reachable collapse witness. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionarySemanticCollapseBranchExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionarySemanticCollapseExample
open GeneralDictionarySemanticCollapse
open CommonNominalFullCarrier
abbrev roles := GeneralDeclarationExamples.roles
abbrev declaration : Declaration := ⟨31,0,[.app 0 [.app 0 [.var 7]]],[],[],[]⟩
abbrev registry : Registry := ⟨source.constructors,roles,[declaration]⟩
abbrev context := start.context
abbrev bounds : List (GeneralNominalInspection.Bounds source) := [(0,0)]

theorem checked : DeclarationChecked registry.constructors roles declaration := by
 constructor
 · simp [Declaration.Signature,Clause.Signature,Declared,roles,GeneralDeclarationExamples.roles,GeneralDeclarationExamples.bareRole,declaration]
 · simp [Declaration.Identified,Declaration.outputNames,declaration]
 · simp [Declaration.Produced,declaration]
 · simp [Declaration.OutputOnly,Declaration.outputNames,declaration]
 · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,declaration,
    normalizeArgs,normalize,variablesArgs,Pattern.variables]
 · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,declaration,registry,source,
    GeneralDeclarationExamples.constructors]
 · intro _ h; cases h
 · intro _ h; cases h
 · intro _ h; cases h
 · intro _ h; cases h

theorem queries : GeneralNominalInspection.queries source interpretation declaration = [query shape] := by
 simp [GeneralNominalInspection.queries,declaration,Declaration.normalHead,normalizeArgs,normalize,
   GeneralNominalInspection.translate,interpretation,source,GeneralDeclarationExamples.constructors,query,shape]

theorem report_exact : report context declaration bounds =
 GeneralDictionarySemanticCollapseBranch.oldRootReport shape :=
 (GeneralDictionarySemanticCollapseBranch.reports shape declaration queries).1

theorem captured : bindings source (report context declaration bounds) = [(7,3,3),(7,3,3)] := by
 rw [report_exact]
 rfl

theorem private_models : GeneralNominalState.Models
 (privateState registry context root declaration bounds) model := by
 unfold privateState
 apply (GeneralNominalState.extend_models ..).mpr
 constructor
 · rw [captured]
   exact GeneralDictionarySemanticCollapseAllocationExample.old_propagation registry root.identity declaration rfl
 · unfold selfChecks
   rw [report_exact]
   change PresenceNormalForm.All CommonNominalFullCarrier.model model
    ([(0,0),(0,0),(1,2),(3,3),(3,3)].map fun pair =>
      PresenceNormalForm.Atom.tyLe (.var pair.1) (.var pair.2))
   intro atom member
   simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl
   all_goals exact subtype_refl _

theorem generated_empty : generated registry context root declaration checked bounds = {} := by
 unfold generated
 rw [GeneralDictionarySemanticCollapseBranch.terminal_requests _ _ _ _ _ _ rfl]
 rfl

theorem old_branch : BranchModels registry context root declaration checked bounds model := by
 refine ⟨private_models,?_,?_⟩
 · rw [report_exact]
   have h := old_projection
   change ProjectionModels start.context.state (inspect start.context.state (query shape) (shape.root,shape.root) none) model at h
   rw [before_exact] at h
   exact h
 · rw [generated_empty]
   exact GeneralNominalMaterialization.empty_models _ _ _ _ _

theorem current_branch : BranchModels registry
 (GeneralDictionarySemanticCollapseBranch.currentContext revision) root declaration checked bounds model := by
 apply GeneralDictionarySemanticCollapseBranch.branch shape registry root declaration checked queries rfl rfl rfl rfl
 · change ∀ entry ∈ (generated registry context root declaration checked bounds).variables, _
   rw [generated_empty]
   intro entry member
   cases member
 · exact old_branch
 · exact revised_models

theorem old_consistent : Consistent registry context root declaration checked bounds :=
 ⟨model,old_branch⟩

theorem current_consistent : Consistent registry
 (GeneralDictionarySemanticCollapseBranch.currentContext revision) root declaration checked bounds :=
 ⟨model,current_branch⟩

theorem source_formed : GeneralNominalValueSteps.SourceFormed registry root revisedTracked := by
 have initial : GeneralNominalSourceFormation.InitialSource registry context root := by
   refine ⟨rfl,⟨rfl,?_⟩,initial_source.linked,initial_source.intervals,initial_source.below_seed,rfl⟩
   intro name primitive found; cases found
 apply GeneralNominalValueSteps.SourceFormed.update
   (GeneralNominalValueSteps.SourceFormed.initial context initial)
 exact ⟨root,.root,.administrative root revision.result (.reobserve root revision certified improves)⟩

theorem reachable_branch_replay :
 GeneralNominalValueSteps.SourceFormed registry root revisedTracked ∧
 GeneralNominalReobservationSteps.Step registry root start revision.result ∧
 BranchModels registry context root declaration checked bounds model ∧
 BranchModels registry (GeneralDictionarySemanticCollapseBranch.currentContext revision)
   root declaration checked bounds model :=
 ⟨source_formed,actual_reobserve,old_branch,current_branch⟩

noncomputable abbrev currentContext := GeneralDictionarySemanticCollapseBranch.currentContext revision

theorem located : arguments context root = some bounds := by decide +kernel

theorem prepared : Prepared registry context root declaration checked := by
 refine ⟨⟨rfl,?_⟩,initial_source.linked,?_,bounds,located,?_,?_,old_consistent⟩
 · intro name primitive found; cases found
 · intro key member collision
   have bound := GeneralNominalAllocation.member_le_max _ _ collision
   have below : (GeneralNominalState.sources source).foldr max 0 = source.seed := by decide +kernel
   rw [below] at bound
   exact False.elim ((GeneralNominalAllocation.source_initial_fresh source registry root.identity key _ bound) rfl)
 · rw [report_exact]
   exact ⟨rfl,rfl,rfl⟩
 · constructor
   · intro output member; cases member
   · rw [generated_empty]

theorem current_generated_empty : generated registry currentContext root declaration checked bounds = {} := by
 unfold generated
 rw [GeneralDictionarySemanticCollapseBranch.terminal_requests _ _ _ _ _ _ rfl]
 rfl

theorem current_report : report currentContext declaration bounds =
 GeneralDictionarySemanticCollapseBranch.newRootReport shape :=
 (GeneralDictionarySemanticCollapseBranch.reports shape declaration queries).2

theorem current_located : arguments currentContext root = some bounds := by rfl

theorem current_prepared : Prepared registry currentContext root declaration checked := by
 refine ⟨⟨rfl,?_⟩,?_,?_,bounds,current_located,?_,?_,current_consistent⟩
 · intro name primitive found; cases found
 · exact initial_source.linked
 · intro key member collision
   have bound := GeneralNominalAllocation.member_le_max _ _ collision
   have below : (GeneralNominalState.sources currentContext.state).foldr max 0 = currentContext.state.seed := by decide +kernel
   rw [below] at bound
   exact False.elim ((GeneralNominalAllocation.source_initial_fresh currentContext.state registry root.identity key _ bound) rfl)
 · rw [current_report]
   exact ⟨rfl,rfl,rfl⟩
 · constructor
   · intro output member; cases member
   · rw [current_generated_empty]

theorem children_empty (state : GeneralNominalState.State) (captures : GeneralNominalAllocation.Bindings) :
 GeneralNominalAllocation.children state registry root declaration checked captures = [] := by
 have emitted := GeneralCanonicalChildOrder.canonicalEmit_perm root.identity declaration checked
   (GeneralNominalAllocation.capture state registry root.identity declaration.id captures)
   (GeneralNominalAllocation.allocation state registry root.identity declaration.id)
 have empty : GeneralDeclarationDemands.emitAll root.identity declaration checked.signature
   (GeneralNominalAllocation.capture state registry root.identity declaration.id captures)
   (GeneralNominalAllocation.allocation state registry root.identity declaration.id) = [] := rfl
 rw [empty] at emitted
 unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
 simp only [GeneralNominalAllocation.frame]
 rw [← List.Perm.nil_eq emitted]
 rfl

theorem survivor : Survivor registry context root declaration.id [] := by
 refine ⟨?_,declaration,by simp [registry],checked,rfl,rfl,bounds,located,prepared,?_⟩
 · rintro ⟨index,unknown⟩
   exact unknown ⟨0,rfl,Or.inr ⟨outer,rfl⟩⟩
 · exact (children_empty _ _).symm

theorem current_survivor : Survivor registry currentContext root declaration.id [] := by
 refine ⟨?_,declaration,by simp [registry],checked,rfl,rfl,bounds,current_located,current_prepared,?_⟩
 · rintro ⟨index,unknown⟩
   exact unknown ⟨(0 : Fin 4),rfl,Or.inr ⟨point,rfl⟩⟩
 · exact (children_empty _ _).symm

end Yulang.GeneralDictionarySemanticCollapseBranchExample
