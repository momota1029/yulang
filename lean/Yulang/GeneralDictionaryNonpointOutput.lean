import Yulang.GeneralDictionaryNonpointExample

/-! A nonempty actual-mode associated-root schema across nonpoint capture
collapse. This proves private branch/model transport, not operational output
installation or a certified revision. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionaryNonpointOutput
open GeneralDictionaryNonpointExample
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseSchema
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalMaterialization
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
abbrev declaration : Declaration := ⟨31,1,[.app 0 [.app 0 [.var 7]]],[],[⟨43,0,.var 7⟩],[]⟩
abbrev registry : Registry := ⟨source.constructors,roles,[declaration]⟩
abbrev outputRoot : GeneralSourceDictionaries.Occurrence roles :=
 ⟨0,⟨1,fun _ => (0,0),[⟨0,4⟩],by intro output member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩⟩
abbrev body : Schema := ⟨[⟨7,.source 4,.actual⟩],[],false⟩

theorem checked : DeclarationChecked registry.constructors roles declaration := by
 constructor
 · refine ⟨rfl,?_,?_,?_⟩
   · intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
   · intro name value present
     change (if name = 0 then some none else none) = some value at present
     split at present
     · rename_i same; subst name; exact Or.inl ⟨⟨43,0,.var 7⟩,by simp [declaration],rfl⟩
     · cases present
   · intro clause member; cases member
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

theorem names : declaration.inputNames = [7] := rfl

theorem root_request : rootRequests declaration outputRoot = [⟨.var 7,4,.actual⟩] := rfl

theorem generated_body : GeneralNominalMaterialization.generated source interpretation
 (rootRequests declaration outputRoot) = body := by
 rw [root_request]
 simp [GeneralNominalMaterialization.generated,GeneralNominalInspection.translate,normalize,schema,Schema.append,body]

theorem nonempty : body.variables.length = 1 := rfl
private theorem observed : Observes model (.source 4) leafValue := by
 rw [← at_upper]
 exact .source 4
private theorem unique (a : Ty) (h : Observes model (.source 4) a) : Equivalent a leafValue :=
 nominal_observation_unique model (.source 4) a leafValue h observed
private theorem propagated : GeneralNominalState.Models
 (GeneralNominalAllocation.propagate source registry outputRoot.identity declaration
 (bindings source (inspect source (query shape) (0,0) none))) model := by
 change GeneralNominalState.Models (GeneralNominalAllocation.propagate start.context.state registry outputRoot.identity declaration
   (bindings start.context.state (inspect start.context.state (query shape) (shape.root,shape.root) none))) model
 rw [bindings_before shape]
 exact GeneralDictionaryNonpointExample.old_propagation

theorem old_materialized : Models source declaration
 (oldCapture shape registry outputRoot.identity declaration)
 (inspect source (query shape) (0,0) none) body model := by
 refine ⟨?_,?_,?_,?_⟩
 · intro test member; cases member
 · intro entry member
   cases List.mem_singleton.mp member
   refine ⟨⟨leafValue,observed⟩,?_⟩
   intro a seen
   change GeneralNominalCaptureMerges.Fits model
     ((oldCapture shape registry outputRoot.identity declaration).inputs 7) a
   have eq := unique a seen
   unfold oldCapture
   rw [bindings_before shape]
   change Subtype (model loId).1 a ∧ Subtype a (model hiId).1
   rw [at_merge_lower,at_merge_upper]
   exact ⟨subtype_trans bottom_leaf eq.2,eq.1⟩
 · intro first hf last hl same one two a b ha hb
   cases List.mem_singleton.mp hf
   cases List.mem_singleton.mp hl
   exact ⟨subtype_trans (unique a ha).1 (unique b hb).2,
     subtype_trans (unique b hb).1 (unique a ha).2⟩
 · intro entry member captured present same actual origin known a b seen leafSeen
   cases List.mem_singleton.mp member
   change captured ∈ (inspect start.context.state (query shape) (shape.root,shape.root) none).captures at present
   rw [before_exact shape] at present
   simp only [beforeReport,List.mem_cons,List.not_mem_nil,or_false] at present
   rcases present with rfl | rfl
   all_goals cases Option.some.inj known
   all_goals exact ⟨subtype_trans (unique a seen).1 (leaf_unique b leafSeen).2,
     subtype_trans (leaf_unique b leafSeen).1 (unique a seen).2⟩

theorem current_materialized : Models revision.snapshot declaration
 (newCapture shape registry outputRoot.identity declaration)
 (inspect revision.snapshot (query shape) ((0 : Fin 5),(0 : Fin 5)) none) body model :=
 GeneralDictionaryNonpointBranch.replay shape registry outputRoot.identity declaration body model
 (by change 7 ∈ [7]; simp)
 (by intro entry member _; cases List.mem_singleton.mp member; rfl)
 (by intro entry member; cases List.mem_singleton.mp member; rfl)
 propagated old_materialized

open GeneralNominalRecursiveCandidates

theorem queries : GeneralNominalInspection.queries source interpretation declaration = [query shape] := by
 simp [GeneralNominalInspection.queries,declaration,Declaration.normalHead,normalizeArgs,normalize,
   GeneralNominalInspection.translate,interpretation,GeneralDictionarySemanticCollapseExample.interpretation,
   source,GeneralDeclarationExamples.constructors,query,shape]

theorem report_exact : report context declaration bounds =
 GeneralDictionarySemanticCollapseBranch.oldRootReport shape :=
 (GeneralDictionarySemanticCollapseBranch.reports shape declaration queries).1

theorem generated_exact : GeneralNominalRecursiveCandidates.generated registry context outputRoot declaration checked bounds = body := by
 unfold GeneralNominalRecursiveCandidates.generated
 rw [GeneralDictionarySemanticCollapseBranch.terminal_requests _ _ _ _ _ _ rfl]
 exact generated_body

theorem private_models : GeneralNominalState.Models
 (privateState registry context outputRoot declaration bounds) model := by
 exact GeneralDictionaryNonpointExample.private_models

theorem old_branch : BranchModels registry context outputRoot declaration checked bounds model := by
 refine ⟨private_models,?_,?_⟩
 · rw [report_exact]
   have h := old_projection
   change ProjectionModels start.context.state (inspect start.context.state (query shape) (shape.root,shape.root) none) model at h
   rw [before_exact] at h
   exact h
 · rw [generated_exact,report_exact]
   have h := old_materialized
   change GeneralNominalMaterialization.Models start.context.state declaration
     (oldCapture shape registry outputRoot.identity declaration)
     (inspect start.context.state (query shape) (shape.root,shape.root) none) body model at h
   unfold oldCapture at h
   rw [before_exact] at h
   exact h

theorem current_branch : BranchModels registry
 (GeneralDictionarySemanticCollapseBranch.currentContext revision) outputRoot declaration checked bounds model := by
 apply GeneralDictionaryNonpointBranch.branch shape registry outputRoot declaration checked queries names rfl
 · change ∀ entry ∈ (GeneralNominalRecursiveCandidates.generated registry context outputRoot declaration checked bounds).variables, _
   rw [generated_exact]
   intro entry member _
   cases List.mem_singleton.mp member
   rfl
 · exact old_branch
 · exact revised_models

theorem positive_nonpoint_output :
 body.variables.length = 1 ∧
 BranchModels registry context outputRoot declaration checked bounds model ∧
 BranchModels registry (GeneralDictionarySemanticCollapseBranch.currentContext revision) outputRoot declaration checked bounds model ∧
 shape.first.1 ≠ shape.first.2 ∧ (model 3).1 ≠ (model 4).1 :=
 ⟨rfl,old_branch,current_branch,nonpoint_leaf⟩
end Yulang.GeneralDictionaryNonpointOutput
