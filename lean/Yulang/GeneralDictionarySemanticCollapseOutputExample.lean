import Yulang.GeneralDictionarySemanticCollapseBranch
import Yulang.GeneralDictionarySemanticCollapseAllocationExample

/-! A nonempty associated root request across the actual revision fixture.
This is an input-backed named output, not a produced output binder. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionarySemanticCollapseOutputExample
open GeneralDictionarySemanticCollapseExample
open GeneralDictionarySemanticCollapse
open GeneralDictionarySemanticCollapseSchema
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalMaterialization
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
abbrev declaration : Declaration := ⟨42,1,[.app 0 [.app 0 [.var 7]]],[],[⟨43,0,.var 7⟩],[]⟩
abbrev registry : Registry := ⟨source.constructors,GeneralDeclarationExamples.roles,[declaration]⟩
abbrev outputRoot : GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles :=
 ⟨0,⟨1,fun _ => (0,0),[⟨0,3⟩],by intro output member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩⟩
abbrev body : Schema := ⟨[⟨7,.source 3,.actual⟩],[],false⟩

theorem checked : DeclarationChecked registry.constructors GeneralDeclarationExamples.roles declaration := by
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

theorem root_request : rootRequests declaration outputRoot = [⟨.var 7,3,.actual⟩] := rfl

theorem generated_body : GeneralNominalMaterialization.generated source interpretation
 (rootRequests declaration outputRoot) = body := by
 rw [root_request]
 simp [GeneralNominalMaterialization.generated,GeneralNominalInspection.translate,normalize,schema,Schema.append,body]

theorem nonempty : body.variables.length = 1 := rfl

private theorem observed : Observes model (.source 3) leafValue := .source 3
private theorem unique (a : Ty) (h : Observes model (.source 3) a) : Equivalent a leafValue :=
 nominal_observation_unique model (.source 3) a leafValue h observed

private theorem propagated : GeneralNominalState.Models
 (GeneralNominalAllocation.propagate source registry outputRoot.identity declaration
 (bindings source (inspect source (query shape) (0,0) none))) model := by
 change GeneralNominalState.Models (GeneralNominalAllocation.propagate start.context.state registry outputRoot.identity declaration
   (bindings start.context.state (inspect start.context.state (query shape) (shape.root,shape.root) none))) model
 rw [bindings_before shape]
 exact GeneralDictionarySemanticCollapseAllocationExample.old_propagation registry _ declaration names

theorem old_materialized : Models source declaration
 (oldCapture shape registry outputRoot.identity declaration)
 (inspect source (query shape) (0,0) none) body model := by
 have ends := GeneralDictionarySemanticCollapseAllocationExample.endpoints registry outputRoot.identity declaration names
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
   exact ⟨subtype_trans ends.1.1 eq.2,subtype_trans eq.1 ends.2.2⟩
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
 (inspect revision.snapshot (query shape) ((0 : Fin 4),(0 : Fin 4)) none) body model :=
 replay shape registry outputRoot.identity declaration body model (by change 7 ∈ [7]; simp)
 (by intro entry member _; cases List.mem_singleton.mp member; rfl)
 old_projection rfl rfl propagated old_materialized

open GeneralNominalRecursiveCandidates
abbrev context := start.context
abbrev bounds : List (GeneralNominalInspection.Bounds source) := [(0,0)]

theorem queries : GeneralNominalInspection.queries source interpretation declaration = [query shape] := by
 simp [GeneralNominalInspection.queries,declaration,Declaration.normalHead,normalizeArgs,normalize,
   GeneralNominalInspection.translate,interpretation,source,GeneralDeclarationExamples.constructors,query,shape]

theorem report_exact : report context declaration bounds =
 GeneralDictionarySemanticCollapseBranch.oldRootReport shape :=
 (GeneralDictionarySemanticCollapseBranch.reports shape declaration queries).1

theorem generated_exact : GeneralNominalRecursiveCandidates.generated registry context outputRoot declaration checked bounds = body := by
 unfold GeneralNominalRecursiveCandidates.generated
 rw [GeneralDictionarySemanticCollapseBranch.terminal_requests _ _ _ _ _ _ rfl]
 exact generated_body

theorem private_models : GeneralNominalState.Models
 (privateState registry context outputRoot declaration bounds) model := by
 unfold privateState
 apply (GeneralNominalState.extend_models ..).mpr
 constructor
 · have captured : bindings source (report context declaration bounds) = [(7,3,3),(7,3,3)] := by
     rw [report_exact]; rfl
   rw [captured]
   exact GeneralDictionarySemanticCollapseAllocationExample.old_propagation registry outputRoot.identity declaration names
 · unfold selfChecks
   rw [report_exact]
   change PresenceNormalForm.All CommonNominalFullCarrier.model model
    ([(0,0),(0,0),(1,2),(3,3),(3,3)].map fun pair =>
      PresenceNormalForm.Atom.tyLe (.var pair.1) (.var pair.2))
   intro atom member
   simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl
   all_goals exact subtype_refl _

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
 apply GeneralDictionarySemanticCollapseBranch.branch shape registry outputRoot declaration checked queries names rfl rfl rfl
 · change ∀ entry ∈ (GeneralNominalRecursiveCandidates.generated registry context outputRoot declaration checked bounds).variables, _
   rw [generated_exact]
   intro entry member _
   cases List.mem_singleton.mp member
   rfl
 · exact old_branch
 · exact revised_models

/-- Terminal checked declarations cannot contain produced output binders. -/
theorem terminal_no_output_binders (d : Declaration)
 (h : d.Produced) (terminal : d.requirements = []) : d.outputBinders = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro binder member
 obtain ⟨clause,inside,_⟩ := h binder member
 rw [terminal] at inside
 cases inside
end Yulang.GeneralDictionarySemanticCollapseOutputExample
