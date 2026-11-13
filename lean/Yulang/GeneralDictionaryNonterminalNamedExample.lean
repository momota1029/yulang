import Yulang.GeneralDictionaryNonpointStrictOutput
import Yulang.GeneralDictionaryNonterminalScope

/-! Nonterminal parent with both a named root output and a named where output.
Two actual-mode requests survive strict nonpoint capture collapse. This proves
private BranchModels, not child Evidence, operational output installation,
or a certified revision. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionaryNonterminalNamedExample
open GeneralDictionaryNonpointStrict
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseSchema
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalMaterialization
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
abbrev child : Clause := ⟨51,1,[.var 7],[⟨52,0,.var 7⟩]⟩
abbrev declaration : Declaration := ⟨31,1,[.app 0 [.app 0 [.var 7]]],[child],[⟨43,0,.var 7⟩],[]⟩
abbrev registry : Registry := ⟨source.constructors,roles,[declaration]⟩
abbrev outputRoot : GeneralSourceDictionaries.Occurrence roles :=
 ⟨0,⟨1,fun _ => (0,0),[⟨0,4⟩],by intro output member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩⟩
abbrev target : Nat := GeneralNominalAllocation.source source registry outputRoot.identity
 (GeneralNominalAllocation.origin outputRoot.identity declaration.id 5 52 0)
abbrev body : Schema := ⟨[⟨7,.source 4,.actual⟩,⟨7,.source target,.actual⟩],[],false⟩

theorem checked : DeclarationChecked registry.constructors roles declaration := by
 constructor
 · refine ⟨rfl,?_,?_,?_⟩
   · intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
   · intro name value present
     change (if name = 0 then some none else none) = some value at present
     split at present
     · rename_i same; subst name; exact Or.inl ⟨⟨43,0,.var 7⟩,by simp [declaration,child],rfl⟩
     · cases present
   · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,by intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩
 · simp [Declaration.Identified,Declaration.outputNames,declaration,child]
 · simp [Declaration.Produced,declaration,child]
 · simp [Declaration.OutputOnly,Declaration.outputNames,declaration,child]
 · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,declaration,child,
    normalizeArgs,normalize,variablesArgs,Pattern.variables]
 · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,declaration,registry,source,
    GeneralDeclarationExamples.constructors,child]
 · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
 · intro clause member; cases List.mem_singleton.mp member
   exact (checkSmaller_exact _ _).mp (by decide +kernel)
 · intro clause member; cases List.mem_singleton.mp member
   unfold ConservativeSmaller; decide +kernel
 · intro clause member; cases List.mem_singleton.mp member
   intro capture
   constructor
   · simp [declaration,child,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
       encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
     omega
   · intro name
     simp [declaration,child,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
       encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

theorem variable_inputs : GeneralDictionaryVariableWhereRequests.VariableInputs declaration := by
 intro c hc; cases List.mem_singleton.mp hc
 intro p hp; cases List.mem_singleton.mp hp
 exact ⟨7,rfl⟩

theorem output_normal : ∀ c ∈ declaration.requirements, ∀ eq ∈ c.outputs,
 GeneralDeclarationPatterns.normalize eq.rhs = eq.rhs := by
 intro c hc; cases List.mem_singleton.mp hc
 intro eq he; cases List.mem_singleton.mp he
 rfl

theorem names : declaration.inputNames = [7] := rfl

theorem root_request : rootRequests declaration outputRoot = [⟨.var 7,4,.actual⟩] := rfl

theorem target_value : (model target).1 = leafValue := by
 have above : 4 < target := GeneralNominalIdentities.source_above_seed _ _
 simp [GeneralDictionaryNonpointStrict.model,show target ≠ 0 by omega,show target ≠ 1 by omega,
   show target ≠ 2 by omega,show target ≠ 3 by omega]
 rfl

theorem nonempty : body.variables.length = 2 := rfl
private theorem entry_source (entry : Use) (h : entry ∈ body.variables) :
 ∃ id, entry = ⟨7,.source id,.actual⟩ ∧ (model id).1 = leafValue := by
 change entry ∈ [⟨7,.source 4,.actual⟩,⟨7,.source target,.actual⟩] at h
 rcases List.mem_cons.mp h with rfl | h
 · exact ⟨4,rfl,at_upper⟩
 · cases List.mem_singleton.mp h
   exact ⟨target,rfl,target_value⟩
private theorem observed (id : Nat) (value : (model id).1 = leafValue) :
 Observes model (.source id) leafValue := by
 rw [← value]
 exact .source id
private theorem unique (id : Nat) (value : (model id).1 = leafValue) (a : Ty)
 (h : Observes model (.source id) a) : Equivalent a leafValue :=
 nominal_observation_unique model (.source id) a leafValue h (observed id value)
private theorem propagated : GeneralNominalState.Models
 (GeneralNominalAllocation.propagate source registry outputRoot.identity declaration
 (bindings source (inspect source (query shape) (0,0) none))) model := by
 change GeneralNominalState.Models (GeneralNominalAllocation.propagate start.context.state registry outputRoot.identity declaration
   (bindings start.context.state (inspect start.context.state (query shape) (shape.root,shape.root) none))) model
 rw [bindings_before shape]
 exact GeneralDictionaryNonpointStrict.old_propagation

theorem old_materialized : Models source declaration
 (oldCapture shape registry outputRoot.identity declaration)
 (inspect source (query shape) (0,0) none) body model := by
 refine ⟨?_,?_,?_,?_⟩
 · intro test member; cases member
 · intro entry member
   obtain ⟨id,rfl,value⟩ := entry_source entry member
   refine ⟨⟨leafValue,observed id value⟩,?_⟩
   intro a seen
   change GeneralNominalCaptureMerges.Fits model
     ((oldCapture shape registry outputRoot.identity declaration).inputs 7) a
   have eq := unique id value a seen
   unfold oldCapture
   rw [bindings_before shape]
   change Subtype (model loId).1 a ∧ Subtype a (model hiId).1
   rw [at_merge_lower,at_merge_upper]
   exact ⟨eq.2,eq.1⟩
 · intro first hf last hl same one two a b ha hb
   obtain ⟨firstId,rfl,firstValue⟩ := entry_source first hf
   obtain ⟨lastId,rfl,lastValue⟩ := entry_source last hl
   exact ⟨subtype_trans (unique firstId firstValue a ha).1 (unique lastId lastValue b hb).2,
     subtype_trans (unique lastId lastValue b hb).1 (unique firstId firstValue a ha).2⟩
 · intro entry member captured present same actual origin known a b seen leafSeen
   obtain ⟨id,rfl,value⟩ := entry_source entry member
   change captured ∈ (inspect start.context.state (query shape) (shape.root,shape.root) none).captures at present
   rw [before_exact shape] at present
   simp only [beforeReport,List.mem_cons,List.not_mem_nil,or_false] at present
   rcases present with rfl | rfl
   all_goals cases Option.some.inj known
   all_goals exact ⟨subtype_trans (unique id value a seen).1 (leaf_unique b leafSeen).2,
     subtype_trans (leaf_unique b leafSeen).1 (unique id value a seen).2⟩

open GeneralNominalRecursiveCandidates

theorem queries : GeneralNominalInspection.queries source interpretation declaration = [query shape] := by
 simp [GeneralNominalInspection.queries,declaration,Declaration.normalHead,normalizeArgs,normalize,
   GeneralNominalInspection.translate,interpretation,GeneralDictionarySemanticCollapseExample.interpretation,
   source,GeneralDeclarationExamples.constructors,query,shape]

theorem report_exact : report context declaration bounds =
 GeneralDictionarySemanticCollapseBranch.oldRootReport shape :=
 (GeneralDictionarySemanticCollapseBranch.reports shape declaration queries).1

theorem requests_exact : GeneralNominalMaterialization.requests source registry outputRoot declaration checked
 (bindings source (report context declaration bounds)) =
 [⟨.var 7,4,.actual⟩,⟨.var 7,target,.actual⟩] := by
 have canon : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by
   simp [GeneralCanonicalChildOrder.canonicalDeclaration, GeneralCanonicalChildOrder.canonicalRequirements, declaration, List.mergeSort_singleton]
 unfold GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
 simp only [canon]
 simp [rootRequests,outputRoot,declaration,child,GeneralDeclarationDemands.emitAll,
   GeneralDeclarationDemands.emit,emissionRequests,inputRequests,GeneralDeclarationDemands.childDemand,
   GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
   normalize,Declaration.outputNames,GeneralNominalAllocation.allocation,target,
   List.ofFn_succ,List.ofFn_zero,roles,GeneralDeclarationExamples.roles,GeneralDeclarationExamples.outputRole]

theorem generated_exact : GeneralNominalRecursiveCandidates.generated registry context outputRoot declaration checked bounds = body := by
 unfold GeneralNominalRecursiveCandidates.generated
 rw [requests_exact]
 simp [GeneralNominalMaterialization.generated,GeneralNominalInspection.translate,
   normalize,schema,Schema.append,body]

theorem private_models : GeneralNominalState.Models
 (privateState registry context outputRoot declaration bounds) model := by
 exact GeneralDictionaryNonpointStrict.private_models

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
 exact GeneralDictionaryNonterminalScope.normal_form_branch shape registry outputRoot declaration checked
   queries names variable_inputs output_normal model old_branch revised_models

theorem positive_nonterminal :
 declaration.requirements.length = 1 ∧ body.variables.length = 2 ∧
 BranchModels registry context outputRoot declaration checked bounds model ∧
 BranchModels registry (GeneralDictionarySemanticCollapseBranch.currentContext revision) outputRoot declaration checked bounds model ∧
 shape.first.1 ≠ shape.first.2 ∧ (model 3).1 ≠ (model 4).1 :=
 ⟨rfl,rfl,old_branch,current_branch,nonpoint_leaf⟩
end Yulang.GeneralDictionaryNonterminalNamedExample
