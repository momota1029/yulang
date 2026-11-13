import Yulang.GeneralDictionaryPositiveNestedProjection

/-! A checked nested declaration with a real nonpoint located argument and
positive complete BranchModels. No operational Step is asserted here. -/
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
namespace Yulang.GeneralDictionaryPositiveNestedBranch
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
abbrev source := GeneralNominalProvenanceSource.state
abbrev roles : Roles.RoleDecls := fun _ => GeneralNominalProvenanceDeclarations.bareRole 1
abbrev declaration : Declaration := ⟨31,0,[.app 0 [.app 0 [.var 7]]],[],[],[]⟩
abbrev registry : Registry := ⟨source.constructors,roles,[declaration]⟩
abbrev context := GeneralNominalProvenanceSource.context
abbrev root : Occurrence roles := ⟨9,⟨0,fun _ => (0,3),[],by intro _ h; cases h⟩⟩
abbrev bounds : List (GeneralNominalInspection.Bounds source) := [(0,3)]
abbrev assignment := GeneralNominalProvenanceSource.model (.base .int) (.base .int) (.base .int)

theorem checked : DeclarationChecked registry.constructors roles declaration := by
 constructor
 · simp [Declaration.Signature,Clause.Signature,Declared,roles,GeneralNominalProvenanceDeclarations.bareRole,declaration]
 · simp [Declaration.Identified,Declaration.outputNames,declaration]
 · simp [Declaration.Produced,declaration]
 · simp [Declaration.OutputOnly,Declaration.outputNames,declaration]
 · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,declaration,
    normalizeArgs,normalize,variablesArgs,Pattern.variables]
 · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,declaration,registry,source,
    GeneralNominalProvenanceSource.state,GeneralNominalProvenanceDeclarations.constructors,GeneralDeclarationExamples.constructors]
 · intro _ h; cases h
 · intro _ h; cases h
 · intro _ h; cases h
 · intro _ h; cases h

theorem report_exact : report context declaration bounds =
 { GeneralDictionaryPositiveNestedProjection.result with
   checked := [(0,3)] ++ GeneralDictionaryPositiveNestedProjection.result.checked } := by
 unfold report
 have q : GeneralNominalInspection.queries source context.interpretation declaration =
   [GeneralDictionaryNestedRefinementExamples.query] := by
   simp [GeneralNominalInspection.queries,declaration,Declaration.normalHead,normalizeArgs,normalize,
     GeneralNominalInspection.translate,context,GeneralNominalProvenanceSource.interpretation,source,
     GeneralNominalProvenanceSource.state,GeneralNominalProvenanceDeclarations.constructors,GeneralDeclarationExamples.constructors]
 rw [q]
 simp [bounds,inspectMany.eq_1,inspectMany.eq_2,Report.append,GeneralDictionaryPositiveNestedProjection.result,
   GeneralDictionaryNestedRefinementExamples.bounds]

theorem captured : bindings source (report context declaration bounds) = [(7,2,2),(7,5,5)] := by
 rw [report_exact]
 exact GeneralDictionaryNestedRefinementExamples.captures_two_sources

private theorem above_value (n : Nat) (above : 7 < n) : (assignment n).1 = .base .int := by
 obtain ⟨k,rfl⟩ : ∃ k, n = k + 8 := ⟨n-8,by omega⟩
 rfl

private theorem allocated_value (key : GeneralNominalIdentities.Origin) :
 (assignment (GeneralNominalAllocation.source source registry root.identity key)).1 = .base .int := by
 apply above_value
 exact GeneralNominalIdentities.source_above_seed source.seed key

private theorem propagated : GeneralNominalState.Models
 (GeneralNominalAllocation.propagate source registry root.identity declaration
  [(7,2,2),(7,5,5)]) assignment := by
 apply (GeneralNominalAllocation.propagate_models ..).mpr
 refine ⟨GeneralNominalProvenanceSource.source_models _ _ _,?_,?_⟩
 · intro first hf last hl same
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hf hl
   rcases hf with rfl | rfl <;> rcases hl with rfl | rfl <;> exact subtype_refl _
 · simp only [GeneralNominalAllocation.merges,Declaration.inputNames,declaration,
    normalizeArgs,normalize,variablesArgs,Pattern.variables,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.map_cons,List.map_nil,List.eraseDups_cons,List.eraseDups_nil]
   change PresenceNormalForm.All CommonNominalFullCarrier.model assignment
    (GeneralNominalAllocation.equations _ (.union (.var 2) (.var 5)) ++
     GeneralNominalAllocation.equations _ (.inter (.var 2) (.var 5)))
   apply (PresenceNormalForm.all_append ..).mpr
   constructor
   · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
     change Equivalent (assignment (GeneralNominalAllocation.source source registry root.identity _)).1 (.union (.base .int) (.base .int))
     rw [allocated_value]
     exact ⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
       (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩
   · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
     change Equivalent (assignment (GeneralNominalAllocation.source source registry root.identity _)).1 (.inter (.base .int) (.base .int))
     rw [allocated_value]
     exact ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
       (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩
theorem checked_intervals : (report context declaration bounds).checked =
 [(0,3),(0,3),(1,1),(2,2),(4,4),(5,5)] := by
 rw [report_exact]
 decide +kernel

theorem private_models : GeneralNominalState.Models
 (privateState registry context root declaration bounds) assignment := by
 unfold privateState
 apply (GeneralNominalState.extend_models ..).mpr
 constructor
 · rw [captured]
   exact propagated
 · unfold selfChecks
   rw [checked_intervals]
   intro atom member
   simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl
   all_goals exact subtype_refl _

theorem generated_empty : generated registry context root declaration checked bounds = {} := by
 have emitted := GeneralCanonicalChildOrder.canonicalEmit_perm root.identity declaration checked
   (GeneralNominalAllocation.capture source registry root.identity declaration.id
     (bindings source (report context declaration bounds)))
   (GeneralNominalAllocation.allocation source registry root.identity declaration.id)
 have empty : GeneralDeclarationDemands.emitAll root.identity declaration checked.signature
   (GeneralNominalAllocation.capture source registry root.identity declaration.id
     (bindings source (report context declaration bounds)))
   (GeneralNominalAllocation.allocation source registry root.identity declaration.id) = [] := rfl
 rw [empty] at emitted
 have actual := List.Perm.nil_eq emitted
 unfold generated GeneralNominalMaterialization.requests
 rw [← actual]
 rfl

theorem branch_models : BranchModels registry context root declaration checked bounds assignment := by
 refine ⟨private_models,?_,?_⟩
 · rw [report_exact]
   exact GeneralDictionaryPositiveNestedProjection.projection _ _
 · rw [generated_empty]
   exact GeneralNominalMaterialization.empty_models _ _ _ _ _

theorem consistent : Consistent registry context root declaration checked bounds :=
 ⟨assignment,branch_models⟩

theorem located : arguments context root = some bounds := by decide +kernel

theorem prepared : Prepared registry context root declaration checked := by
 refine ⟨?_,?_,?_,bounds,located,?_,?_,consistent⟩
 · exact GeneralNominalProvenanceSource.metadata
 · constructor
   · intro index
     exact ⟨GeneralNominalProvenanceSource.source_member 0,
       GeneralNominalProvenanceSource.source_member 3⟩
   · intro output member; cases member
 · intro key member collision
   have below : (GeneralNominalState.sources source).foldr max 0 = source.seed := by decide +kernel
   have bound := GeneralNominalAllocation.member_le_max _ _ collision
   rw [below] at bound
   exact False.elim ((GeneralNominalAllocation.source_initial_fresh source registry root.identity key _ bound) rfl)
 · rw [report_exact]
   exact GeneralDictionaryNestedRefinementExamples.nested_finished
 · constructor
   · intro output member; cases member
   · rw [generated_empty]

theorem survivor : Survivor registry context root declaration.id [] := by
 refine ⟨?_,declaration,by simp [registry],checked,rfl,rfl,bounds,located,prepared,?_⟩
 · rintro ⟨index,unknown⟩
   exact unknown ⟨0,rfl,Or.inr ⟨GeneralNominalProvenanceSource.listDescriptor 1,rfl⟩⟩
 · symm
   unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
   have emitted := GeneralCanonicalChildOrder.canonicalEmit_perm root.identity declaration checked
     (GeneralNominalAllocation.capture source registry root.identity declaration.id
       (bindings source (report context declaration bounds)))
     (GeneralNominalAllocation.allocation source registry root.identity declaration.id)
   have empty : GeneralDeclarationDemands.emitAll root.identity declaration checked.signature
     (GeneralNominalAllocation.capture source registry root.identity declaration.id
       (bindings source (report context declaration bounds)))
     (GeneralNominalAllocation.allocation source registry root.identity declaration.id) = [] := rfl
   rw [empty] at emitted
   simp only [GeneralNominalAllocation.frame]
   rw [← List.Perm.nil_eq emitted]
   rfl

end Yulang.GeneralDictionaryPositiveNestedBranch
