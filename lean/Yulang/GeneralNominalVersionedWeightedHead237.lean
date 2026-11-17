import Yulang.GeneralNominalVersionedHeadMass237
import Yulang.GeneralNominalVersionedEvidence231
import Yulang.GeneralNominalCompleteNames183

set_option backward.isDefEq.respectTransparency false

/-! The actual head-only preparation supplies complete queries. Their schema
weights are bounded by semantic input labels, without inspecting outputs. -/
namespace Yulang.GeneralNominalVersionedWeightedHead237
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatHeadParts
open GeneralNominalCenteredHeadMatSchemaMass hiding schema_restrict schema_mass
open GeneralNominalVersionedHeadMass237
open GeneralNominalCenteredHeadMatSemanticLabels (Inputs)
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalCompoundReadback GeneralNominalMaterialization
open GeneralNominalHeadMatchMass GeneralNominalCanonicalTemplates
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {labels : List Pattern}

theorem substituted_size (patterns : List Pattern) (substitution : Roles.Subst) :
    Roles.argsSize (Roles.substArgs substitution (encodeArgs patterns)) =
      (patterns.map fun pattern => (pattern.encode.subst substitution).size).sum := by
  induction patterns with
  | nil => rfl
  | cons first rest ih => simp only [encodeArgs,Roles.substArgs,Roles.argsSize,List.map_cons,List.sum_cons,ih]

theorem head_weight
    (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
    (nonempty : plan.packet.declaration.requirements ≠ [])
    (branch : GeneralNominalVersionedPlans231.Holds plan model)
    (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
    (substitution : Roles.Subst)
    (bounded : ∀ name pattern,
      Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name pattern →
      (substitution name).size ≤ pattern.encode.size) :
    Roles.argsSize (Roles.substArgs substitution (encodeArgs (normalizeArgs plan.packet.declaration.head))) ≤ mass labels := by
  obtain ⟨clause,member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have covered := (plan.packet.checked.countsCovered clause member).1
  obtain ⟨inputLength,inputMeanings⟩ := known
  have role : plan.packet.declaration.role = plan.input.occurrence.demand.role := by
    rw [plan.input_exact,frame.occurrence_eq]; exact frame.role_eq
  have headLength : (normalizeArgs plan.packet.declaration.head).length = (roles plan.input.occurrence.demand.role).arity := by
    simpa only [GeneralNominalChildAssembly.normalize_map,List.length_map,role] using plan.packet.checked.signature.1
  have prepared := frame.prepared
  rw [← frame.context_eq] at prepared
  obtain ⟨_,_,bounds,_,_,finished,_⟩ := prepared
  have allComplete := GeneralNominalCompleteNames183.many_complete plan.packet.context.state _ bounds _ _ finished
  have schemaValid := branch.2.1.2.2.2.2.1
  let heads := normalizeArgs plan.packet.declaration.head
  have atIndex (index : Fin (roles plan.input.occurrence.demand.role).arity) :
      ((heads[index.val]'(by rw [headLength]; exact index.isLt)).encode.subst substitution).size ≤
        (normalize (labels[index.val]'(by rw [inputLength]; exact index.isLt))).encode.size := by
    let pattern := heads[index.val]'(by rw [headLength]; exact index.isLt)
    have patternMem : pattern ∈ normalizeArgs plan.packet.declaration.head := List.getElem_mem ..
    have counted := GeneralNominalChildAssembly.covered_member _ covered pattern patternMem
    have normal := GeneralPatternCoveredResult.prepared_normal pattern
      (GeneralPatternCoveredResult.args_prepared _ pattern patternMem) counted
    have complete : Complete (GeneralNominalInspection.translate plan.packet.context.state.constructors
        plan.packet.context.interpretation pattern) := allComplete _ (List.mem_map.mpr ⟨pattern,patternMem,rfl⟩)
    obtain ⟨term,quoted,canonical,_⟩ := quoted _ (translated_good pattern normal complete (allowed := fun _ => True) (by intro name used; trivial))
    let origin := Origin.source (plan.input.center index)
    have input := inputMeanings index
    have represented : At model .actual origin (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation)
        (fun _ => .bottom) (normalize (labels[index.val]'(by rw [inputLength]; exact index.isLt)))) :=
      ⟨⟨_,.source _⟩,by intro value seen; change Observes model (.source (plan.input.center index)) value at seen; cases seen; exact input.2.2⟩
    have included := schemas_component
      (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration)
      (fun i => .source ((List.ofFn plan.input.center)[i]?.getD 0)) .actual 0 index.val
      (query := GeneralNominalInspection.translate plan.packet.context.state.constructors plan.packet.context.interpretation pattern)
      (by simp only [GeneralNominalInspection.queries,Declaration.normalHead,List.getElem?_map,
        List.getElem?_eq_getElem (by rw [headLength]; exact index.isLt),Option.map_some]; rfl)
    have localSchema : GeneralNominalVersionedPlans231.SchemaHolds plan (schema (quote term) origin .actual) model := by
      have restricted := schema_restrict schemaValid included
      simpa only [Nat.zero_add,List.getElem?_ofFn,index.isLt,dite_eq_left,Option.getD_some,← quoted,origin] using restricted
    rw [translated_count pattern counted complete substitution,← quoted]
    exact schema_mass term canonical
      ⟨input.1,GeneralPatternCoveredResult.covered_result_normal _ input.2.1⟩ represented localSchema bounded
  have summed := sum_le _ _ atIndex
  rw [substituted_size]
  have first := ofFn_index heads headLength (fun pattern => (pattern.encode.subst substitution).size)
  have last := ofFn_index labels inputLength (fun pattern => (normalize pattern).encode.size)
  rw [first,last] at summed
  simpa only [heads,mass,counted,GeneralNominalChildAssembly.normalize_map,encoded_size,size,List.map_map,Function.comp_def] using summed

end Yulang.GeneralNominalVersionedWeightedHead237
