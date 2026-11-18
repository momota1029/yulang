import Yulang.GeneralNominalVersionedHeadReadback237
import Yulang.GeneralPatternAdditiveDepth253

/-! All named head-input captures, including associated-only uses. The actual
Frame, Holds and ground Inputs imply finite bounded labels for covered heads.
Checked nonempty where supplies that coverage; arbitrary leaf heads do not. -/
namespace Yulang.GeneralNominalAllHeadReadback253
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatHeadParts GeneralNominalCenteredHeadMatSchemaMass
open GeneralNominalCenteredHeadMatSemanticLabels (Inputs Captures images)
open GeneralNominalVersionedWeightedHead237
open GeneralNominalCenteredHeadMatStepJournal GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalCenteredHeadMatStepDepthSupport
open GeneralNominalCenteredHeadMatSemanticAncestry (GroundHeadReadback)
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {labels : List Pattern}

open GeneralNominalVersionedHeadMass237
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalCompoundReadback GeneralNominalMaterialization
open GeneralNominalHeadMatchMass GeneralNominalCanonicalTemplates
open GeneralNominalCenteredHeadMatSchemaMass hiding schema_restrict schema_mass

theorem head_weight_covered
    (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
    (coveredHead : coveredArgs (normalizeArgs plan.packet.declaration.head) = true)
    (branch : GeneralNominalVersionedPlans231.Holds plan model)
    (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
    (substitution : Roles.Subst)
    (bounded : ∀ name pattern,
      Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name pattern →
      (substitution name).size ≤ pattern.encode.size) :
    Roles.argsSize (Roles.substArgs substitution (encodeArgs (normalizeArgs plan.packet.declaration.head))) ≤ mass labels := by
  have covered := coveredHead
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

theorem finite_capture_covered
    (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
    (coveredHead : coveredArgs (normalizeArgs plan.packet.declaration.head) = true)
    (branch : GeneralNominalVersionedPlans231.Holds plan model)
    (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
    (input : name ∈ plan.packet.declaration.inputNames) :
    ∃ pattern, Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name pattern := by
  classical
  apply Classical.byContradiction
  intro absent
  let substitution : Roles.Subst := fun other =>
    if other = name then GeneralNominalCenteredCaptureLabels.large (mass labels) else .var other
  have weighted := head_weight_covered frame coveredHead branch known substitution (by
    intro other pattern finite
    have different : other ≠ name := by
      intro same; subst other; exact absent ⟨pattern,finite⟩
    simpa only [substitution,different,ite_false,Roles.Term.size] using Nat.succ_le_of_lt pattern.encode.size_pos)
  have lower := GeneralNominalCenteredCaptureLabels.variables_bound
    (normalizeArgs plan.packet.declaration.head) substitution
    input
  have large : (substitution name).size = mass labels + 1 := by
    simp only [substitution,ite_true,GeneralNominalCenteredCaptureLabels.large_size]
  omega

theorem readback_covered
    (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
    (coveredHead : coveredArgs (normalizeArgs plan.packet.declaration.head) = true)
    (branch : GeneralNominalVersionedPlans231.Holds plan model)
    (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels) :
    ∃ capture, Captures plan model capture ∧
      (∀ name ∈ plan.packet.declaration.inputNames, Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name (capture name)) ∧
      (∀ name ∈ plan.packet.declaration.inputNames, (capture name).encode.size ≤ mass labels) ∧
      mass (substArgs (images capture) (normalizeArgs plan.packet.declaration.head)) ≤ mass labels := by
  classical
  let semantics := algebra plan.packet.registry.constructors plan.packet.context.interpretation
  have witnesses : ∀ name, name ∈ plan.packet.declaration.inputNames →
      ∃ pattern, Part semantics plan model name pattern ∧
        ∀ other, Part semantics plan model name other → pattern.encode.size ≤ other.encode.size :=
    fun name needed => GeneralNominalVersionedHeadReadback237.minimum_capture (finite_capture_covered frame coveredHead branch known needed)
  let capture : Nat → Pattern := fun name => if needed : name ∈ plan.packet.declaration.inputNames
    then Classical.choose (witnesses name needed) else .var name
  have normals (name : Nat) : GeneralPatternNormalForm.Normal (capture name) := by
    by_cases needed : name ∈ plan.packet.declaration.inputNames
    · simpa only [capture,dite_eq_left needed] using (Classical.choose_spec (witnesses name needed)).1.1.2
    · simp only [capture,dite_eq_right needed,GeneralPatternNormalForm.Normal]
  have fixed (name : Nat) : normalize (capture name) = capture name := GeneralPatternNormalForm.fixed _ (normals name)
  have meaning (name : Nat) (needed : name ∈ plan.packet.declaration.inputNames) :
      Part semantics plan model name (capture name) := by
    simpa only [capture,dite_eq_left needed] using (Classical.choose_spec (witnesses name needed)).1
  have captures : Captures plan model capture := by
    refine ⟨fun name => ?_,fun name needed => ?_⟩
    · rw [fixed]; exact GeneralPatternNormalForm.covered_normal _ (normals name)
    · have finite := meaning name (GeneralNominalCenteredHeadMatSemanticLabels.needed_in_head needed)
      exact ⟨by rw [fixed]; exact finite.1.1,
        by rw [fixed]; exact GeneralPatternNormalForm.covered_normal _ finite.1.2,
        by rw [fixed]; exact finite.2⟩
  have imageFixed (name : Nat) : normalize (images capture name) = capture name := by
    simp only [images,fixed]
  have weighted := head_weight_covered frame coveredHead branch known
    (GeneralPatternConservativeSubstitution.captureTerms (images capture)) (by
      intro name pattern finite
      change (normalize (images capture name)).encode.size ≤ pattern.encode.size
      rw [imageFixed]
      by_cases needed : name ∈ plan.packet.declaration.inputNames
      · simpa only [capture,dite_eq_left needed] using (Classical.choose_spec (witnesses name needed)).2 pattern finite
      · simpa only [capture,dite_eq_right needed,Pattern.encode,Roles.Term.size] using Nat.succ_le_of_lt pattern.encode.size_pos)
  have bound := (GeneralPatternConservativeSubstitution.substitutions_bounds (normalizeArgs plan.packet.declaration.head)
    coveredHead (images capture)).2
  refine ⟨capture,captures,meaning,?_,Nat.le_trans bound weighted⟩
  intro name input
  have lower := GeneralNominalCenteredCaptureLabels.variables_bound
    (normalizeArgs plan.packet.declaration.head)
    (GeneralPatternConservativeSubstitution.captureTerms (images capture)) input
  have small := Nat.le_trans lower weighted
  change (normalize (images capture name)).encode.size ≤ mass labels at small
  rw [imageFixed] at small
  exact small

/-- Checked nonempty-where declarations supply the head-coverage premise. -/
theorem readback
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (nonempty : plan.packet.declaration.requirements ≠ [])
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels) :
 ∃ capture, Captures plan model capture ∧
 (∀ name ∈ plan.packet.declaration.inputNames, Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name (capture name)) ∧
 (∀ name ∈ plan.packet.declaration.inputNames, (capture name).encode.size ≤ mass labels) ∧
 mass (substArgs (images capture) (normalizeArgs plan.packet.declaration.head)) ≤ mass labels := by
 obtain ⟨clause,member⟩ := List.exists_mem_of_ne_nil _ nonempty
 exact readback_covered frame (plan.packet.checked.countsCovered clause member).1 branch known

/-- Actual nonempty-where packet input readbacks have source-label-mass-bounded
constructor depth, including inputs used only by associated outputs. -/
theorem readback_depth
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (nonempty : plan.packet.declaration.requirements ≠ [])
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels) :
 ∃ capture, Captures plan model capture ∧
 (∀ name ∈ plan.packet.declaration.inputNames, Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name (capture name)) ∧
 (∀ name ∈ plan.packet.declaration.inputNames, GeneralPatternAdditiveDepth253.depth (capture name) ≤ mass labels) ∧
 mass (substArgs (images capture) (normalizeArgs plan.packet.declaration.head)) ≤ mass labels := by
 obtain ⟨capture,captures,parts,sizes,headBound⟩ := readback frame nonempty branch known
 refine ⟨capture,captures,parts,?_,headBound⟩
 intro name member
 exact Nat.le_trans (GeneralPatternAdditiveDepth253.depth_le_size _) (sizes name member)

/-- This version also covers leaf declarations whose normalized head passes
the explicit syntactic coverage check. It does not assume a readback bound. -/
theorem readback_depth_covered
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (coveredHead : coveredArgs (normalizeArgs plan.packet.declaration.head) = true)
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels) :
 ∃ capture, Captures plan model capture ∧
 (∀ name ∈ plan.packet.declaration.inputNames, Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name (capture name)) ∧
 (∀ name ∈ plan.packet.declaration.inputNames, GeneralPatternAdditiveDepth253.depth (capture name) ≤ mass labels) ∧
 mass (substArgs (images capture) (normalizeArgs plan.packet.declaration.head)) ≤ mass labels := by
 obtain ⟨capture,captures,parts,sizes,headBound⟩ := readback_covered frame coveredHead branch known
 refine ⟨capture,captures,parts,?_,headBound⟩
 intro name member
 exact Nat.le_trans (GeneralPatternAdditiveDepth253.depth_le_size _) (sizes name member)
end Yulang.GeneralNominalAllHeadReadback253
