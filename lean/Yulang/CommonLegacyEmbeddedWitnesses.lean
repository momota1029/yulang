import Yulang.CommonLegacyGenerationTranslation

/-!
# Old contextual typing and shared embedded witnesses of the real generator

For every required-field source and every old result, old contextual typing
is equivalent to an actual presence clause satisfied by one shared embedded
old assignment, with the output slot equal to the requested result. This
retains all generated binder slots and the exact output row.

The missing general reflection step is now isolated: given an arbitrary
common witness at an embedded old result, produce such a shared old witness.
The theorem below does not assume or prove this remaining existence claim.
-/

namespace Yulang.CommonLegacyEmbeddedWitnesses

open Core.PresenceGeneration PresenceNormalForm
open CommonLegacyEmptyReflection (legacyModel contextualModel)
open CommonLegacyGenerationTranslation
open CommonLegacyGeneratedAtoms (generated_atoms_exact)
open Inference (Expr)

/-- Old contextual typing is exactly the existence of an actual presence
clause with a shared old assignment, including the fixed output slot. -/
theorem embedded_witnesses_iff_typing (expression : Expr)
    (required : expression.requiredFieldsOnly = true) (target : Inference.Comp legacyModel) :
    (∃ clause ∈ normalise (principal ([] : SchemeEnv Empty) expression),
      ∃ values : Fin (clause.locals + 1) → Inference.Comp legacyModel,
        values (Fin.last clause.locals) = target ∧
          All Common.model (CommonLegacyTyping.assignment values) clause.pack) ↔
      Inference.Typing contextualModel [] expression target := by
  constructor
  · rintro ⟨clause, member, values, output, held⟩
    apply (ConstraintNormalForm.closed_source_exact contextualModel expression target).mpr
    refine ⟨translateClause clause, generated_clause expression required clause member, values, output, ?_⟩
    exact (generated_atoms_exact expression clause member _
      (generated_pack_translation expression required clause member) values).mp held
  · intro typed
    obtain ⟨oldClause, member, values, output, held⟩ :=
      (ConstraintNormalForm.closed_source_exact contextualModel expression target).mp typed
    have translated := normalise_translation (principal ([] : SchemeEnv Empty) expression)
    rw [principal_translation expression required] at translated
    simp only [translateEnv, List.map_nil] at translated
    rw [← translated] at member
    obtain ⟨clause, included, rfl⟩ := List.mem_map.mp member
    refine ⟨clause, included, values, output, ?_⟩
    exact (generated_atoms_exact expression clause included _
      (generated_pack_translation expression required clause included) values).mpr held

/-- Contextual old typing, not just old structural typing, preserves into
the independent common presence judgment. No old solver support is needed. -/
theorem contextual_typing_preserved (expression : Expr)
    (required : expression.requiredFieldsOnly = true) (target : Inference.Comp legacyModel)
    (typed : Inference.Typing contextualModel [] expression target) :
    Typing Common.model [] expression (Common.embedComp target) := by
  obtain ⟨clause, member, values, output, held⟩ :=
    (embedded_witnesses_iff_typing expression required target).mpr typed
  apply (closed_source_exact Common.model expression (Common.embedComp target)).mpr
  refine ⟨clause, member, CommonLegacyTyping.assignment values, ?_, held⟩
  change Common.embedComp (values (Fin.last clause.locals)) = Common.embedComp target
  rw [output]

end Yulang.CommonLegacyEmbeddedWitnesses
