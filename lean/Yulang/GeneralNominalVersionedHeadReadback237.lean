import Yulang.GeneralNominalVersionedWeightedHead237

/-! Finite capture existence and minimum labels follow from the actual head
schema's weight inequality. Only unnamed child uses require finite captures. -/
namespace Yulang.GeneralNominalVersionedHeadReadback237
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

theorem finite_capture
    (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
    (nonempty : plan.packet.declaration.requirements ≠ [])
    (branch : GeneralNominalVersionedPlans231.Holds plan model)
    (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
    (needed : GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ pattern, Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name pattern := by
  classical
  apply Classical.byContradiction
  intro absent
  let substitution : Roles.Subst := fun other =>
    if other = name then GeneralNominalCenteredCaptureLabels.large (mass labels) else .var other
  have weighted := head_weight frame nonempty branch known substitution (by
    intro other pattern finite
    have different : other ≠ name := by
      intro same; subst other; exact absent ⟨pattern,finite⟩
    simpa only [substitution,different,ite_false,Roles.Term.size] using Nat.succ_le_of_lt pattern.encode.size_pos)
  have lower := GeneralNominalCenteredCaptureLabels.variables_bound
    (normalizeArgs plan.packet.declaration.head) substitution
    (GeneralNominalCenteredHeadMatSemanticLabels.needed_in_head needed)
  have large : (substitution name).size = mass labels + 1 := by
    simp only [substitution,ite_true,GeneralNominalCenteredCaptureLabels.large_size]
  omega

private theorem least (predicate : Nat → Prop) (nonempty : ∃ value, predicate value) :
    ∃ value, predicate value ∧ ∀ other, predicate other → value ≤ other := by
  classical
  obtain ⟨value,present⟩ := nonempty
  induction value using Nat.strongRecOn with
  | ind value ih =>
      by_cases smaller : ∃ other, other < value ∧ predicate other
      · obtain ⟨other,below,known⟩ := smaller
        exact ih other below known
      · exact ⟨value,present,fun other known => by
          by_cases below : value ≤ other
          · exact below
          · exact False.elim (smaller ⟨other,by omega,known⟩)⟩

theorem minimum_capture
    (available : ∃ pattern, Part semantics plan model name pattern) :
    ∃ pattern, Part semantics plan model name pattern ∧
      ∀ other, Part semantics plan model name other → pattern.encode.size ≤ other.encode.size := by
  have nonempty : ∃ size, ∃ pattern, Part semantics plan model name pattern ∧ pattern.encode.size = size := by
    obtain ⟨pattern,known⟩ := available
    exact ⟨pattern.encode.size,pattern,known,rfl⟩
  obtain ⟨size,⟨pattern,known,same⟩,minimal⟩ := least _ nonempty
  exact ⟨pattern,known,fun other valid => same ▸ minimal _ ⟨other,valid,rfl⟩⟩

theorem readback
    (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
    (nonempty : plan.packet.declaration.requirements ≠ [])
    (branch : GeneralNominalVersionedPlans231.Holds plan model)
    (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels) :
    ∃ capture, Captures plan model capture ∧
      mass (substArgs (images capture) (normalizeArgs plan.packet.declaration.head)) ≤ mass labels := by
  classical
  let semantics := algebra plan.packet.registry.constructors plan.packet.context.interpretation
  have witnesses : ∀ name, GeneralNominalSharedCaptures.Needed plan.packet name →
      ∃ pattern, Part semantics plan model name pattern ∧
        ∀ other, Part semantics plan model name other → pattern.encode.size ≤ other.encode.size :=
    fun name needed => minimum_capture (finite_capture frame nonempty branch known needed)
  let capture : Nat → Pattern := fun name => if needed : GeneralNominalSharedCaptures.Needed plan.packet name
    then Classical.choose (witnesses name needed) else .var name
  have normals (name : Nat) : GeneralPatternNormalForm.Normal (capture name) := by
    by_cases needed : GeneralNominalSharedCaptures.Needed plan.packet name
    · simpa only [capture,dite_eq_left needed] using (Classical.choose_spec (witnesses name needed)).1.1.2
    · simp only [capture,dite_eq_right needed,GeneralPatternNormalForm.Normal]
  have fixed (name : Nat) : normalize (capture name) = capture name := GeneralPatternNormalForm.fixed _ (normals name)
  have meaning (name : Nat) (needed : GeneralNominalSharedCaptures.Needed plan.packet name) :
      Part semantics plan model name (capture name) := by
    simpa only [capture,dite_eq_left needed] using (Classical.choose_spec (witnesses name needed)).1
  have captures : Captures plan model capture := by
    refine ⟨fun name => ?_,fun name needed => ?_⟩
    · rw [fixed]; exact GeneralPatternNormalForm.covered_normal _ (normals name)
    · have finite := meaning name needed
      exact ⟨by rw [fixed]; exact finite.1.1,
        by rw [fixed]; exact GeneralPatternNormalForm.covered_normal _ finite.1.2,
        by rw [fixed]; exact finite.2⟩
  have imageFixed (name : Nat) : normalize (images capture name) = capture name := by
    simp only [images,fixed]
  have weighted := head_weight frame nonempty branch known
    (GeneralPatternConservativeSubstitution.captureTerms (images capture)) (by
      intro name pattern finite
      change (normalize (images capture name)).encode.size ≤ pattern.encode.size
      rw [imageFixed]
      by_cases needed : GeneralNominalSharedCaptures.Needed plan.packet name
      · simpa only [capture,dite_eq_left needed] using (Classical.choose_spec (witnesses name needed)).2 pattern finite
      · simpa only [capture,dite_eq_right needed,Pattern.encode,Roles.Term.size] using Nat.succ_le_of_lt pattern.encode.size_pos)
  obtain ⟨clause,member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have bound := (GeneralPatternConservativeSubstitution.substitutions_bounds (normalizeArgs plan.packet.declaration.head)
    (plan.packet.checked.countsCovered clause member).1 (images capture)).2
  exact ⟨capture,captures,Nat.le_trans bound weighted⟩


end Yulang.GeneralNominalVersionedHeadReadback237
