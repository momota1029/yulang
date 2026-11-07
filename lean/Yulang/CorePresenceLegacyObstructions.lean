import Yulang.SourcePrincipalInference
import Yulang.PresenceRegularLegacyBridge
import Yulang.StructuralDecisions
import Yulang.StructuralRowResolution

/-!
# An obstruction to a semantic replacement of the legacy subtype order

The legacy regular order is structural, and in particular does not distribute
a pair over a union in a component. The data interpretation does distribute.
This distinction is already observable on the actual principal instances of
a closed, supported, record-free source expression.

This does not rule out a conservative structural presence extension. It rules
out claiming that the existing data-inclusion bridge reflects the old subtype
order, or that a new inference relation closed under that inclusion has
exactly the old instances. No meaning of the legacy width type is changed.
-/

namespace Yulang.Core.PresenceLegacyObstructions

open Inference

universe u

variable {Row : Type u}

def factorisedTree : StructuralBase.Ty Row :=
  .pair (.base .int) (.union (.base .int) (.base .str))

def distributedTree : StructuralBase.Ty Row :=
  .union (.pair (.base .int) (.base .int)) (.pair (.base .int) (.base .str))

private theorem unit_not_distributed :
    ¬ StructuralBase.Subtype (fun (_ _ : Unit) => True)
      (factorisedTree : StructuralBase.Ty Unit) distributedTree := by
  intro below
  have accepted := (StructuralDecisions.check_exact (fun (_ _ : Unit) => true)
    (fun _ _ => by simp) (fun _ _ => trivial) factorisedTree distributedTree).mpr below
  have rejected : StructuralDecisions.check (fun (_ _ : Unit) => true)
      (factorisedTree : StructuralBase.Ty Unit) distributedTree = false := by
    decide +kernel
  rw [rejected] at accepted
  cases accepted

/-- The obstruction is independent of every row law: erase all row values
to a singleton before applying the kernel-checked structural decision. -/
theorem structural_not_distributed (leRow : Row → Row → Prop) :
    ¬ StructuralBase.Subtype leRow (factorisedTree : StructuralBase.Ty Row)
      distributedTree := by
  intro below
  apply unit_not_distributed
  simpa only [factorisedTree, distributedTree, StructuralRowResolution.mapRows] using
    StructuralRowResolution.subtype_map (fun (_ : Row) => ())
      (leB := fun _ _ => True) (fun _ => trivial) below

def factorised : RegularInferenceModel.Ty Row :=
  .pair (.node (.base .int)) (.node (.union (.base .int) (.base .str)))

def distributed : RegularInferenceModel.Ty Row :=
  .union (.pair (.node (.base .int)) (.node (.base .int)))
    (.pair (.node (.base .int)) (.node (.base .str)))

/-- A single actual finite observation refutes every regular subtype
derivation; no restriction is imposed on the ambient regular graph carrier. -/
theorem regular_not_distributed (leRow : Row → Row → Prop) :
    ¬ RegularInferenceModel.Subtype leRow (factorised : RegularInferenceModel.Ty Row)
      distributed := by
  intro below
  exact structural_not_distributed leRow (below 1)

/-- Predicate semantics forces this law for all three payload predicates,
including empty and overlapping predicates. -/
theorem pair_union_data_exact (left first last : PresenceDataTypes.Ty)
    (value : SourceDataRuntime.Value) :
    PresenceDataTypes.pair left (PresenceDataTypes.union first last) value ↔
      PresenceDataTypes.union (PresenceDataTypes.pair left first)
        (PresenceDataTypes.pair left last) value := by
  cases value <;> simp [PresenceDataTypes.pair, PresenceDataTypes.union, and_or_left]

/-- The failed structural comparison holds at every finite data observation,
not just after taking an unbounded or informal semantic limit. -/
theorem regular_data_distributes :
    PresenceRegularObservations.DataSubtype
      (PresenceRegularLegacyBridge.graph (RegularInferenceModel.graph Row))
      (PresenceRegularLegacyBridge.translate (factorised : RegularInferenceModel.Ty Row))
      (PresenceRegularLegacyBridge.translate distributed) := by
  intro depth
  cases depth with
  | zero =>
      intro value held
      cases value <;> simp [factorised, PresenceRegularLegacyBridge.translate,
        PresenceLayers.Layer.denote, PresenceLayers.Layer.meaning,
        PresenceRegularObservations.observe, PresenceDataTypes.pair,
        PresenceDataTypes.never] at held
  | succ depth =>
      change PresenceDataTypes.Le
        (PresenceDataTypes.pair (PresenceDataTypes.base .int)
          (PresenceDataTypes.union (PresenceDataTypes.base .int) (PresenceDataTypes.base .str)))
        (PresenceDataTypes.union
          (PresenceDataTypes.pair (PresenceDataTypes.base .int) (PresenceDataTypes.base .int))
          (PresenceDataTypes.pair (PresenceDataTypes.base .int) (PresenceDataTypes.base .str)))
      exact fun value held => (pair_union_data_exact _ _ _ value).mp held

/-- Thus the one missing implication in a proposed data/structural subtype
equivalence is false, even on finite data types containing no records. -/
theorem data_subtype_not_reflecting (leRow : Row → Row → Prop) :
    ¬ (∀ left right : RegularInferenceModel.Ty Row,
      PresenceRegularObservations.DataSubtype
        (PresenceRegularLegacyBridge.graph (RegularInferenceModel.graph Row))
        (PresenceRegularLegacyBridge.translate left)
        (PresenceRegularLegacyBridge.translate right) →
      RegularInferenceModel.Subtype leRow left right) := by
  intro reflects
  exact regular_not_distributed leRow (reflects factorised distributed regular_data_distributes)

/-- A closed source witness. `branch` is the legacy nonconstant conditional
constructor; its independent typing checks both alternatives. -/
def source : Expr :=
  .pair (.lit .int) (.branch (.lit .bool) (.lit .int) (.lit .str))

theorem source_recordFree : SourceConstraintSupport.RecordFree source := by
  simp [source, SourceConstraintSupport.RecordFree]

theorem source_supported : SourcePrincipalInference.supported source = true :=
  SourcePrincipalInference.recordFree_supported source source_recordFree

/-- Every declarative result of this particular source lies above the
factorised type. All result rows and all regular result types are quantified. -/
theorem source_lower_bound (algebra : RowFlowSchemes.Algebra Row)
    (target : Comp (SourcePrincipalInference.model algebra))
    (typed : Typing (SourcePrincipalInference.model algebra) [] source target) :
    RegularInferenceModel.Subtype algebra.le factorised target.1 := by
  cases typed with
  | pair first last pairBound =>
      cases first with
      | lit integerBound =>
          cases last with
          | branch _ yes no branchBound =>
              cases yes with
              | lit yesBound =>
                  cases no with
                  | lit noBound =>
                      apply RegularInferenceModel.subtype_trans _ pairBound.1
                      apply RegularInferenceModel.pair_subtype integerBound.1
                      apply RegularInferenceModel.subtype_trans _ branchBound.1
                      intro depth
                      exact StructuralBase.union_mono (yesBound.1 depth) (noBound.1 depth)

/-- The source is typable. This witness does not assume any successful
inference run or solver valuation. -/
theorem source_minimum_typing (algebra : RowFlowSchemes.Algebra Row) :
    Typing (SourcePrincipalInference.model algebra) [] source (factorised, algebra.empty) := by
  have emptyJoin : algebra.le (algebra.join algebra.empty algebra.empty) algebra.empty :=
    (algebra.join_le_iff _ _ _).mpr ⟨algebra.refl _, algebra.refl _⟩
  have emptyBranch : algebra.le
      (algebra.join algebra.empty (algebra.join algebra.empty algebra.empty)) algebra.empty :=
    (algebra.join_le_iff _ _ _).mpr ⟨algebra.refl _, emptyJoin⟩
  apply Typing.pair (m := SourcePrincipalInference.model algebra)
    (a := (.base .int, algebra.empty))
    (b := (.union (.base .int) (.base .str), algebra.empty))
  · exact .lit ⟨RegularInferenceModel.subtype_refl algebra.le _, algebra.refl _⟩
  · apply Typing.branch (m := SourcePrincipalInference.model algebra) (eg := algebra.empty)
      (a := (.base .int, algebra.empty)) (b := (.base .str, algebra.empty))
    · exact .lit ⟨RegularInferenceModel.subtype_refl algebra.le _, algebra.refl _⟩
    · exact .lit ⟨RegularInferenceModel.subtype_refl algebra.le _, algebra.refl _⟩
    · exact .lit ⟨RegularInferenceModel.subtype_refl algebra.le _, algebra.refl _⟩
    · exact ⟨RegularInferenceModel.subtype_refl algebra.le _, emptyBranch⟩
  · exact ⟨RegularInferenceModel.subtype_refl algebra.le _, emptyJoin⟩

/-- No result row can make the distributed target a legacy typing. -/
theorem source_not_distributed (algebra : RowFlowSchemes.Algebra Row) (row : Row) :
    ¬ Typing (SourcePrincipalInference.model algebra) [] source (distributed, row) :=
  fun typed => regular_not_distributed algebra.le (source_lower_bound algebra _ typed)

/-- This is a positive instance of the actual `SourcePrincipalInference`
return value; it is not an instance of an artificially supplied scheme. -/
theorem source_minimum_instance (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right) :
    (SourcePrincipalInference.infer source).Instance algebra (factorised, algebra.empty) :=
  (SourcePrincipalInference.infer_instances_exact algebra rowAntisymm source source_supported
    (factorised, algebra.empty)).mpr (source_minimum_typing algebra)

/-- Every free-parameter choice in every returned alternative is excluded
at the distributed target, for every result row. -/
theorem source_not_distributed_instance (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (row : Row) :
    ¬ (SourcePrincipalInference.infer source).Instance algebra (distributed, row) := by
  intro accepted
  exact source_not_distributed algebra row
    ((SourcePrincipalInference.infer_instances_exact algebra rowAntisymm source source_supported
      (distributed, row)).mp accepted)

/-- Any proposed new instance relation closed under *full data inclusion*
cannot preserve and reflect all old instances. The assumptions name exactly
the semantic design choice responsible; no new inference implementation or
new typing relation is introduced by this theorem. -/
theorem no_semantic_legacy_instance_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (newInstance : Expr → Comp (SourcePrincipalInference.model algebra) → Prop)
    (semanticSubsumption : ∀ expression left right row,
      PresenceRegularObservations.DataSubtype
        (PresenceRegularLegacyBridge.graph (RegularInferenceModel.graph Row))
        (PresenceRegularLegacyBridge.translate left)
        (PresenceRegularLegacyBridge.translate right) →
      newInstance expression (left, row) → newInstance expression (right, row)) :
    ¬ (∀ expression, SourcePrincipalInference.supported expression = true →
      ∀ target, (SourcePrincipalInference.infer expression).Instance algebra target ↔
        newInstance expression target) := by
  intro exact
  have first := (exact source source_supported (factorised, algebra.empty)).mp
    (source_minimum_instance algebra rowAntisymm)
  have last := semanticSubsumption source factorised distributed algebra.empty
    regular_data_distributes first
  exact source_not_distributed_instance algebra rowAntisymm algebra.empty
    ((exact source source_supported (distributed, algebra.empty)).mpr last)

end Yulang.Core.PresenceLegacyObstructions
