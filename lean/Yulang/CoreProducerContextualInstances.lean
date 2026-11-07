import Yulang.CoreProducerLegacyInstances
import Yulang.ProducerContextualRegular
import Yulang.CorePresenceLegacyObstructions

/-!
# Concrete legacy-family contract for the contextual regular producer order

This is an actual instantiation of the solved-family migration theorem. Its
only algebraic input is the existing row algebra. The producer order is the
concrete all-depth, all-rank demand order, with arbitrary type-parameter
assignments, explicit role-head observations, and full arrow decomposition
against every regular target type.

The direct instance interpretation retains the original scheme evaluator and
all free parameters. It is sound for independent typing in the new regular
model, and preserves/reflects old instances modulo demand equality. The
converse from independent new typing to these same solved families, for every
old supported source, is proved in `CoreContextualSourceInference` after the
actual joint solver is connected. Presence defaults and exact empty records
are not added by reinterpreting this legacy entry.
-/

namespace Yulang.Core.ProducerContextualInstances

open ProducerLegacyInstances (Value Computation)

universe u
variable {Row : Type u}

def order (algebra : RowFlowSchemes.Algebra Row) : ProducerLegacyInstances.OrderExtension algebra where
  le := ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Row) algebra.le
  old_preserved := ProducerContextualRegular.structural_subtype_preserved
    (graph := RegularInferenceModel.graph Row) (leRow := algebra.le) algebra.trans
  trans := ProducerContextualRegular.producerLe_trans
  union_upper first last := (ProducerContextualRegular.producerLe_union_iff _ _ _).mpr ⟨first, last⟩

abbrev Instance (algebra : RowFlowSchemes.Algebra Row) :=
  ProducerLegacyInstances.Instance algebra (order algebra)

abbrev Equivalent (algebra : RowFlowSchemes.Algebra Row) :=
  ProducerContextualRegular.ProducerEq (RegularInferenceModel.graph Row) algebra.le

/-- Every actual old result instance is accepted by the direct new-order
interpretation of the same finite schemes and unrestricted parameters. -/
theorem legacy_instances_preserved (algebra : RowFlowSchemes.Algebra Row)
    (result : SourcePrincipalInference.Result) (target : Computation Row)
    (accepted : result.Instance algebra target) : Instance algebra result target :=
  ProducerLegacyInstances.instances_preserved algebra (order algebra) result target accepted

/-- Reflection changes only the value type by demand equivalence; it keeps
the exact requested result row. There are no source-support or success
premises because this theorem applies to every result of the actual entry. -/
theorem legacy_instances_reflected (algebra : RowFlowSchemes.Algebra Row)
    (result : SourcePrincipalInference.Result) (target : Computation Row)
    (accepted : Instance algebra result target) :
    ∃ oldValue : Value Row, result.Instance algebra (oldValue, target.2) ∧
      Equivalent algebra oldValue target.1 :=
  ProducerLegacyInstances.instances_reflected algebra (order algebra) result target accepted

theorem legacy_instances_exact_modulo (algebra : RowFlowSchemes.Algebra Row)
    (result : SourcePrincipalInference.Result) (target : Computation Row) :
    Instance algebra result target ↔
      ∃ oldValue : Value Row, result.Instance algebra (oldValue, target.2) ∧
        Equivalent algebra oldValue target.1 :=
  ProducerLegacyInstances.instances_exact_modulo algebra (order algebra) result target

/-- For every old supported expression and every old result, the directly
evaluated new-order family is exactly the demand-equivalence closure of the
original independent typing judgment. Row antisymmetry is the inherited
legacy inference theorem's explicit hypothesis. -/
theorem source_instances_exact_modulo (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {a b}, algebra.le a b → algebra.le b a → a = b)
    (expression : Inference.Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (target : Computation Row) :
    Instance algebra (SourcePrincipalInference.infer expression) target ↔
      ∃ oldValue : Value Row,
        Inference.Typing (SourcePrincipalInference.model algebra) [] expression (oldValue, target.2) ∧
        Equivalent algebra oldValue target.1 :=
  ProducerLegacyInstances.source_instances_exact_modulo algebra (order algebra)
    rowAntisymm expression supported target

/-- These new instances also produce an independent typing derivation in the
concrete contextual regular model. No new typing derivation is used to define an
instance. The converse for old supported sources is supplied by
`Core.ContextualRequiredInference.legacy_source_typing_exact`. -/
theorem source_instances_sound (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {a b}, algebra.le a b → algebra.le b a → a = b)
    (expression : Inference.Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (target : Computation Row)
    (accepted : Instance algebra (SourcePrincipalInference.infer expression) target) :
    Inference.Typing (ProducerContextualRegular.model Row algebra.empty algebra.join algebra.le)
      [] expression target := by
  obtain ⟨oldValue, old, equivalent⟩ := legacy_instances_reflected algebra _ target accepted
  have typed := ProducerContextualRegular.legacy_instances_preserved algebra rowAntisymm
    expression supported (oldValue, target.2) old
  exact ConstraintProblems.typing_subsumption
    (ProducerContextualRegular.model Row algebra.empty algebra.join algebra.le)
    ProducerContextualRegular.producerLe_trans algebra.refl algebra.trans typed
    ⟨equivalent.1, algebra.refl _⟩

/-- Reinterpreting the family changes no computation or status tag. -/
theorem unsupported_has_no_instance (algebra : RowFlowSchemes.Algebra Row) (target : Computation Row) :
    ¬ Instance algebra .unsupported target := fun impossible => impossible

theorem rejected_has_no_instance (algebra : RowFlowSchemes.Algebra Row) (target : Computation Row) :
    ¬ Instance algebra .rejected target := fun impossible => impossible

namespace DistributionExample

open PresenceLegacyObstructions

/-- The precise witness that obstructed literal legacy-instance equality is
equal under the new demand order, for every row relation. -/
theorem factorised_equivalent_distributed (leRow : Row → Row → Prop) :
    ProducerContextualRegular.ProducerEq (RegularInferenceModel.graph Row) leRow
      factorised distributed := by
  have pointwise : ∀ depth, ProducerContextual.ProducerEq leRow
      ((factorised : Value Row).eval (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth))
      ((distributed : Value Row).eval (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth)) := by
    intro depth
    cases depth with
    | zero =>
        exact ProducerContextual.producerEq_symm
          (ProducerContextual.producerEq_union_absorb (ProducerContextual.producerLe_refl _))
    | succ depth =>
        exact ProducerContextual.pair_union_last _ _ _
  exact ⟨fun depth => (pointwise depth).1, fun depth => (pointwise depth).2⟩

/-- The unchanged old source now has the distributed result as a directly
interpreted scheme instance; the old instance relation still rejects it. -/
theorem distributed_instance (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {a b}, algebra.le a b → algebra.le b a → a = b) :
    Instance algebra (SourcePrincipalInference.infer source) (distributed, algebra.empty) ∧
      ¬ (SourcePrincipalInference.infer source).Instance algebra (distributed, algebra.empty) := by
  refine ⟨(legacy_instances_exact_modulo algebra _ _).mpr ?_,
    source_not_distributed_instance algebra rowAntisymm algebra.empty⟩
  exact ⟨factorised, source_minimum_instance algebra rowAntisymm,
    factorised_equivalent_distributed algebra.le⟩

end DistributionExample

end Yulang.Core.ProducerContextualInstances
