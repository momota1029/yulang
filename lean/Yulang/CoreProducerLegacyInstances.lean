import Yulang.SourcePrincipalInference

/-!
# Legacy solved families under an extended producer order

This module reinterprets the actual finite schemes and all of their unrestricted
value/row parameters. It does not define the new instances by existential
quantification over old instances or by old typing.

An extended producer order only needs to preserve old structural inequalities
and the union upper-bound rule. If an evaluated scheme value `a` is newly below
`c`, the old result `a | c` is an old instance and is newly equivalent to `c`.
This proves the preservation/reflection-modulo-equivalence contract at the
solved-family boundary. Connecting that view to an independent presence
judgment and a new solver is a separate theorem.
-/

namespace Yulang.Core.ProducerLegacyInstances

open Inference (Expr)
open SourcePrincipalInference (Alternative Principal Result)

universe u
variable {Row : Type u}

abbrev Value (Row : Type u) := RegularInferenceModel.Ty Row
abbrev Computation (Row : Type u) := Value Row × Row

/-- The laws are supplied by a concrete producer order, not by an instance
reflection assumption. No constructor distribution law is needed here. -/
structure OrderExtension (algebra : RowFlowSchemes.Algebra Row) where
  le : Value Row → Value Row → Prop
  old_preserved {left right} : RegularInferenceModel.Subtype algebra.le left right → le left right
  trans {left middle right} : le left middle → le middle right → le left right
  union_upper {left right bound} : le left bound → le right bound → le (.union left right) bound

variable (algebra : RowFlowSchemes.Algebra Row) (order : OrderExtension algebra)

def Equivalent (left right : Value Row) : Prop := order.le left right ∧ order.le right left

theorem le_refl (value : Value Row) : order.le value value :=
  order.old_preserved (RegularInferenceModel.subtype_refl algebra.le value)

/-- The old result constructed during reflection retains the exact requested
row and adds only a union with the evaluated value. -/
theorem reflected_value {evaluated target : Value Row} (below : order.le evaluated target) :
    RegularInferenceModel.Subtype algebra.le evaluated (.union evaluated target) ∧
      Equivalent algebra order (.union evaluated target) target := by
  refine ⟨fun _ => .unionLeft _ _, ?_, ?_⟩
  · exact order.union_upper below (le_refl algebra order target)
  · exact order.old_preserved (fun _ => .unionRight _ _)

/-- Direct parameter evaluation, followed by the new producer comparison. -/
def AlternativeInstance (alternative : Alternative) (target : Computation Row) : Prop :=
  ∃ rowParameter : Fin alternative.slots → Row,
    ∃ valueParameter : Fin alternative.scheme.size → Value Row,
      let evaluated := alternative.scheme.instantiate algebra rowParameter valueParameter alternative.output
      order.le evaluated.1 target.1 ∧ algebra.le evaluated.2 target.2

def Instance (result : Result) (target : Computation Row) : Prop :=
  match result with
  | .inferred principal => ∃ alternative ∈ principal, AlternativeInstance algebra order alternative target
  | .rejected | .unsupported => False

theorem alternative_preserved (alternative : Alternative) (target : Computation Row)
    (old : alternative.Instance algebra target) :
    AlternativeInstance algebra order alternative target := by
  obtain ⟨rows, values, bounded, rowBound⟩ := old
  exact ⟨rows, values, order.old_preserved bounded, rowBound⟩

theorem alternative_reflected (alternative : Alternative) (target : Computation Row)
    (accepted : AlternativeInstance algebra order alternative target) :
    ∃ oldValue : Value Row, alternative.Instance algebra (oldValue, target.2) ∧
      Equivalent algebra order oldValue target.1 := by
  obtain ⟨rows, values, bounded, rowBound⟩ := accepted
  let evaluated := alternative.scheme.instantiate algebra rows values alternative.output
  obtain ⟨oldBound, equivalent⟩ := reflected_value algebra order bounded
  exact ⟨.union evaluated.1 target.1, ⟨rows, values, oldBound, rowBound⟩, equivalent⟩

theorem alternative_subsumption (alternative : Alternative) {left right : Computation Row}
    (accepted : AlternativeInstance algebra order alternative left)
    (valueBound : order.le left.1 right.1)
    (rowBound : algebra.le left.2 right.2) :
    AlternativeInstance algebra order alternative right := by
  obtain ⟨rows, values, below, rowBelow⟩ := accepted
  exact ⟨rows, values, order.trans below valueBound, algebra.trans rowBelow rowBound⟩

/-- Every instance of every actual old result survives. Neither success nor
source supportedness is assumed; rejected/unsupported results are empty. -/
theorem instances_preserved (result : Result) (target : Computation Row)
    (old : result.Instance algebra target) : Instance algebra order result target := by
  cases result with
  | unsupported | rejected => exact False.elim old
  | inferred principal =>
      obtain ⟨alternative, member, accepted⟩ := old
      exact ⟨alternative, member, alternative_preserved algebra order alternative target accepted⟩

/-- Every direct new-order parameter instance has an actual old instance with
the same result row and a producer-equivalent value. All returned alternatives
and all old/new free parameters remain quantified. -/
theorem instances_reflected (result : Result) (target : Computation Row)
    (accepted : Instance algebra order result target) :
    ∃ oldValue : Value Row, result.Instance algebra (oldValue, target.2) ∧
      Equivalent algebra order oldValue target.1 := by
  cases result with
  | unsupported | rejected => exact False.elim accepted
  | inferred principal =>
      obtain ⟨alternative, member, accepted⟩ := accepted
      obtain ⟨oldValue, old, equivalent⟩ := alternative_reflected algebra order alternative target accepted
      exact ⟨oldValue, ⟨alternative, member, old⟩, equivalent⟩

theorem instances_exact_modulo (result : Result) (target : Computation Row) :
    Instance algebra order result target ↔
      ∃ oldValue : Value Row, result.Instance algebra (oldValue, target.2) ∧
        Equivalent algebra order oldValue target.1 := by
  constructor
  · exact instances_reflected algebra order result target
  · rintro ⟨oldValue, old, equivalent⟩
    have moved := instances_preserved algebra order result (oldValue, target.2) old
    cases result with
    | unsupported | rejected => exact False.elim moved
    | inferred principal =>
        obtain ⟨alternative, member, accepted⟩ := moved
        exact ⟨alternative, member, alternative_subsumption algebra order alternative accepted
          equivalent.1 (algebra.refl target.2)⟩

/-- The contract for every closed old supported expression and every old
result, now stated through the original independent source judgment. This
does not identify the left side with presence typing in a new concrete model. -/
theorem source_instances_exact_modulo
    (rowAntisymm : ∀ {a b}, algebra.le a b → algebra.le b a → a = b)
    (expression : Inference.Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (target : Computation Row) :
    Instance algebra order (SourcePrincipalInference.infer expression) target ↔
      ∃ oldValue : Value Row,
        Inference.Typing (SourcePrincipalInference.model algebra) [] expression (oldValue, target.2) ∧
        Equivalent algebra order oldValue target.1 := by
  rw [instances_exact_modulo]
  apply exists_congr
  intro oldValue
  rw [SourcePrincipalInference.infer_instances_exact algebra rowAntisymm expression supported]

end Yulang.Core.ProducerLegacyInstances
