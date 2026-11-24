import Yulang.GeneralDeclarativeI65I72FiniteSupport402
import Yulang.GeneralDeclarativeI65I72NativePriority403

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Result Summarizes)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOutputs320 (bodyPattern)

def DeclaredHead404 {s slots c p} (key : Nat) : NamedMixedTree401 s slots c p → Prop
  | .declaredApp n use _ _ _ => n = key ∧ ∃ ps, use.mode = .declared ps
  | _ => False

/-- The expected output still has its whole B6 term, exact producer
request, selected dictionary, original output ordinal and real target.
This direct-name fragment never silently follows an alias. -/
structure LiteralInputNeed404 (s : State) (a : Capture) (need : OutputNeed s) where
  key : Nat
  arguments : List Expr
  usesOriginalLower : need.expected.original.target = a.lower
  declared : DeclaredHead404 key need.expected.rhs
  nominalCode : fixedValueCode403 need.expected.rhs = some (.nominal key arguments)

def KeepsFixedOutputs404 (R : SourcePrimitives) : Prop :=
  ∀ s q (e : Event s q) needs, R.elected s q e needs →
    RetainedVariableOutputs403 e ∨ RetainedTypedValueRows403 e

theorem c403_keeps_both_fixed_backings404 : KeepsFixedOutputs404 variableWithNativeK2403 :=
  fun _ _ _ _ elected => elected.2.2

private theorem variable_body_does_not_project_nominal404 {s slots c p}
    (tree : NamedMixedTree401 s slots c p) {binder key args} (literal : p = .var binder) :
    fixedValueCode403 tree ≠ some (.nominal key args) := by
  subst p
  cases tree with
  | binder => intro bad; cases bad

private theorem selected_output_retained404 {R s q t e}
    (policy : KeepsFixedOutputs404 R) (trace : SourceTrace R s q t (some e)) :
    RetainedVariableOutputs403 e ∨ RetainedTypedValueRows403 e := by
  cases trace
  exact policy _ _ _ _ (by assumption)

/-- No separate authority, guessed head, solver flag or model. The
actual selected producer and its original named output are read from
the same finite proof forest that the consumer later uses. -/
theorem completed_input_owns_retained_nominal404 {R s a need}
    (policy : KeepsFixedOutputs404 R)
    (literal : LiteralInputNeed404 s a need) (done : ExactOutputSupport R s need) :
    (⟨a.lower,.nominal literal.key literal.arguments⟩ : Equation) ∈
      s.core.current.ordinary.equations := by
  let output := done.event.outputs need.ordinal
  have retained := selected_output_retained404 policy done.source
  have projected : fixedValueCode403 output.rhs = some (.nominal literal.key literal.arguments) := by
    exact (congrArg (fun r : NamedMixedReceipt401 s.core => fixedValueCode403 r.rhs)
      done.sameTypedOutput).trans literal.nominalCode
  have target : need.producer.demand.outputs[need.ordinal].target = a.lower :=
    (congrArg (fun r : NamedMixedReceipt401 s.core => r.original.target)
      done.sameTypedOutput).trans literal.usesOriginalLower
  rcases retained with alias|typed
  · obtain ⟨binder,_,written,_,_,_⟩ := alias need.ordinal
    exact (variable_body_does_not_project_nominal404 output.rhs written projected).elim
  · obtain ⟨rhs,code,mem⟩ := typed need.ordinal
    change fixedValueCode403 output.rhs = some rhs at code
    have exactCode := Option.some.inj (code.symm.trans projected)
    simpa only [target,exactCode] using mem

theorem support_at_literal_ordinal_yields_nominal404 {R s needs a need}
    (policy : KeepsFixedOutputs404 R) (forest : SupportForest R s needs)
    (slot : Nat) (atNeed : needs[slot]? = some need) (literal : LiteralInputNeed404 s a need) :
    (⟨a.lower,.nominal literal.key literal.arguments⟩ : Equation) ∈
      s.core.current.ordinary.equations :=
  completed_input_owns_retained_nominal404 policy literal (forest.atOriginal slot atNeed)

theorem wrong_target_is_not_direct_input_support404 {s a need}
    (wrong : need.expected.original.target ≠ a.lower) :
    ¬ Nonempty (LiteralInputNeed404 s a need) := by
  rintro ⟨use⟩
  exact wrong use.usesOriginalLower

/-- This is about the actual same diagnostic proof. A separate
pending derivation is not declared to rule out all later states. -/
theorem exact_support_is_not_pending404 {R s need} (support : ExactOutputSupport R s need) :
    ¬ Summarizes support.diagnostic .pending := by
  intro waiting
  have same := (CommonRoleOutermostResolver.classification_exact _ _).mpr support.completion
  have other := (CommonRoleOutermostResolver.classification_exact _ _).mpr waiting
  rw [same] at other
  cases other

theorem no_finite_selected_producer_no_support404 {R s need}
    (noCompletion : ¬ Classifies R s need.producer (.selected need.dictionary)) :
    ¬ Nonempty (ExactOutputSupport R s need) := by
  rintro ⟨ready⟩
  exact noCompletion ⟨ready.diagnostic,some ready.event,⟨ready.source⟩,ready.completion⟩

end Yulang.GeneralDeclarativeI65.I72
