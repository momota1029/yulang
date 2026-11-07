import Yulang.CoreCommonSyntaxExact
import Yulang.CommonSolvedSource

/-!
# Finite solved inference for the extended common Core judgment

The compiler lowers literals, structural data, strict application and singleton
unguarded name cases into the existing finite presence solver. Every lowering
has been proved against an independent constructor rule. Captured polymorphic
environments, source sharing and both old presence let rules are retained.

The syntactic gate is internal to the algorithm. None of the public exactness,
all-parameter soundness or rejection theorems assumes coverage, success, fuel,
a closed cache or a residual predicate. Outside the explicitly declared common
fragment both this judgment and this solved list are empty; this says nothing
about typing in a different, fuller Yulang model.
-/

namespace Yulang.CommonSolvedCoreSyntax

open Core.PresenceGeneration (Comp)
open CommonSolvedSource (Scheme)

def infer (expression : Core.Required.Term) : List Scheme :=
  if Core.CommonSyntax.covered expression then
    CommonSolvedSource.inferSource (Core.CommonSyntax.lower expression)
  else []

@[simp] theorem infer_embed (expression : Inference.Expr) :
    infer (Core.Required.embed expression) = CommonSolvedSource.inferSource expression := by
  simp [infer]

/-- Every returned scheme, and every ordinary unrestricted parameter product,
gives a typing in the same extended constructor model. -/
theorem all_parameter_sound (expression : Core.Required.Term) (scheme : Scheme)
    (returned : scheme ∈ infer expression) (parameters : scheme.Parameters) :
    Core.Typing (Core.CommonSyntax.model Common.model) [] expression (scheme.instantiate parameters) := by
  cases within : Core.CommonSyntax.covered expression with
  | false => simp [infer, within] at returned
  | true =>
      exact (Core.CommonSyntax.lowering_exact expression within (Core.CommonSyntax.EnvRel.nil Common.model) _).mpr
        (CommonSolvedSource.source_instantiates (Core.CommonSyntax.lower expression) scheme
          (by simpa [infer, within] using returned) parameters)

/-- Every Core input and every Common result, with no additional premise.
The right side is the actual finite list and ordinary free parameters. -/
theorem principal (expression : Core.Required.Term) (result : Comp Common.model) :
    Core.Typing (Core.CommonSyntax.model Common.model) [] expression result ↔
      ∃ scheme ∈ infer expression, ∃ parameters : scheme.Parameters,
        Comp.le Common.model (scheme.instantiate parameters) result := by
  change Core.CommonSyntax.Typing Common.model [] expression result ↔ _
  cases within : Core.CommonSyntax.covered expression with
  | false =>
      constructor
      · intro typed
        have accepted := Core.CommonSyntax.typing_covered typed
        simp [within] at accepted
      · rintro ⟨scheme, returned, _⟩
        simp [infer, within] at returned
  | true =>
      simpa only [infer, within, ↓reduceIte] using
        (Core.CommonSyntax.lowering_exact expression within (Core.CommonSyntax.EnvRel.nil Common.model) result).trans
          (CommonSolvedSource.source_principal (Core.CommonSyntax.lower expression) result)

/-- Absence of a scheme is exactly absence of a result typing in this model;
unsupported constructors are not silently compiled as the fallback literal. -/
theorem empty_iff_untypable (expression : Core.Required.Term) :
    infer expression = [] ↔
      ¬ ∃ result, Core.Typing (Core.CommonSyntax.model Common.model) [] expression result := by
  cases within : Core.CommonSyntax.covered expression with
  | false =>
      simp only [infer, within, Bool.false_eq_true, ↓reduceIte, true_iff]
      rintro ⟨result, typed⟩
      have accepted := Core.CommonSyntax.typing_covered typed
      simp [within] at accepted
  | true =>
      simp only [infer, within, ↓reduceIte, CommonSolvedSource.source_empty_iff]
      apply not_congr
      apply exists_congr
      intro result
      exact (Core.CommonSyntax.lowering_exact expression within (Core.CommonSyntax.EnvRel.nil Common.model) result).symm

/-- Every expression accepted by the original presence syntax has literally
the same solved schemes. No old instance or presence comparison is dropped. -/
theorem presence_schemes (expression : Core.Required.Term)
    (within : Core.InferenceSyntax.supported expression = true) :
    infer expression = CommonSolvedSource.inferCore expression := by
  have recovered := Core.InferenceSyntax.embed_decode expression within
  rw [← recovered, infer_embed, CommonSolvedSource.inferCore_embed]

/-- Previous closed presence typings are preserved, including whole defaults
and captured value-let schemes. The syntactic fact is derived internally. -/
theorem presence_typing_preserved (expression : Core.Required.Term) (result : Comp Common.model)
    (typed : Core.Typing (Core.PresenceGeneration.CoreRules.model Common.model) [] expression result) :
    Core.Typing (Core.CommonSyntax.model Common.model) [] expression result := by
  apply (principal expression result).mpr
  rw [presence_schemes expression (Core.PresenceGeneration.CoreRules.typing_syntax typed)]
  exact (CommonSolvedSource.core_principal expression result).mp typed

end Yulang.CommonSolvedCoreSyntax
