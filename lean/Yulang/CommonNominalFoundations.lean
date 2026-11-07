import Yulang.CommonNominalTypingPreservation
import Yulang.CommonNominalCarrierConstraints
import Yulang.CommonNominalGroundAdapter

/-!
# Invariant nominal foundations with the old Common extension obligations

The local invariant theorem ranges over the same new regular carrier as every
structural constructor. The companion order, source-typing and actual old
solved-family theorems establish the conservative extension requirements.
Cast synthesis for arbitrary Common boundaries and construction generation
are separate B5 statements and are not claimed by these foundations.
-/

namespace Yulang.CommonNominalFoundations

open CommonNominalCarrier

/-- Every nominal ID and arity, with arbitrary value arguments of this same
nested/regular carrier and arbitrary invariant rows. The old Common extension
obligations are proved in `old_common_extension` below. -/
theorem common_nominal_invariant_exact (name other : Nat) (first last : List Argument) :
    CommonNominalCarrier.Subtype (nominal name first) (nominal other last) ↔
      name = other ∧ first.length = last.length ∧ ArgumentsEquivalent first last :=
  nominal_regular_invariant_exact name other first last

/-- The concrete extension obligations are recorded together, not assumed as
model laws or hidden parameter conditions. Existing source expressions,
returned schemes, their parameter products and all original result rows stay
unchanged. -/
structure OldCommonExtension : Prop where
  order : ∀ first last : Common.Ty,
    CommonNominalCarrier.Subtype (CommonNominalModelMap.value first) (CommonNominalModelMap.value last) ↔
      Common.Subtype first last
  presence : ∀ (environment : List (Core.PresenceGeneration.Binding Common.model))
      (expression : Inference.Expr) (result : Core.PresenceGeneration.Comp Common.model),
    Core.PresenceGeneration.Typing Common.model environment expression result →
      Core.PresenceGeneration.Typing model
        (environment.map CommonNominalTypingPreservation.binding) expression
        (CommonNominalTypingPreservation.comp result)
  common : ∀ (environment : List (Core.CommonSyntax.Binding Common.model))
      (expression : Core.Required.Term) (result : Core.PresenceGeneration.Comp Common.model),
    Core.CommonSyntax.Typing Common.model environment expression result →
      Core.CommonSyntax.Typing model
        (environment.map CommonNominalTypingPreservation.coreBinding) expression
        (CommonNominalTypingPreservation.comp result)
  schemeSound : ∀ (expression : Core.Required.Term) (scheme : CommonSolvedSource.Scheme),
    scheme ∈ Core.infer expression → ∀ parameters : scheme.Parameters,
      Core.Typing (Core.CommonSyntax.model model) [] expression
        (CommonNominalTypingPreservation.comp (scheme.instantiate parameters))
  schemeExact : ∀ (expression : Core.Required.Term) (result : Core.PresenceGeneration.Comp Common.model),
    (∃ scheme ∈ Core.infer expression, ∃ parameters : scheme.Parameters,
      Core.PresenceGeneration.Comp.le model
        (CommonNominalTypingPreservation.comp (scheme.instantiate parameters))
        (CommonNominalTypingPreservation.comp result)) ↔
      Core.Typing (Core.CommonSyntax.model Common.model) [] expression result

theorem old_common_extension : OldCommonExtension where
  order := CommonNominalModelMap.subtype_exact
  presence := fun _ _ _ => CommonNominalTypingPreservation.typing_preserved
  common := fun _ _ _ => CommonNominalTypingPreservation.core_typing_preserved_in_environment
  schemeSound := CommonNominalTypingPreservation.old_solver_all_parameters
  schemeExact := CommonNominalTypingPreservation.old_solver_instances_exact

end Yulang.CommonNominalFoundations
