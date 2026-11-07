import Yulang.CommonPresenceSolvedSource
import Yulang.CommonLegacyTyping

/-!
# The public common presence inference result

Inference returns finite solved families and distinguishes unsupported Core
syntax from an empty set of solutions. Every member carries unrestricted
row/type parameters; its instance predicate is ordinary output subsumption.
The syntax boundary is the existing presence Core fragment, including
functions, applications, both let branches, records and whole defaults.
-/

namespace Yulang.Core

open PresenceGeneration (Comp)
open CommonPresenceSolvedSource (Scheme)

inductive InferenceResult where
  | unsupported
  | rejected
  | inferred : List Scheme → InferenceResult

abbrev InferenceStatus := SourcePrincipalInference.Status

def InferenceResult.status : InferenceResult → InferenceStatus
  | .unsupported => .unsupported
  | .rejected => .rejected
  | .inferred _ => .inferred

def InferenceResult.schemes : InferenceResult → List Scheme
  | .inferred schemes => schemes
  | _ => []

instance : Membership Scheme InferenceResult where
  mem result scheme := scheme ∈ result.schemes

def InferenceResult.Instance (result : InferenceResult) (target : Comp Common.model) : Prop :=
  ∃ scheme ∈ result, ∃ parameters : scheme.Parameters,
    Comp.le Common.model (scheme.instantiate parameters) target

def InferenceResult.ofSchemes : List Scheme → InferenceResult
  | [] => .rejected
  | first :: rest => .inferred (first :: rest)

@[simp] theorem InferenceResult.ofSchemes_schemes (schemes : List Scheme) :
    (ofSchemes schemes).schemes = schemes := by
  cases schemes <;> rfl

@[simp] theorem InferenceResult.ofSchemes_rejected_iff (schemes : List Scheme) :
    (ofSchemes schemes).status = .rejected ↔ schemes = [] := by
  cases schemes <;> simp [ofSchemes, status]

@[simp] theorem InferenceResult.ofSchemes_not_unsupported (schemes : List Scheme) :
    (ofSchemes schemes).status ≠ .unsupported := by
  cases schemes <;> simp [ofSchemes, status]

/-- The public finite algorithm: the established Core syntax gate, source
lowering, clause normalization and actual free-family solver. -/
def infer (expression : Required.Term) : InferenceResult :=
  if InferenceSyntax.supported expression then
    InferenceResult.ofSchemes
      (CommonPresenceSolvedSource.inferSource (PresenceGeneration.CoreRules.decode expression))
  else .unsupported

theorem infer_schemes (expression : Required.Term) :
    (infer expression).schemes = CommonPresenceSolvedSource.inferCore expression := by
  cases checked : InferenceSyntax.supported expression with
  | false => simp [infer, CommonPresenceSolvedSource.inferCore, checked, InferenceResult.schemes]
  | true => simp [infer, CommonPresenceSolvedSource.inferCore, checked]

/-- Every closed Core term and every common result, with no solver-success,
cache, residual-model, fuel or parameter-condition premise. Outside the
presence syntax fragment both sides are false. -/
theorem infer_principal (expression : Required.Term) (result : Comp Common.model) :
    Typing (PresenceGeneration.CoreRules.model Common.model) [] expression result ↔
      ∃ scheme ∈ infer expression, ∃ parameters : scheme.Parameters,
        Comp.le Common.model (scheme.instantiate parameters) result := by
  change Typing (PresenceGeneration.CoreRules.model Common.model) [] expression result ↔
    ∃ scheme ∈ (infer expression).schemes, ∃ parameters : scheme.Parameters,
      Comp.le Common.model (scheme.instantiate parameters) result
  rw [infer_schemes]
  exact CommonPresenceSolvedSource.core_principal expression result

theorem infer_instances_exact (expression : Required.Term) (result : Comp Common.model) :
    (infer expression).Instance result ↔
      Typing (PresenceGeneration.CoreRules.model Common.model) [] expression result :=
  (infer_principal expression result).symm

/-- All parameters of every returned family produce an actual independent
Core typing derivation. No condition on those parameters is omitted. -/
theorem infer_all_parameters (expression : Required.Term) (scheme : Scheme)
    (returned : scheme ∈ infer expression) (parameters : scheme.Parameters) :
    Typing (PresenceGeneration.CoreRules.model Common.model) [] expression
      (scheme.instantiate parameters) :=
  (infer_principal expression _).mpr
    ⟨scheme, returned, parameters, Common.subtype_refl _, Common.rowLe_refl _⟩

theorem infer_empty_iff_untypable (expression : Required.Term) :
    (infer expression).schemes = [] ↔
      ¬ ∃ result, Typing (PresenceGeneration.CoreRules.model Common.model) [] expression result := by
  constructor
  · intro empty ⟨result, typed⟩
    obtain ⟨scheme, member, _, _⟩ := (infer_principal expression result).mp typed
    change scheme ∈ (infer expression).schemes at member
    rw [empty] at member
    cases member
  · intro untypable
    cases found : (infer expression).schemes with
    | nil => rfl
    | cons first rest =>
        have member : first ∈ infer expression := by
          change first ∈ (infer expression).schemes
          rw [found]
          exact List.mem_cons_self
        exact False.elim (untypable
          ⟨first.instantiate first.defaultParameters,
            infer_all_parameters expression first member first.defaultParameters⟩)

/-- Rejection is exactly lack of a typing derivation on the entire declared
presence fragment, including invalid expressions within that syntax. -/
theorem infer_rejected_iff (expression : Required.Term)
    (fragment : InferenceSyntax.supported expression = true) :
    (infer expression).status = .rejected ↔
      ¬ ∃ result, Typing (PresenceGeneration.CoreRules.model Common.model) [] expression result := by
  rw [← infer_empty_iff_untypable expression]
  simp [infer, fragment]

theorem infer_not_unsupported (expression : Required.Term)
    (fragment : InferenceSyntax.supported expression = true) :
    (infer expression).status ≠ .unsupported := by
  simp [infer, fragment]

theorem infer_unsupported_iff (expression : Required.Term) :
    (infer expression).status = .unsupported ↔ InferenceSyntax.supported expression = false := by
  cases checked : InferenceSyntax.supported expression with
  | false => simp [infer, checked, InferenceResult.status]
  | true => simp [infer, checked]

/-- Old supported source instances are actual instances of the new solved
entry. The old target's row is embedded without any change. -/
theorem legacy_instances_preserved (expression : Inference.Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (result : Inference.Comp CommonLegacyTyping.oldModel)
    (accepted : (SourcePrincipalInference.infer expression).Instance Common.rowAlgebra result) :
    (infer (Required.embed expression)).Instance (Common.embedComp result) :=
  (infer_instances_exact _ _).mpr
    (CommonLegacyTyping.legacy_core_instances_preserved expression supported result accepted)

end Yulang.Core
