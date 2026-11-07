import Yulang.CommonSolvedCoreSyntax

/-!
# The finite common inference entry for the extended Core fragment

`Core.infer` classifies the actual finite list of solved common schemes.
An empty list is rejected; a nonempty list is inferred. The unsupported
constructor is available in the result vocabulary but is never returned by
this entry.

The public entry uses the independent constructor judgment
`CommonSyntax.model Common.model`: the old presence forms, literals,
structural data, strict application, transparent leaves and singleton unguarded
name cases. Data containing nominal/list values and general cases, effects,
roles and casts are not rules of this judgment yet. Thus `.rejected` means
untypable in this declared fragment, not untypable in every other Yulang model.

`PresenceOnly.infer` retains the previous entry and all of its theorems with
their original statements. On the old presence syntax the actual solved lists
and classification are literally unchanged, including whole defaults.
-/

namespace Yulang.Core.CommonInference

open CommonSolvedSource (Scheme)

inductive Result where
  | inferred : List Scheme → Result
  | rejected : Result
  | unsupported : Result

def Result.schemes : Result → List Scheme
  | .inferred schemes => schemes
  | .rejected | .unsupported => []

instance : Membership Scheme Result where
  mem result scheme := scheme ∈ result.schemes

@[simp] theorem Result.mem_schemes (scheme : Scheme) (result : Result) :
    scheme ∈ result ↔ scheme ∈ result.schemes := Iff.rfl

def Result.Instance (result : Result) (target : PresenceGeneration.Comp Common.model) : Prop :=
  ∃ scheme ∈ result, ∃ parameters : scheme.Parameters,
    PresenceGeneration.Comp.le Common.model (scheme.instantiate parameters) target

def finish : List Scheme → Result
  | [] => .rejected
  | first :: rest => .inferred (first :: rest)

@[simp] theorem finish_schemes (schemes : List Scheme) : (finish schemes).schemes = schemes := by
  cases schemes <;> rfl

theorem finish_rejected_iff (schemes : List Scheme) : finish schemes = .rejected ↔ schemes = [] := by
  cases schemes <;> simp [finish]

theorem finish_ne_unsupported (schemes : List Scheme) : finish schemes ≠ .unsupported := by
  cases schemes <;> simp [finish]

end Yulang.Core.CommonInference

namespace Yulang.Core.PresenceOnly

/-- Actual finite inference in the common presence model. No successful
check, semantic model, typing derivation, or caller fuel is an input. -/
def infer (expression : Required.Term) : CommonInference.Result :=
  CommonInference.finish (CommonSolvedSource.inferCore expression)

@[simp] theorem infer_schemes (expression : Required.Term) :
    (infer expression).schemes = CommonSolvedSource.inferCore expression :=
  CommonInference.finish_schemes _

@[simp] theorem infer_embed (expression : Inference.Expr) :
    infer (Required.embed expression) = CommonInference.finish (CommonSolvedSource.inferSource expression) := by
  rw [infer, CommonSolvedSource.inferCore_embed]

/-- All Core inputs are classified by the independent presence model;
unsupported syntax for that model contributes no schemes. -/
theorem infer_ne_unsupported (expression : Required.Term) : infer expression ≠ .unsupported :=
  CommonInference.finish_ne_unsupported _

theorem infer_rejected_iff_nil (expression : Required.Term) :
    infer expression = .rejected ↔ CommonSolvedSource.inferCore expression = [] :=
  CommonInference.finish_rejected_iff _

theorem infer_instantiates (expression : Required.Term) (scheme : CommonSolvedSource.Scheme)
    (member : scheme ∈ infer expression) (parameters : scheme.Parameters) :
    Typing (PresenceGeneration.CoreRules.model Common.model) [] expression (scheme.instantiate parameters) :=
  CommonSolvedSource.core_instantiates expression scheme
    (by simpa only [CommonInference.Result.mem_schemes, infer_schemes] using member) parameters

/-- Every closed Core term and every result in the independent common
presence model. The parameters are an ordinary unrestricted product. -/
theorem infer_principal (expression : Required.Term) (result : PresenceGeneration.Comp Common.model) :
    Typing (PresenceGeneration.CoreRules.model Common.model) [] expression result ↔
      ∃ scheme ∈ infer expression, ∃ parameters : scheme.Parameters,
        PresenceGeneration.Comp.le Common.model (scheme.instantiate parameters) result := by
  simpa only [CommonInference.Result.mem_schemes, infer_schemes] using
    CommonSolvedSource.core_principal expression result

theorem infer_instances_exact (expression : Required.Term) (result : PresenceGeneration.Comp Common.model) :
    (infer expression).Instance result ↔
      Typing (PresenceGeneration.CoreRules.model Common.model) [] expression result :=
  (infer_principal expression result).symm

/-- Rejection means precisely the absence of any typing in this presence
model, without a syntax/support premise or a successful inference premise. -/
theorem infer_rejected_iff (expression : Required.Term) :
    infer expression = .rejected ↔
      ¬ ∃ result, Typing (PresenceGeneration.CoreRules.model Common.model) [] expression result :=
  (infer_rejected_iff_nil expression).trans (CommonSolvedSource.core_empty_iff expression)

end Yulang.Core.PresenceOnly

namespace Yulang.Core

/-- Finite solved inference for `CommonSyntax.model Common.model`. This
entry takes only the original Core term, with no caller fuel or proof input.
The module documentation states the current constructor range explicitly. -/
def infer (expression : Required.Term) : CommonInference.Result :=
  CommonInference.finish (CommonSolvedCoreSyntax.infer expression)

@[simp] theorem infer_schemes (expression : Required.Term) :
    (infer expression).schemes = CommonSolvedCoreSyntax.infer expression :=
  CommonInference.finish_schemes _

@[simp] theorem infer_embed (expression : Inference.Expr) :
    infer (Required.embed expression) = CommonInference.finish (CommonSolvedSource.inferSource expression) := by
  rw [infer, CommonSolvedCoreSyntax.infer_embed]

/-- Classification is total relative to the declared common constructor
model. Absence of a rule in that model is not a full-language rejection claim. -/
theorem infer_ne_unsupported (expression : Required.Term) : infer expression ≠ .unsupported :=
  CommonInference.finish_ne_unsupported _

theorem infer_rejected_iff_nil (expression : Required.Term) :
    infer expression = .rejected ↔ CommonSolvedCoreSyntax.infer expression = [] :=
  CommonInference.finish_rejected_iff _

/-- Every returned scheme and every unrestricted parameter assignment has a
typing in the same independent constructor judgment. -/
theorem infer_instantiates (expression : Required.Term) (scheme : CommonSolvedSource.Scheme)
    (member : scheme ∈ infer expression) (parameters : scheme.Parameters) :
    Typing (CommonSyntax.model Common.model) [] expression (scheme.instantiate parameters) :=
  CommonSolvedCoreSyntax.all_parameter_sound expression scheme
    (by simpa only [CommonInference.Result.mem_schemes, infer_schemes] using member) parameters

/-- All closed terms and all Common results in this model. No support,
success, fuel, closed-cache or residual premise is required. -/
theorem infer_principal (expression : Required.Term) (result : PresenceGeneration.Comp Common.model) :
    Typing (CommonSyntax.model Common.model) [] expression result ↔
      ∃ scheme ∈ infer expression, ∃ parameters : scheme.Parameters,
        PresenceGeneration.Comp.le Common.model (scheme.instantiate parameters) result := by
  simpa only [CommonInference.Result.mem_schemes, infer_schemes] using
    CommonSolvedCoreSyntax.principal expression result

theorem infer_instances_exact (expression : Required.Term) (result : PresenceGeneration.Comp Common.model) :
    (infer expression).Instance result ↔
      Typing (CommonSyntax.model Common.model) [] expression result :=
  (infer_principal expression result).symm

/-- Rejection is exactly the absence of any result typing in the explicitly
declared common fragment. This does not classify other Core typing models. -/
theorem infer_rejected_iff (expression : Required.Term) :
    infer expression = .rejected ↔
      ¬ ∃ result, Typing (CommonSyntax.model Common.model) [] expression result :=
  (infer_rejected_iff_nil expression).trans (CommonSolvedCoreSyntax.empty_iff_untypable expression)

/-- The previous presence entry returns exactly the same result on every
old supported Core term, not merely an equivalent collection of instances. -/
theorem infer_presence (expression : Required.Term)
    (within : InferenceSyntax.supported expression = true) :
    infer expression = PresenceOnly.infer expression := by
  rw [infer, PresenceOnly.infer, CommonSolvedCoreSyntax.presence_schemes expression within]

/-- Old presence typings, including presence/default constraints, remain
typings in the extended model. Coverage is derived from the old derivation. -/
theorem infer_presence_typing_preserved (expression : Required.Term)
    (result : PresenceGeneration.Comp Common.model)
    (typed : Typing (PresenceGeneration.CoreRules.model Common.model) [] expression result) :
    Typing (CommonSyntax.model Common.model) [] expression result :=
  CommonSolvedCoreSyntax.presence_typing_preserved expression result typed

end Yulang.Core
