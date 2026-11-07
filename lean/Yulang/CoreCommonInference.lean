import Yulang.CommonSolvedSource

/-!
# The finite common inference entry for the Core presence fragment

`Core.infer` classifies the actual finite list of solved common schemes.
An empty list is rejected; a nonempty list is inferred. The unsupported
constructor is available in the result vocabulary but is never returned by
this entry.

The independent typing model is `PresenceGeneration.CoreRules.model
Common.model`. Other Core effect and qualified models are not identified with
this presence fragment, and their existing entries remain unchanged.
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

namespace Yulang.Core

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

end Yulang.Core
