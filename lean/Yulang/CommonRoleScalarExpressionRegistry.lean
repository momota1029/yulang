import Yulang.CommonRoleScalarRegistry
import Yulang.CommonRoleScalarExpressionInputs

/-!
# Annotated scalar source expressions to registry dictionaries

The caller passes an original expression, explicit int/str annotation, role and
visible scalar declarations. Validation, one ordinary slot, paired bounds,
ordinary consistency, materialization and the actual dictionary are computed.
Closed literal/variable/let expressions are the supported fragment. Other
forms are adapter failure, not general language rejection. No effects, where,
associated equations, parser lowering or general B4 source instance is claimed.
-/
namespace Yulang.CommonRoleScalarExpressionRegistry
open CommonRoleScalarDictionaryModels (Scalar)
open CommonRoleScalarRegistry (Entry Ready Outcome Implements)
open CommonRoleScalarExpressionInputs (Evaluates Meaning)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open RoleDictionaries (Answer Plan)

/-- An actual generated ordinary state, not an assumption supplied by callers. -/
def initial (scalar : Scalar) : State 1 :=
  CommonRoleCandidateStateFrontier.extend State.empty 0 scalar.base

def run (entries : List Entry) (role : Nat) (annotation : Scalar) (expression : Inference.Expr) : Option Outcome :=
  if CommonRoleScalarExpressionInputs.infer [] expression = some annotation.base then
    CommonRoleScalarRegistry.run entries role 0 (initial annotation)
  else none

/-- Independent original-expression and source-declaration judgments. -/
def Classify (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) (answer : Answer) : Prop :=
  Evaluates [] expression annotation.base ∧ Ready entries role annotation.term answer

/-- Soundness/completeness of the source outer entry. No success, ordinary
state, receiver slot, solved assignment or typed input is a caller premise. -/
theorem run_exact (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) (answer : Answer) :
    run entries role annotation expression = some (.ready answer) ↔
      Classify entries role annotation expression answer := by
  unfold run Classify
  by_cases valid : CommonRoleScalarExpressionInputs.infer [] expression = some annotation.base
  · have evaluated := (CommonRoleScalarExpressionInputs.infer_exact ..).mp valid
    simp only [valid, ↓reduceIte, evaluated, true_and, initial,
      CommonRoleScalarRegistry.run_recorded, Option.some.injEq, Outcome.ready.injEq]
    exact CommonRoleScalarRegistry.elaborate_exact entries role annotation.term answer
  · have invalid : ¬ Evaluates [] expression annotation.base := fun evaluated =>
      valid ((CommonRoleScalarExpressionInputs.infer_exact ..).mpr evaluated)
    simp [valid, invalid]

/-- Every supported, correctly annotated expression obtains an actual
classification. A missing/overlapping implementation is not adapter failure. -/
theorem run_exists_iff (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) :
    (∃ answer, run entries role annotation expression = some (.ready answer)) ↔
      Evaluates [] expression annotation.base := by
  constructor
  · rintro ⟨answer, returned⟩
    exact ((run_exact entries role annotation expression answer).mp returned).1
  · intro evaluated
    let answer := RoleDictionaries.elaborate (CommonRoleScalarRegistry.visible entries)
      (CommonRoleScalarRegistry.wellFormed entries) (CommonRoleScalarDictionaryModels.goal role annotation.term)
    exact ⟨answer, (run_exact entries role annotation expression answer).mpr
      ⟨evaluated, (CommonRoleScalarRegistry.elaborate_exact entries role annotation.term answer).mp rfl⟩⟩

/-- Explicit annotations supply the upper bound. Existing declarative typing
supplies the lower bound, for every permitted type of the original expression. -/
theorem initial_models (annotation : Scalar) (expression : Inference.Expr)
    (evaluated : Evaluates [] expression annotation.base) (value : Common.Ty)
    (meaning : Meaning expression annotation.base value) :
    PresenceNormalForm.All Common.model (fun _ => Comp.pure Common.model value) (initial annotation).atoms := by
  apply (CommonRoleCandidateStateFrontier.extend_exact ..).mpr
  exact ⟨(by intro atom member; cases member),
    (CommonRoleScalarExpressionInputs.meaning_exact evaluated value).mp meaning⟩

/-- Every returned actual dictionary is sound at every original-expression
model satisfying its annotation, not just the checker's canonical scalar. -/
theorem run_all_models (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) (dictionary : Plan)
    (returned : run entries role annotation expression = some (.ready (.resolved dictionary)))
    (value : Common.Ty) (meaning : Meaning expression annotation.base value) :
    Implements entries role value dictionary := by
  have classified := (run_exact entries role annotation expression _).mp returned
  have valid := (CommonRoleScalarExpressionInputs.infer_exact ..).mpr classified.1
  have actual : CommonRoleScalarRegistry.run entries role 0 (initial annotation) =
      some (.ready (.resolved dictionary)) := by
    simpa only [run, valid, ↓reduceIte] using returned
  exact CommonRoleScalarRegistry.run_all_models entries role 0 (initial annotation) dictionary actual
    (fun _ => Comp.pure Common.model value) (initial_models annotation expression classified.1 value meaning)

/-- Exact source success and all-model dictionary evidence in one statement. -/
theorem successful_dictionary_exact (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) (dictionary : Plan) :
    (run entries role annotation expression = some (.ready (.resolved dictionary)) ∧
      ∀ value, Meaning expression annotation.base value → Implements entries role value dictionary) ↔
      Classify entries role annotation expression (.resolved dictionary) := by
  constructor
  · intro returned
    exact (run_exact entries role annotation expression _).mp returned.1
  · intro classified
    have returned := (run_exact entries role annotation expression _).mpr classified
    exact ⟨returned, run_all_models entries role annotation expression dictionary returned⟩

/-- Original source syntax and generated ordinary constraints remain fixed
when only the visible enumeration changes; dictionary identity is preserved. -/
theorem run_visible_set (first last : List Entry)
    (same : ∀ entry, entry ∈ first ↔ entry ∈ last)
    (role : Nat) (annotation : Scalar) (expression : Inference.Expr) :
    run first role annotation expression = run last role annotation expression := by
  unfold run
  split
  · exact CommonRoleScalarRegistry.run_visible_set first last same role 0 (initial annotation)
  · rfl

/-- Once the annotation check passes, the generated receiver is known, so
no intermediate pending result can be confused with candidate exhaustion. -/
theorem never_pending (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) : run entries role annotation expression ≠ some .pending := by
  unfold run
  split
  · simp only [initial, CommonRoleScalarRegistry.run_recorded, ne_eq, Option.some.injEq]
    intro impossible
    cases impossible
  · simp

end Yulang.CommonRoleScalarExpressionRegistry
