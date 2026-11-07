import Yulang.CommonCaseComputations
import Yulang.CommonPatternComputationSafety
import Yulang.CommonCaseBoundedObservations

/-! First-match cases compose in a computation logic, allowing unfinished
defaults/guards/bodies. The shared cap is a conservative bound, not a choice
of principal source effect row. Coverage and source match-failure translation
are separate obligations. -/

namespace Yulang.CommonCaseComputationSafety

open CommonPatternComputations (Ops)
open CommonPatternComputationSafety (Logic OptionHolds DefaultSound typing_safe)
open CommonCaseComputations (Visits testArm runArms eval)
open CommonCaseBoundedObservations (ArmTyping)
open CommonPatternEnvironment (NamedTypes)
open CommonPatternTyping (valueAt bindingTypes)
open CaseValues (Bindings BindingsHold)
open CaseEvaluation (Arm)
open Core.CommonData (Value)

def VisitsSafe {M : Type → Type} {ops : Ops M} (logic : Logic ops) (visits : Visits M) : Prop :=
  ∀ {A} (visit : CommonCaseComputations.Visit) (computation : M A) (post : A → Prop) (cap : Common.Row),
    logic.Safe computation post cap → logic.Safe (visits.prepend visit computation) post cap

def GuardSound {M : Type → Type} {ops : Ops M} (logic : Logic ops) (cap : Common.Row)
    (GuardTyped : G → NamedTypes → Prop) (evaluate : G → Bindings Empty → M Bool) : Prop :=
  ∀ code types, GuardTyped code types → ∀ actual, BindingsHold (bindingTypes types) actual →
    logic.Safe (evaluate code actual) (fun _ => True) cap

def BodySound {M : Type → Type} {ops : Ops M} (logic : Logic ops) (cap : Common.Row)
    (BodyTyped : B → NamedTypes → Common.Ty → Prop) (evaluate : B → Bindings Empty → M Value) : Prop :=
  ∀ code types target, BodyTyped code types target → ∀ actual, BindingsHold (bindingTypes types) actual →
    logic.Safe (evaluate code actual) (valueAt target) cap

def ResultHolds (target : Common.Ty) : Option Value → Prop
  | none => True
  | some value => valueAt target value

theorem testArm_safe {M : Type → Type} {ops : Ops M} (logic : Logic ops) (visits : Visits M)
    (visitSafe : VisitsSafe logic visits) (cap : Common.Row) (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → M Value) (defaults : DefaultSound logic cap DefaultTyped defaultEval)
    (environment : Bindings Empty) (env : BindingsHold (bindingTypes types) environment)
    (guardEval : G → Bindings Empty → M Bool) (guards : GuardSound logic cap GuardTyped guardEval)
    (index : Nat) (arm : Arm Empty D G B)
    (typed : CommonAlignedPatternTyping.Typing DefaultTyped types arm.pattern input bindings)
    (guardTyped : ∀ code, arm.guard = some code → GuardTyped code bindings)
    (value : Value) (within : valueAt input value) :
    logic.Safe (testArm ops visits floatCheck defaultEval environment guardEval index arm value) (OptionHolds bindings) cap := by
  apply logic.bind_safe (typing_safe logic cap floatCheck defaultEval defaults typed.2 typed.1 environment env value within)
  intro option returnedTyped
  cases option with
  | none => exact logic.ret_safe _ _ _ True.intro
  | some actual =>
      cases selected : arm.guard with
      | none => exact logic.ret_safe _ _ _ returnedTyped
      | some code =>
          apply visitSafe
          apply logic.bind_safe (guards code bindings (guardTyped code selected) actual returnedTyped)
          intro accepted any
          cases accepted with
          | false => exact logic.ret_safe _ _ _ True.intro
          | true => exact logic.ret_safe _ _ _ returnedTyped

/-- Arbitrary finite ordered arms and arbitrary starting index. Later arms
are sequenced only after a completed miss/false guard; no chosen match or
successful callback is a premise. -/
theorem runArms_safe {M : Type → Type} {ops : Ops M} (logic : Logic ops) (visits : Visits M)
    (visitSafe : VisitsSafe logic visits) (cap : Common.Row) (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → M Value) (defaults : DefaultSound logic cap DefaultTyped defaultEval)
    (environment : Bindings Empty) (env : BindingsHold (bindingTypes types) environment)
    (guardEval : G → Bindings Empty → M Bool) (guards : GuardSound logic cap GuardTyped guardEval)
    (bodyEval : B → Bindings Empty → M Value) (bodies : BodySound logic cap BodyTyped bodyEval)
    (value : Value) (within : valueAt input value) (index : Nat) (arms : List (Arm Empty D G B))
    (typed : ∀ arm ∈ arms, ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target) :
    logic.Safe (runArms ops visits floatCheck defaultEval environment guardEval bodyEval value index arms) (ResultHolds target) cap := by
  induction arms generalizing index with
  | nil => exact logic.ret_safe _ _ _ True.intro
  | cons arm rest ih =>
      obtain ⟨patternTyped, guardTyped, bodyTyped⟩ := typed arm List.mem_cons_self
      apply visitSafe
      apply logic.bind_safe (testArm_safe logic visits visitSafe cap floatCheck defaultEval defaults environment env
        guardEval guards index arm patternTyped guardTyped value within)
      intro option selectedTyped
      cases option with
      | none => exact ih (index + 1) (fun arm member => typed arm (List.mem_cons_of_mem _ member))
      | some actual =>
          apply visitSafe
          apply logic.bind_safe (bodies arm.body _ target bodyTyped actual selectedTyped)
          intro result resultTyped
          exact logic.ret_safe _ _ _ resultTyped

theorem eval_safe {M : Type → Type} {ops : Ops M} (logic : Logic ops) (visits : Visits M)
    (visitSafe : VisitsSafe logic visits) (cap : Common.Row) (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → M Value) (defaults : DefaultSound logic cap DefaultTyped defaultEval)
    (environment : Bindings Empty) (env : BindingsHold (bindingTypes types) environment)
    (guardEval : G → Bindings Empty → M Bool) (guards : GuardSound logic cap GuardTyped guardEval)
    (bodyEval : B → Bindings Empty → M Value) (bodies : BodySound logic cap BodyTyped bodyEval)
    (scrutinee : M Value) (scrutineeSafe : logic.Safe scrutinee (valueAt input) cap)
    (arms : List (Arm Empty D G B))
    (typed : ∀ arm ∈ arms, ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target) :
    logic.Safe (eval ops visits floatCheck defaultEval environment guardEval bodyEval scrutinee arms) (ResultHolds target) cap := by
  apply visitSafe
  apply logic.bind_safe scrutineeSafe
  intro value within
  exact runArms_safe logic visits visitSafe cap floatCheck defaultEval defaults environment env guardEval guards
    bodyEval bodies value within 0 arms typed

end Yulang.CommonCaseComputationSafety
