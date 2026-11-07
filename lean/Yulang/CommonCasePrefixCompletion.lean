import Yulang.CommonCasePrefixCoverage

/-! Constructive successful completion for the existing finite-prefix
computations. The existential interpretation of the existing computation
logic builds an actual completed trace through every sequential boundary.
It reuses the unchanged structural matcher and ordered first-match case.
Coverage is separate: finite traversal may complete with an ordinary miss. -/

namespace Yulang.CommonCasePrefixCompletion

set_option backward.isDefEq.respectTransparency false

open CommonPatternFinitePrefixes (Computation ops ret Bind)
open CommonPatternPrefixNoMiss (Returns returns_ret returns_bind)
open CommonPatternComputationSafety (Logic DefaultSound)
open CommonCaseComputationSafety (VisitsSafe GuardSound BodySound ResultHolds)
open CommonPatternTyping (valueAt bindingTypes)
open CommonCaseFinitePrefixes (visits Prepend)
open CaseValues (Bindings BindingsHold)
open CaseEvaluation (Arm)
open Core.CommonData (Value)

def Completes (computation : Computation E R A) (post : A → Prop) : Prop :=
  ∃ value, Returns computation value ∧ post value

theorem ret_completes (value : A) (post : A → Prop) (valid : post value) :
    Completes (ret (E := E) (R := R) value) post :=
  ⟨value, (returns_ret value value).mpr rfl, valid⟩

theorem bind_completes (first : Computation E R A) (next : A → Computation E R B)
    (pre : A → Prop) (post : B → Prop) (head : Completes first pre)
    (tail : ∀ value, pre value → Completes (next value) post) : Completes (Bind first next) post := by
  obtain ⟨value, returned, valid⟩ := head
  obtain ⟨result, later, good⟩ := tail value valid
  exact ⟨result, (returns_bind first next result).mpr ⟨value, returned, later⟩, good⟩

/-- This interpretation concerns existence of a successful completed trace.
The row argument is ignored; universal row safety remains a separate theorem. -/
def logic (E R : Type) : Logic (ops E R) where
  Safe := fun computation post _ => Completes computation post
  ret_safe := fun value post _ valid => ret_completes value post valid
  bind_safe := fun {A B} {first next pre post cap} => bind_completes first next pre post
  weaken := by
    intro A computation pre post cap completed implication
    obtain ⟨value, returned, valid⟩ := completed
    exact ⟨value, returned, implication value valid⟩

theorem visits_complete (E R : Type) : VisitsSafe (logic E R) (visits E R) := by
  intro A visit computation post cap completed
  obtain ⟨value, returned, valid⟩ := completed
  exact ⟨value, (CommonCasePrefixCoverage.returns_prepend visit computation value).mpr returned, valid⟩

/-- Every finite original arm list, with actual typed incoming bindings and
subject. Successful leaf computations are sequenced constructively, including
failed patterns and false guards before a later arm. No chosen arm is given.
The source-specific theorem must derive these leaf contracts from syntax. -/
theorem eval_completes (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Computation E R Value)
    (defaults : DefaultSound (logic E R) Common.rowEmpty DefaultTyped defaultEval)
    (environment : Bindings Empty) (env : BindingsHold (bindingTypes types) environment)
    (guardEval : G → Bindings Empty → Computation E R Bool)
    (guards : GuardSound (logic E R) Common.rowEmpty GuardTyped guardEval)
    (bodyEval : B → Bindings Empty → Computation E R Value)
    (bodies : BodySound (logic E R) Common.rowEmpty BodyTyped bodyEval)
    (scrutinee : Computation E R Value) (subject : Completes scrutinee (valueAt input))
    (arms : List (Arm Empty D G B))
    (typed : ∀ arm ∈ arms,
      CommonCaseBoundedObservations.ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target) :
    Completes (CommonCaseComputations.eval (ops E R) (visits E R) floatCheck defaultEval environment
      guardEval bodyEval scrutinee arms) (ResultHolds target) :=
  CommonCaseComputationSafety.eval_safe (logic E R) (visits E R) (visits_complete E R) Common.rowEmpty
    floatCheck defaultEval defaults environment env guardEval guards bodyEval bodies scrutinee subject arms typed

end Yulang.CommonCasePrefixCompletion
