import Yulang.CommonCaseComputationSafety
import Yulang.CommonPatternFinitePrefixes

/-! All represented finite case prefixes, including unfinished callbacks.
Administrative visits are pure. Their pending empty prefixes are retained.
No source-prefix coverage or source evaluator is manufactured by this model. -/

namespace Yulang.CommonCaseFinitePrefixes

open CommonPatternFinitePrefixes (Computation Observation Safe ops logic)
open CommonCaseComputations (Visit Visits)
open CommonCaseComputationSafety
open CommonCaseEffectPaths (traceRow eventRow)

inductive Prepend (visit : Visit) (computation : Computation E R A) : Computation E R A where
  | pending : Prepend visit computation ⟨[], none⟩
  | next (observed : Observation E R A) : computation observed →
      Prepend visit computation ⟨visit.event :: observed.trace, observed.result⟩

def visits (E R : Type) : Visits (Computation E R) := ⟨Prepend⟩

theorem visit_empty (source : E → Common.Row) (visit : Visit) :
    eventRow source visit.event = Common.rowEmpty := by
  cases visit <;> rfl

theorem prepend_safe (source : E → Common.Row) (failure : R → Common.Row)
    (visit : Visit) (computation : Computation E R A) (post : A → Prop) (cap : Common.Row)
    (safe : Safe source failure computation post cap) : Safe source failure (Prepend visit computation) post cap := by
  intro observed present
  cases present with
  | pending =>
      constructor
      · intro occurrence impossible
        rcases impossible with left | right <;> exact False.elim ‹False›
      · intro value impossible
        cases impossible
  | next observed present =>
      have sourceSafe := safe observed present
      refine ⟨?_, sourceSafe.2⟩
      intro occurrence within
      have later : CommonPatternFinitePrefixes.observationRow source failure observed occurrence := by
        simpa only [CommonPatternFinitePrefixes.observationRow, traceRow, visit_empty,
          Common.rowJoin, Common.rowEmpty, false_or] using within
      exact sourceSafe.1 occurrence later

theorem visits_safe (source : E → Common.Row) (failure : R → Common.Row) :
    VisitsSafe (logic source failure) (visits E R) :=
  fun visit computation post cap safe => prepend_safe source failure visit computation post cap safe

theorem row_mono (source : E → Common.Row) (failure : R → Common.Row) (computation : Computation E R A)
    (post : A → Prop) (lower upper : Common.Row) (safe : Safe source failure computation post lower)
    (below : Common.rowLe lower upper) : Safe source failure computation post upper := by
  intro observed present
  have valid := safe observed present
  exact ⟨Common.rowLe_trans valid.1 below, valid.2⟩

/-- Every admitted subject/arm computation, without successful or terminating
leaf premises. Errors and unfinished prefixes obey the same row bound;
only completed successful outputs carry the result-value obligation. -/
theorem eval_finite_prefixes (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → D → Computation E R Core.CommonData.Value)
    (defaults : CommonPatternComputationSafety.DefaultSound (logic source failure) cap DefaultTyped defaultEval)
    (environment : CaseValues.Bindings Empty)
    (env : CaseValues.BindingsHold (CommonPatternTyping.bindingTypes types) environment)
    (guardEval : G → CaseValues.Bindings Empty → Computation E R Bool)
    (guards : GuardSound (logic source failure) cap GuardTyped guardEval)
    (bodyEval : B → CaseValues.Bindings Empty → Computation E R Core.CommonData.Value)
    (bodies : BodySound (logic source failure) cap BodyTyped bodyEval)
    (scrutinee : Computation E R Core.CommonData.Value)
    (subjectSafe : Safe source failure scrutinee (CommonPatternTyping.valueAt input) cap)
    (arms : List (CaseEvaluation.Arm Empty D G B))
    (typed : ∀ arm ∈ arms, CommonCaseBoundedObservations.ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target) :
    Safe source failure
      (CommonCaseComputations.eval (ops E R) (visits E R) floatCheck defaultEval environment guardEval bodyEval scrutinee arms)
      (ResultHolds target) cap :=
  eval_safe (logic source failure) (visits E R) (visits_safe source failure) cap floatCheck defaultEval defaults
    environment env guardEval guards bodyEval bodies scrutinee subjectSafe arms typed

end Yulang.CommonCaseFinitePrefixes
