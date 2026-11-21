import Yulang.GeneralDeclarativeTraceNames321
import Yulang.GeneralDeclarativeCompileLists321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTraceHead321
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeTrace321 (Trace Occurrence Links links_append trace_model)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativePoint320 (FrozenReads semantic_point)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralNominalCenteredHeadMatExpressions (Expr value translate)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_trans)

/-- The source constructor walk is separate from the common capture. The
actual center may already be exposed, or be forced by exact observations
of both endpoints. The latter is especially useful for invariant nominal. -/
inductive Read (s : State) (capture : Nat → Capture) (argument : Capture)
    (expression : Expr) : List Occurrence → Prop where
  | actual : Trace s .actual argument.center expression seen →
    Read s capture argument expression seen
  | point : Bounds s argument → FrozenReads s capture expression →
    Trace s .lower argument.lower expression lower →
    Trace s .upper argument.upper expression upper →
    Read s capture argument expression (lower ++ upper)

theorem read_model {s : State} (read : Read s capture arg code seen)
    (links : Links s capture seen) (m : Assignment) (valid : Models s m) :
    Equivalent (m arg.center).1 (value (variables capture m) .actual code) := by
  cases read with
  | actual matched => exact trace_model m valid capture matched links
  | point bounds freeze lo hi =>
    have limits := bounds_sound bounds m valid
    have exacts := semantic_point freeze m valid
    have low := eqv_trans (trace_model m valid capture lo (links_append links).1) exacts.1
    have high := eqv_trans (trace_model m valid capture hi (links_append links).2) exacts.2
    exact ⟨subtype_trans limits.2 high.1,subtype_trans low.2 limits.1⟩

theorem head_result (p : Supported s completed)
    (translation : translate c interp pattern = some code)
    (read : Read (restriction p) capture arg code seen)
    (links : Links (restriction p) capture seen) : Result s (headFact c interp capture arg pattern) := by
  refine ⟨[⟨arg.center,logical capture .actual code⟩],by simp [headFact,translation],?_⟩
  intro row present m valid
  cases List.mem_singleton.mp present
  simp only [Holds,logical_value]
  exact read_model read links m (restrict_models p m valid)

end Yulang.GeneralDeclarativeTraceHead321
