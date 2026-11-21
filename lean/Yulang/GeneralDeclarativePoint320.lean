import Yulang.GeneralDeclarativeLocal320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralDeclarativePoint320
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralDeclarativeHead320 (State Models Read read_sound)
open GeneralDeclarativeDemand320 (Bounds HeadMeaning bounds_sound sourceValue)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalExpressionIntervals237 (reads value_mono)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDeclarationPatterns (Constructors Pattern)
open GeneralNominalInspection (Interpretation)

def FrozenReads (s : State) (capture : Nat → Capture) (e : Expr) : Prop :=
  ∀ binder ∈ reads e,
    Bounds s (capture binder) ∧ Bound s.normal (capture binder).center (capture binder).lower ∧
      Bound s.normal (capture binder).upper (capture binder).center

/-- Only genuinely mode-sensitive reads need these reverse inequalities.
Variables inside invariant nominal applications have no such requirement. -/
theorem semantic_point {s capture e} (freeze : FrozenReads s capture e)
    (m : Assignment) (valid : Models s m) :
    Equivalent (value (variables capture m) .lower e) (value (variables capture m) .actual e) ∧
    Equivalent (value (variables capture m) .upper e) (value (variables capture m) .actual e) := by
  constructor <;> constructor <;> apply value_mono
  · intro n uses
    exact bound_sound m valid.1 (freeze n uses).1.1
  · intro n uses
    exact bound_sound m valid.1 (freeze n uses).2.1
  · intro n uses
    exact bound_sound m valid.1 (freeze n uses).2.2
  · intro n uses
    exact bound_sound m valid.1 (freeze n uses).1.2

/-- Neither an equation at the actual center nor equality of the three
logical names is needed: ordinary interval containment and the checked
endpoint observations force this exact actual result. -/
theorem actual_of_endpoints {s capture argument e}
    (bounds : Bounds s argument)
    (lower : Read s capture .lower argument.lower e)
    (upper : Read s capture .upper argument.upper e)
    (freeze : FrozenReads s capture e)
    (m : Assignment) (valid : Models s m) :
    Equivalent (m argument.center).1 (value (variables capture m) .actual e) := by
  have span := bounds_sound bounds m valid
  have same := semantic_point freeze m valid
  have lo := eqv_trans (read_sound lower m valid) same.1
  have hi := eqv_trans (read_sound upper m valid) same.2
  exact ⟨subtype_trans span.2 hi.1,subtype_trans lo.2 span.1⟩

theorem normalized_head_of_endpoints {s capture argument e} {c : Constructors} {interp : Interpretation}
    {pattern : Pattern} (compiled : translate c interp pattern = some e)
    (bounds : Bounds s argument)
    (lower : Read s capture .lower argument.lower e)
    (upper : Read s capture .upper argument.upper e)
    (freeze : FrozenReads s capture e)
    (m : Assignment) (valid : Models s m) :
    HeadMeaning c interp capture m argument pattern :=
  ⟨eqv_trans (actual_of_endpoints bounds lower upper freeze m valid) (compiled_normalized compiled),
    bounds_sound bounds m valid⟩

theorem frozen_nominal (s : State) (capture : Nat → Capture) (name : Nat) (args : List Expr) :
    FrozenReads s capture (.nominal name args) := by
  intro n impossible
  cases impossible

theorem invariant_nominal_actual {s capture argument name args}
    (bounds : Bounds s argument)
    (lower : Read s capture .lower argument.lower (.nominal name args))
    (upper : Read s capture .upper argument.upper (.nominal name args))
    (m : Assignment) (valid : Models s m) :
    Equivalent (m argument.center).1 (value (variables capture m) .actual (.nominal name args)) :=
  actual_of_endpoints bounds lower upper (frozen_nominal s capture name args) m valid

end Yulang.GeneralDeclarativePoint320
