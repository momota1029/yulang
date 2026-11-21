import Yulang.GeneralDeclarativeHead320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralDeclarativeDemand320
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (State Models Read read_sound source_head)
open GeneralDeclarativeWhere319 (Capture variables InInterval SourceWhere)
open GeneralDeclarativeBounds319 (Bound Tracks bound_sound)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatPatternSemantics (eval)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralSourceState (Output)
open CommonRoleOutermostResolver (All₂)

structure Demand where
  role : Nat
  arguments : List Capture
  outputs : List Output

def Bounds (s : State) (arg : Capture) : Prop :=
  Bound s.normal arg.lower arg.center ∧ Bound s.normal arg.center arg.upper

theorem bounds_sound {s : State} {argument : Capture} (given : Bounds s argument)
    (m : Assignment) (valid : Models s m) :
    InInterval (m argument.lower).1 (m argument.upper).1 (m argument.center).1 :=
  ⟨bound_sound m valid.1 given.1,bound_sound m valid.1 given.2⟩

def sourceValue (catalogue : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (m : Assignment) (pattern : Pattern) : Ty :=
  eval (algebra catalogue interp) (variables capture m .actual) (normalize pattern)

def HeadArg (s : State) (catalogue : Constructors) (interp : Interpretation)
    (capture : Nat → Capture) (argument : Capture) (pattern : Pattern) : Prop :=
  Bounds s argument ∧ ∃ code, translate catalogue interp pattern = some code ∧
    Read s capture .actual argument.center code

def HeadMeaning (catalogue : Constructors) (interp : Interpretation)
    (capture : Nat → Capture) (m : Assignment) (argument : Capture) (pattern : Pattern) : Prop :=
  Equivalent (m argument.center).1 (sourceValue catalogue interp capture m pattern) ∧
  InInterval (m argument.lower).1 (m argument.upper).1 (m argument.center).1

theorem head_arg {s catalogue interp capture argument pattern}
    (given : HeadArg s catalogue interp capture argument pattern)
    (m : Assignment) (valid : Models s m) :
    HeadMeaning catalogue interp capture m argument pattern := by
  obtain ⟨bounds,code,compiled,read⟩ := given
  exact ⟨source_head compiled read m valid,bounds_sound bounds m valid⟩

theorem head_args {s catalogue interp capture args patterns}
    (given : All₂ (HeadArg s catalogue interp capture) args patterns)
    (m : Assignment) (valid : Models s m) :
    All₂ (HeadMeaning catalogue interp capture m) args patterns := by
  induction given with
  | nil => exact .nil
  | cons h _ ih => exact .cons (head_arg h m valid) ih

/-- All three names of an emitted argument come from one expression and the
same capture. Nominal subexpressions read actual parameters in all modes. -/
def WhereArg (s : State) (catalogue : Constructors) (interp : Interpretation)
    (capture : Nat → Capture) (argument : Capture) (pattern : Pattern) : Prop :=
  ∃ code, translate catalogue interp pattern = some code ∧
    Tracks s.normal capture code ∧
    Read s capture .lower argument.lower code ∧
    Read s capture .actual argument.center code ∧
    Read s capture .upper argument.upper code

def WhereMeaning (catalogue : Constructors) (interp : Interpretation)
    (capture : Nat → Capture) (m : Assignment) (argument : Capture) (pattern : Pattern) : Prop :=
  ∃ code, translate catalogue interp pattern = some code ∧
    Equivalent (m argument.lower).1 (value (variables capture m) .lower code) ∧
    Equivalent (m argument.upper).1 (value (variables capture m) .upper code) ∧
    HeadMeaning catalogue interp capture m argument pattern

theorem where_arg {s catalogue interp capture argument pattern}
    (given : WhereArg s catalogue interp capture argument pattern)
    (m : Assignment) (valid : Models s m) :
    WhereMeaning catalogue interp capture m argument pattern := by
  obtain ⟨code,compiled,tracks,lower,center,upper⟩ := given
  have lo := read_sound lower m valid
  have hi := read_sound upper m valid
  have actual := source_head compiled center m valid
  have sourced : SourceWhere catalogue interp capture m pattern code :=
    GeneralDeclarativeBounds319.source_where compiled tracks m valid.1
  exact ⟨code,compiled,lo,hi,actual,
    subtype_trans lo.1 (subtype_trans sourced.1 actual.2),
    subtype_trans actual.1 (subtype_trans sourced.2 hi.2)⟩

theorem where_args {s catalogue interp capture args patterns}
    (given : All₂ (WhereArg s catalogue interp capture) args patterns)
    (m : Assignment) (valid : Models s m) :
    All₂ (WhereMeaning catalogue interp capture m) args patterns := by
  induction given with
  | nil => exact .nil
  | cons h _ ih => exact .cons (where_arg h m valid) ih

end Yulang.GeneralDeclarativeDemand320
