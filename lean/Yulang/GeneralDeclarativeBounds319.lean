import Yulang.GeneralDeclarativeWhere319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 3500000
namespace Yulang.GeneralDeclarativeBounds319
open CommonNominalFullCarrier (Subtype Equivalent subtype_trans subtype_refl)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWhere319 (State Models Capture SourceWhere variables)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany value)
open GeneralNominalExpressionIntervals237 (reads interval)
open GeneralNominalCenteredHeadMatPatternSemantics (eval)
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra compiled_normalized)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open CommonRoleOutermostResolver (All₂)

/-- A deliberately small declarative proof of a variable-to-variable type
bound. It reads logical constraints and intervals only, not solver state;
soundness below does not assert completeness of this deduction system. -/
inductive Bound (s : State) : Nat → Nat → Prop where
  | interval : (a,b) ∈ s.intervals → Bound s a b
  | constraint : PresenceNormalForm.Atom.tyLe (.var a) (.var b) ∈ s.ordinary → Bound s a b
  | refl (a : Nat) : Bound s a a
  | trans : Bound s a b → Bound s b c → Bound s a c

theorem bound_sound {s : State} (m : Assignment) (valid : Models s m)
    {a b : Nat} (bound : Bound s a b) : Subtype (m a).1 (m b).1 := by
  induction bound with
  | interval present => exact valid.2 _ present
  | constraint present => exact valid.1 _ present
  | refl i => exact subtype_refl _
  | trans _ _ first last => exact subtype_trans first last

def Tracks (s : State) (capture : Nat → Capture) (exp : Expr) : Prop :=
  ∀ name ∈ reads exp,
    Bound s (capture name).lower (capture name).center ∧
    Bound s (capture name).center (capture name).upper

theorem tracked_literal {s : State} {capture exp}
    (facts : GeneralDeclarativeWhere319.Tracks s capture exp) : Tracks s capture exp := by
  intro name uses
  exact ⟨.interval (facts name uses).1,.interval (facts name uses).2⟩

theorem source_where {s : State} {catalogue : Constructors} {interp}
    {capture : Nat → Capture} {pattern : Pattern} {exp : Expr}
    (compiled : translate catalogue interp pattern = some exp)
    (tracked : Tracks s capture exp) (m : Assignment) (valid : Models s m) :
    SourceWhere catalogue interp capture m pattern exp := by
  have sem := interval (variables capture m) exp (fun n read =>
    ⟨bound_sound m valid (tracked n read).1,bound_sound m valid (tracked n read).2⟩)
  have actual : Equivalent (value (variables capture m) .actual exp)
      (eval (algebra catalogue interp) (variables capture m .actual) (normalize pattern)) :=
    compiled_normalized compiled
  exact ⟨subtype_trans sem.1 actual.1,subtype_trans actual.2 sem.2⟩

end Yulang.GeneralDeclarativeBounds319
