import Yulang.GeneralDeclarativeI65I74CompiledOpeningScope460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open GeneralNominalCenteredHeadMatExpressions (Expr)
open AuthoredInspectQuery456 (AuthoredQuery)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeGraphRows321 (structural)
open GeneralDeclarativeWitnessConstructorModes357 (Use readUse)
open RoutedNominalPoint456 (cov)

/-- A syntactic tail receipt; only the record spine is inspected.
Unclassified malformed or uncompiled tails are distinct from open binders. -/
inductive TailBoundary where
  | closed
  | openBinder (name : Nat)
  | unsupported
  deriving DecidableEq

def classifyTail (keys : KeyRead) : Term → TailBoundary
  | .record _ _ t => classifyTail keys t
  | .var n => .openBinder n
  | .app k .nil => if keys k = .emptyRow then .closed else .unsupported
  | _ => .unsupported

inductive ReachesOpenTail : Term → Nat → Prop
  | binder : ReachesOpenTail (.var n) n
  | rest : ReachesOpenTail t n → ReachesOpenTail (.record f field t) n

theorem open_tail_mark_is_exact (keys : KeyRead) (t : Term) (n : Nat) :
    classifyTail keys t = .openBinder n ↔ ReachesOpenTail t n := by
  constructor
  · intro seen
    cases t with
    | var name =>
      simp [classifyTail] at seen
      subst name
      exact .binder
    | record _ _ t => exact .rest ((open_tail_mark_is_exact keys t n).mp seen)
    | variant | join => simp [classifyTail] at seen
    | app _ args =>
      cases args with
      | nil => simp [classifyTail] at seen; split at seen <;> contradiction
      | cons => simp [classifyTail] at seen
  · intro has
    induction has with
    | binder => rfl
    | rest _ ih => exact ih

theorem open_written_tail_has_no_g04_field_step {keys f payload tail n t lab}
    (actual : ReachesOpenTail tail n) :
    ¬ Step keys (.record f payload tail) (.field lab) t := by
  have notClosed : ¬ ClosedSpine keys tail := by
    intro closed
    induction actual with
    | binder => cases closed
    | rest _ ih => cases closed with | next ct => exact ih ct
  intro step
  cases step with
  | field closed _ => exact notClosed closed

mutual
  def actualArgumentCount : Args → Nat
    | .nil => 0
    | .cons _ more => 1 + actualArgumentCount more
end

theorem actual_argument_count_is_original_arity (args : Args) :
    actualArgumentCount args = (writeArgs args).length := by
  cases args with
  | nil => rfl
  | cons p q =>
    simp only [actualArgumentCount,writeArgs,List.length_cons,actual_argument_count_is_original_arity q]
    omega

/-- The possible general nominal forms remain in the syntax. These marks
do not classify any raw endpoint as point, do not inspect arguments, and
do not invent a mode where the current compiler has no actual Use. -/
inductive AppBoundary where
  | primitive
  | covariantUnaryOperator
  | delegatedG20G21
  | unresolved
  deriving DecidableEq

def modeScope {s : CoreState} {k arity : Nat}
    (u : Use s.current.environment k arity) : AppBoundary :=
  match u.mode with
  | .primitive _ => .primitive
  | .invariant => .delegatedG20G21
  | .declared ps =>
    if arity = 1 ∧ ps = [cov] then .covariantUnaryOperator else .delegatedG20G21

def markAtArity (s : CoreState) (key arity : Nat) : AppBoundary :=
  match readUse s.current.environment key arity with
  | some u => modeScope u
  | none => .unresolved

def markApplication (s : CoreState) (key : Nat) (args : Args) : AppBoundary :=
  markAtArity s key (actualArgumentCount args)

theorem app_mark_reads_only_original_arity {s key a b}
    (same : actualArgumentCount a = actualArgumentCount b) :
    markApplication s key a = markApplication s key b := by
  exact congrArg (markAtArity s key) same

theorem declared_mode_delegation_uses_actual_authored_layout {s key args}
    (u : Use s.current.environment key (actualArgumentCount args))
    (chosen : readUse s.current.environment key (actualArgumentCount args) = some u)
    {params} (m : u.mode = .declared params)
    (outside : ¬ (actualArgumentCount args = 1 ∧ params = [cov])) :
    markApplication s key args = .delegatedG20G21 := by
  simp [markApplication,markAtArity,chosen,modeScope,m,outside]

theorem residual_join_cannot_be_a_current_raw_visit_root {s root site left right e}
    (alreadyNormalized : AuthoredQuery s (writeTerm (.join left right)) e) :
    ¬ Visit (structural s.current.ordinary) root e site := by
  change AuthoredQuery s (.join (writeTerm left) (writeTerm right)) e at alreadyNormalized
  cases alreadyNormalized
  intro visit
  cases visit with
  | here inspect => cases inspect

theorem bound_variable_cannot_be_a_current_raw_visit_root {s root site name e}
    (alreadyNormalized : AuthoredQuery s (writeTerm (.var name)) e) :
    ¬ Visit (structural s.current.ordinary) root e site := by
  change AuthoredQuery s (.var name) e at alreadyNormalized
  cases alreadyNormalized
  exact GeneralDeclarativeInspect321.variable_has_no_visit

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
