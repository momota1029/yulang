import Yulang.GeneralDeclarativeRepeatedActual323
import Yulang.GeneralDeclarativeTraceExpand323
import Yulang.GeneralDeclarativeRigidObserve323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRigidCode323
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeEqualities322 (entails)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeTermWalk322 (Walk WalkMany)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeTraceExpand323 (convert expands)
open GeneralDeclarativeRepeatedActual323 (Rigid RigidMany)
open GeneralDeclarativeRigidSource323 (Scanned)
open GeneralDeclarativeRigidObserve323 (from_expression)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadWFSource (PatternCovered)
open GeneralDeclarationPatterns (normalize)

mutual
inductive Code : Expr → Prop where
  | variable : Code (.variable binder)
  | scalar : Code (.primitive (.scalar base) [])
  | pair : Code a → Code b → Code (.primitive .pair [a,b])
  | nominal : Codes args → Code (.nominal tag args)
inductive Codes : List Expr → Prop where
  | nil : Codes []
  | cons : Code one → Codes rest → Codes (one::rest)
end

theorem rigid_of_walk (walk : Walk mode term code seen) (hasCode : Code code) :
    Rigid mode term code seen :=
  Walk.rec
    (motive_1 := fun mode term code seen _ => Code code → Rigid mode term code seen)
    (motive_2 := fun mode terms codes seen _ => Codes codes → RigidMany mode terms codes seen)
    (by intro _ _ _ _; exact .capture)
    (by
      intro mode as bs seen tag walked ih kind
      cases kind with
      | scalar =>
        cases ih .nil with
        | nil => exact .scalar
      | pair x y =>
        cases ih (.cons x (.cons y .nil)) with
        | cons first tail =>
          cases tail with
          | cons next last =>
            cases last
            simpa using Rigid.pair first next)
    (by
      intro as bs seen mode tag walked ih kind
      cases kind with
      | nominal kinds => exact .nominal (ih kinds))
    (by intros; rename_i impossible; cases impossible)
    (by intros; rename_i impossible; cases impossible)
    (by intros; rename_i impossible; cases impossible)
    (by intro _ _; exact .nil)
    (by
      intro mode a b first as bs rest f g ih jh kind
      cases kind with
      | cons h t => exact .cons (ih h) (jh t))
    walk hasCode

/-- An actual normalized trace from the authorized ordinary subset
produces the exact source observation and logical occurrences for the
rigid fragment. The upper names and constraints are not substituted for
that actual trace. -/
theorem actual_trace {s : State} {support : Supported s completed}
    (bounds : Bounds s arg) (metadata : PatternCovered c interp p)
    (compiled : translate c interp (normalize p) = some code)
    (kind : Code code) (real : Trace (restriction support) .actual arg.center code raw) :
    Scanned s c interp arg p (raw.map convert) := by
  obtain ⟨term,observed,walk⟩ := expands real
  exact from_expression bounds metadata compiled (rigid_of_walk walk kind)
    (fun m valid => entails observed m (restrict_models support m valid))

end Yulang.GeneralDeclarativeRigidCode323
