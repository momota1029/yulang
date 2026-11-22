import Yulang.GeneralDeclarativeMixedSources339
import Yulang.GeneralDeclarativeAliasProbe327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeMixedLeafGrowth339
open GeneralDeclarativeMixedLeaf339 (Reader ReadyLeaf read_nominal read_primitive)
open GeneralDeclarativeMixedSources339 (Source)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeArityPlan330 (Shape Shapes)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeCompoundSources338 (Anchored)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)

/-- An actual trace is sufficient for later authorized rereads of its
operand list; no hypothesis about every future state is needed. -/
theorem grow_args {s t : State} (grew : Extends s t)
    (known : TraceArgs s mode names codes uses) : TraceArgs t mode names codes uses := by
  induction names generalizing codes uses with
  | nil => cases known; exact .nil
  | cons _ _ rec =>
    cases known with
    | cons head tail => exact .cons (GeneralDeclarativeObserverGrowth330.trace grew head) (rec tail)

theorem named_reader {s : State} (seen : Trace s mode root code uses) : Reader s mode (.variable root) code := by
  intro t grew n anchored
  obtain ⟨owner,equal,row⟩ := anchored
  exact GeneralDeclarativeAliasProbe327.trace (.trans equal (.forward row))
    (GeneralDeclarativeObserverGrowth330.trace grew seen)

/-- Concrete independently sourced invariant nominal operands are
observed at their actual names, not at lower or upper representatives. -/
theorem invariant_leaf {s : State}
    (printed : translate c i (normalize pat) = some (.nominal tag codes))
    (shape : Shapes codes)
    (left : TraceArgs s .actual lows codes lowerUses)
    (right : TraceArgs s .actual highs codes upperUses) :
    Source c i s (.nominal tag (lows.map Expr.variable))
      (.nominal tag (highs.map Expr.variable)) (normalize pat) :=
  .leaf ⟨_,printed,.nominal shape,
    read_nominal (fun _ grows => ⟨_,grow_args grows left⟩),
    read_nominal (fun _ grows => ⟨_,grow_args grows right⟩)⟩

/-- Pair operands keep the side's mode. This locator does not assign
either endpoint to an unknown center. -/
theorem pair_leaf {s : State}
    (printed : translate c i (normalize pat) = some (pair x y))
    (shapeX : Shape x) (shapeY : Shape y)
    (low1 : Trace s .lower a x l1) (low2 : Trace s .lower b y l2)
    (high1 : Trace s .upper u x h1) (high2 : Trace s .upper v y h2) :
    Source c i s (pair (.variable a) (.variable b)) (pair (.variable u) (.variable v)) (normalize pat) := by
  have low : TraceArgs s .lower [a,b] [x,y] (l1 ++ (l2 ++ [])) := .cons low1 (.cons low2 .nil)
  have high : TraceArgs s .upper [u,v] [x,y] (h1 ++ (h2 ++ [])) := .cons high1 (.cons high2 .nil)
  exact .leaf ⟨_,printed,.pair shapeX shapeY,
    read_primitive (fun _ grows => ⟨_,grow_args grows low⟩),
    read_primitive (fun _ grows => ⟨_,grow_args grows high⟩)⟩

/-- Raw endpoint trace has a join case, while this delivery/compiler's
existing recognized structural leaf fragment does not. This is a
scope check, not a rejection or new K2 priority rule. -/
theorem join_shape_missing (lo hi : Expr) : ¬ Shape (.join lo hi) := by
  intro recognized
  cases recognized

end Yulang.GeneralDeclarativeMixedLeafGrowth339
