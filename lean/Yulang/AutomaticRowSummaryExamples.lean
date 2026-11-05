import Yulang.AutomaticRowSummaries

/-!
# Original-AST guard checks with genuinely infinite solutions

A one-dimensional row starts at weight one and repeatedly adds two. Its guard
excludes zero, which is unreachable by parity. No constant-coordinate affine
certificate can certify the nonzero cycle, but the automatic checker can.
The guarded example whose seed is zero must remain unsupported: erasing its
guard would create effects that the original least solution does not contain.
-/

namespace Yulang.AutomaticRowSummaries.Examples

open SemilinearWeights (Weight)

def scalar (value : Int) : Weight 1 := fun _ => value

def odd : RecursiveRows.Problem 1 Nat Nat :=
  [⟨7, .protect 0 Directed.allowNone (.head 0)⟩,
   ⟨7, .protect 0 Directed.allowNone
     (.protect 0 Directed.allowNone (.residual [0] (.var 7)))⟩]

def blocked : RecursiveRows.Problem 1 Nat Nat :=
  [⟨7, .head 0⟩,
   ⟨7, .protect 0 Directed.allowNone
     (.protect 0 Directed.allowNone (.residual [0] (.var 7)))⟩]

set_option maxRecDepth 100000 in
theorem parity_guard_automatically_accepted :
    check (CertifiedRowSummaries.normalizedProblem 0 odd) 0 = true := by decide

set_option maxRecDepth 100000 in
theorem odd_seed_is_member : query odd 0 7 (scalar 1) = some true := by decide

set_option maxRecDepth 100000 in
theorem later_odd_is_member : query odd 0 7 (scalar 3) = some true := by decide

set_option maxRecDepth 100000 in
theorem even_weight_is_not_member : query odd 0 7 (scalar 2) = some false := by decide

set_option maxRecDepth 100000 in
theorem negative_odd_is_not_member : query odd 0 7 (scalar (-1)) = some false := by decide

set_option maxRecDepth 100000 in
theorem reachable_guard_is_unsupported : query blocked 0 7 (scalar 2) = none := by decide

/-- A supported negative answer excludes every finite derivation, without
choosing an unfolding or path-length bound. -/
theorem even_weight_has_no_derivation :
    ¬ RecursiveRows.Derives odd 7 ⟨0, scalar 2⟩ :=
  query_false odd 0 7 (scalar 2) even_weight_is_not_member

theorem later_odd_has_derivation : RecursiveRows.Derives odd 7 ⟨0, scalar 3⟩ :=
  (query_exact odd 0 7 (scalar 3) true later_odd_is_member).mp rfl

end Yulang.AutomaticRowSummaries.Examples
