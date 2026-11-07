import Yulang.CheckedRoles
import Yulang.CommonCanonicalShapes

/-!
# Limits of reusing finite-tree role descent for regular goals

The declaration below passes the actual `CheckedRoles.checkImpl` and
`Roles.Impl.WellFormed` checks. Its pair/variant interpretation will be used
to exhibit an infinite chain of distinct finite regular descriptions.

This does not modify the role resolver, prove that B4 is false, or claim
undecidability. It isolates why the existing finite-tree size proof and a
cache of already visited exact goals cannot by themselves establish the
required regular-goal termination theorem. Source reachability is not asserted.
-/

namespace Yulang.CommonRoleRegularObstructions

open Roles (Term Impl Goal)

/-- Constructor 0 is a pair; constructor 1 is one fixed variant tag. -/
def headPattern : Term :=
  .app 0 [.app 1 [.app 1 [.var 0]], .var 1]

def childPattern : Term :=
  .app 0 [.var 0, .app 1 [.var 1]]

def declaration : Impl :=
  ⟨0, [headPattern], [⟨0, [childPattern]⟩], 0⟩

theorem declaration_sizes :
    Roles.argsSize declaration.head = 5 ∧
      Roles.argsSize [childPattern] = 4 := by
  decide +kernel

theorem declaration_accepted : CheckedRoles.checkImpl declaration = true := by
  decide +kernel

theorem declaration_wellFormed : declaration.WellFormed :=
  (CheckedRoles.checkImpl_exact declaration).mp declaration_accepted

open Common (Ty Equivalent)

def wrap (value : Ty) : Ty := Common.variant 7 value

/-- Only the two constructors in the example are interpreted. Other trees
are rejected, so this is not an arbitrary decoder for all Common types. -/
def interpretPattern (assignment : Nat → Ty) : Term → Option Ty
  | .var name => some (assignment name)
  | .app 0 [first, last] => do
      return Common.pair (← interpretPattern assignment first) (← interpretPattern assignment last)
  | .app 1 [value] => do
      return wrap (← interpretPattern assignment value)
  | .app _ _ => none

/-- The independent one-step instance relation for the one declaration,
using Common demand equivalence for its finite regular arguments. -/
def InstanceStep (source target : Ty) : Prop :=
  ∃ assignment first last,
    interpretPattern assignment headPattern = some first ∧
    interpretPattern assignment childPattern = some last ∧
    Equivalent first source ∧ Equivalent last target

/-- One finite state, with one back edge. -/
def loopState : CommonSyntax.State Common.Row :=
  .block [.variant 7 (.inl 0)] 0

def loop : Ty := CommonSyntax.graph Common.Row loopState

theorem observe_loop_wrap (depth : Nat) :
    Common.observeTy depth loop = Common.observeTy depth (wrap loop) := by
  cases depth <;> rfl

theorem loop_unfold : Equivalent loop (wrap loop) := by
  constructor <;> intro depth
  · rw [observe_loop_wrap]
    exact CommonFinite.producerLe_refl _
  · rw [observe_loop_wrap depth]
    exact CommonFinite.producerLe_refl _

def growing : Nat → Ty
  | 0 => .base .int
  | count + 1 => wrap (growing count)

def chain (count : Nat) : Ty := Common.pair loop (growing count)

/-- The accepted declaration has another instantiated child at every
natural-number stage, even though each stage is finite regular syntax. -/
theorem chain_step (count : Nat) : InstanceStep (chain count) (chain (count + 1)) := by
  refine ⟨(fun name => if name = 0 then loop else growing count),
    Common.pair (wrap (wrap loop)) (growing count), chain (count + 1), rfl, rfl, ?_,
    Common.equivalent_refl _⟩
  apply (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr
  refine ⟨?_, Common.equivalent_refl _⟩
  exact Common.equivalent_symm (Common.equivalent_trans loop_unfold
    ((CommonCanonicalShapes.variant_equivalent_iff 7 _ _).mpr loop_unfold))

end Yulang.CommonRoleRegularObstructions
