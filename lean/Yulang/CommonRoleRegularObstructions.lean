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

end Yulang.CommonRoleRegularObstructions
