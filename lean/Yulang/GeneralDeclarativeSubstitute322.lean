import Yulang.GeneralDeclarativeEqualities322
import Yulang.GeneralDeclarativeSubstitution320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSubstitute322
open GeneralDeclarativeHead320 (State byMode)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSubstitution320 (logical logicals)
open GeneralDeclarativeEqualities322 (Derives Forest)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr)

mutual
 def visits (mode : Mode) : Expr → List (Nat × Mode)
  | .variable name => [(name,mode)]
  | .primitive _ xs => visitsMany mode xs
  | .nominal _ xs => visitsMany .actual xs
  | .record _ a b | .join a b => visits mode a ++ visits mode b
  | .variant _ p => visits mode p
 def visitsMany (mode : Mode) : List Expr → List (Nat × Mode)
  | [] => []
  | first :: rest => visits mode first ++ visitsMany mode rest
end

def Agreement (s : State) (l r : Nat → Capture) (uses : List (Nat × Mode)) : Prop :=
  ∀ u ∈ uses, Derives s (.variable (byMode (l u.1) u.2)) (.variable (byMode (r u.1) u.2))

theorem split {s : State} {l r : Nat → Capture} {one two : List (Nat × Mode)}
    (agree : Agreement s l r (one ++ two)) :
    Agreement s l r one ∧ Agreement s l r two :=
  ⟨fun u h => agree u (List.mem_append_left _ h), fun u h => agree u (List.mem_append_right _ h)⟩

mutual
 theorem substitute {s : State} (l r : Nat → Capture) (mode : Mode) (e : Expr)
    (agree : Agreement s l r (visits mode e)) :
    Derives s (logical l mode e) (logical r mode e) := by
  cases e with
  | «variable» key => exact agree (key,mode) List.mem_cons_self
  | primitive tag xs => exact .primitive (substitute_many l r mode xs agree)
  | nominal tag xs => exact .nominal (substitute_many l r .actual xs agree)
  | record label a b =>
    exact .record (substitute l r mode a (split agree).1) (substitute l r mode b (split agree).2)
  | variant label p => exact .variant (substitute l r mode p agree)
  | join a b =>
    exact .join (substitute l r mode a (split agree).1) (substitute l r mode b (split agree).2)
 termination_by sizeOf e

 theorem substitute_many {s : State} (l r : Nat → Capture) (mode : Mode) (es : List Expr)
    (agree : Agreement s l r (visitsMany mode es)) :
    Forest s (logicals l mode es) (logicals r mode es) := by
  cases es with
  | nil => exact .nil
  | cons first rest =>
    exact .cons (substitute l r mode first (split agree).1) (substitute_many l r mode rest (split agree).2)
 termination_by sizeOf es
end

/-- Changing representatives of actual type identities conserves an ordinary
output at the original target. Only the effective modes of variables read
by the particular source formula are compared. -/
theorem at_same_target {s : State} {l r : Nat → Capture} {mode : Mode} {exp : Expr}
    (first : Derives s (.variable target) (logical l mode exp))
    (agree : Agreement s l r (visits mode exp)) :
    Derives s (.variable target) (logical r mode exp) :=
  .trans first (substitute l r mode exp agree)

end Yulang.GeneralDeclarativeSubstitute322
