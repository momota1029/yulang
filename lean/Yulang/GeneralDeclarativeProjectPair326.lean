import Yulang.GeneralDeclarativeJoinedSpan326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProjectPair326
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativePairUnion326 (Coordinates)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativePairNames326 (Span)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeJoinedSpan326 (named_join)

def project : Expr → Option (Expr × Expr)
  | .primitive .pair [a,b] => some (a,b)
  | .join first last => do
      let (a,b) ← project first
      let (c,d) ← project last
      pure (.join a c,.join b d)
  | _ => none

theorem recorded (found : project expression = some (a,b)) :
    Coordinates expression a b := by
  cases expression with
  | primitive tag args =>
    cases tag with
    | scalar _ | emptyRecord | exactEmpty => cases found
    | pair =>
      cases args with
      | nil => cases found
      | cons x xs =>
        cases xs with
        | nil => cases found
        | cons y ys =>
          cases ys with
          | nil =>
            have same : (x,y) = (a,b) := Option.some.inj found
            cases same
            exact .literal
          | cons _ _ => cases found
  | join first last =>
    cases left : project first with
    | none => simp [project,left] at found
    | some ab =>
      rcases ab with ⟨x,y⟩
      cases right : project last with
      | none => simp [project,left,right] at found
      | some cd =>
        rcases cd with ⟨z,w⟩
        have same : (Expr.join x z,Expr.join y w) = (a,b) := by simpa [project,left,right] using found
        cases same
        exact .union (recorded left) (recorded right)
  | «variable» _ | nominal _ _ | record _ _ _ | variant _ _ => cases found
termination_by sizeOf expression

theorem complete (existsHere : Coordinates expression a b) : project expression = some (a,b) := by
  induction existsHere with
  | literal => rfl
  | union _ _ l r => simp [project,l,r]

theorem exact : project expression = some (a,b) ↔ Coordinates expression a b :=
  ⟨recorded,complete⟩

theorem same_coordinates (one : Coordinates expression left right) (two : Coordinates expression a b) :
    left = a ∧ right = b := by
  have equal := Option.some.inj ((complete one).symm.trans (complete two))
  exact ⟨congrArg Prod.fst equal,congrArg Prod.snd equal⟩

end Yulang.GeneralDeclarativeProjectPair326
