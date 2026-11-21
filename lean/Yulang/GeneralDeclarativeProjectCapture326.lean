import Yulang.GeneralDeclarativeProjectInterval326
import Yulang.GeneralDeclarativeForwardHead325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProjectCapture326
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativePairNames326 (Span first second)
open GeneralDeclarativePairSpan326 (state)
open GeneralDeclarativeProjectInterval326 (projectAll names_and_actual)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeTermWalk322 (Walk Binds)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)

def capture (s : State) (kept : List Nat) (left right : Nat) (l r : Span)
    (base : Nat → Capture) : Nat → Capture :=
  fun n => if n = left then first s kept l r else if n = right then second s kept l r else base n

theorem identities {s : State} (kept : List Nat) (base : Nat → Capture) (separate : left ≠ right) :
    capture s kept left right l r base left = first s kept l r ∧
    capture s kept left right l r base right = second s kept l r := by
  simp [capture,Ne.symm separate]

/-- For the distinct-binder pair head, the genuine computed coordinate
names, rather than a caller-provided capture equation, produce the
usual normalized head fact at the original center and the child ranges. -/
theorem exact_head {s : State} {arg : Capture}
    (bounds : Bounds s arg) (lowSeen : Derives s (.variable arg.lower) low)
    (midSeen : Derives s (.variable arg.center) mid) (highSeen : Derives s (.variable arg.upper) high)
    (read : projectAll low mid high = some (l,r)) (kept : List Nat)
    (base : Nat → Capture) (separate : left ≠ right)
    (pattern : translate c i (normalize pat) = some (pair (.variable left) (.variable right))) :
    Bounds (state s kept l r) ((capture s kept left right l r base) left) ∧
    Bounds (state s kept l r) ((capture s kept left right l r base) right) ∧
    Result (state s kept l r) (fact c i (capture s kept left right l r base) arg pat) := by
  obtain ⟨leftEq,rightEq⟩ := identities (s := s) (l := l) (r := r) kept base separate
  obtain ⟨leftBound,rightBound,_,actual⟩ := names_and_actual bounds lowSeen midSeen highSeen read kept
  refine ⟨leftEq ▸ leftBound,rightEq ▸ rightBound,?_⟩
  refine GeneralDeclarativeForwardHead325.by_walk pattern actual
    (.primitive (.cons .capture (.cons .capture .nil))) ?_
  intro o occurs
  change o ∈ [_,_] at occurs
  rcases List.mem_cons.mp occurs with rfl|rightOcc
  · rw [GeneralDeclarativeHead320.byMode,leftEq]
    exact .refl _
  · cases List.mem_singleton.mp rightOcc
    rw [GeneralDeclarativeHead320.byMode,rightEq]
    exact .refl _

end Yulang.GeneralDeclarativeProjectCapture326
