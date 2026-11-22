import Yulang.GeneralDeclarativeAlternativeView333

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeSpine333
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeAlternativeView333 (Offer Index Covers exact_offer)
open GeneralDeclarativeRecordSpine330 (Spine Terminal)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeNestedTail332 (peel exact_peel isTerminal ClosedAt)
open GeneralDeclarativeNestedSeek332 (terminal_seen)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row)

def isPrefix : Expr → Option Nat
  | .variable n => some n
  | _ => none

theorem prefix_exact (known : isPrefix term = some n) : term = .variable n := by
  cases term <;> cases known <;> rfl

theorem peel_keeps (stop : Expr) (noField : ∀ k f t, stop ≠ .record k f t) (row : Row Expr) :
    peel (withTail row stop) = (row,stop) := by
  induction row with
  | nil => cases stop <;> first | rfl | exact False.elim (noField _ _ _ rfl)
  | cons a rest ih =>
    rcases a with ⟨label,raw⟩
    simp [withTail,peel,ih]

theorem peel_terminal (closed : Terminal stop) (row : Row Expr) :
    peel (withTail row stop) = (row,stop) :=
  peel_keeps stop (by cases closed <;> intro _ _ _ bad <;> cases bad) row

theorem peel_variable (row : Row Expr) (n : Nat) :
    peel (withTail row (.variable n)) = (row,.variable n) :=
  peel_keeps _ (by intro _ _ _ nope; cases nope) _

def finishing (edge : Offer s root) : List (ClosedAt s root) :=
  let part := peel edge.rhs
  match isTerminal part.2 with
  | none => []
  | some stop => [⟨part,.inline edge.linked stop.down ((exact_peel edge.rhs).symm ▸ edge.stored)⟩]

def through (edge : Offer s root) (next : ∀ n, List (ClosedAt s n)) : List (ClosedAt s root) :=
  let part := peel edge.rhs
  match read : isPrefix part.2 with
  | none => []
  | some n => (next n).map fun tail => ⟨(part.1++tail.val.1,tail.val.2),
      have spelling : withTail part.1 (.variable n) = edge.rhs :=
        (prefix_exact read) ▸ exact_peel edge.rhs
      .prefixed edge.linked (spelling.symm ▸ edge.stored) tail.property⟩

/-- Enumerate exact closed spines from all independently backed row
spellings. More depth exposes witnesses but does not diagnose a
recurrence; nothing in this program decides language admission. -/
def spines (src : Index s) (root : Nat) : Nat → List (ClosedAt s root)
  | 0 => []
  | fuel+1 => (src root).flatMap fun edge =>
    finishing edge ++ through edge (fun n => spines src n fuel)

abbrev LiteralAt (s : State) (raw : Expr) :=
  { out : Row Expr × Expr // Closed s raw out.1 out.2 }

def literals (src : Index s) (fuel : Nat) : (raw : Expr) → List (LiteralAt s raw)
  | .variable n => (spines src n fuel).map fun tail => ⟨tail.val,.name tail.property⟩
  | .record label payload rest => (literals src fuel rest).map fun tail =>
      ⟨((label,payload)::tail.val.1,tail.val.2),.field tail.property⟩
  | .primitive .emptyRecord [] => [⟨([], .primitive .emptyRecord []), .terminal .width⟩]
  | .primitive .exactEmpty [] => [⟨([], .primitive .exactEmpty []), .terminal .exactEnd⟩]
  | _ => []

end Yulang.GeneralDeclarativeAlternativeSpine333
