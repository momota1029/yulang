import Yulang.RowTransportNormalForm

/-!
# Finite transport programs in the existing row syntax

The wrapper below expresses a guarded transport program using only the existing
`RowExpr` protection, release and residual constructors. Its evaluation theorem
uses the established possibly infinite set-row algebra and keeps every guard
at its original point in the program.
-/

namespace Yulang.FinitePointGuards

open Directed
open RowInference (RowExpr)
open RecursiveRowGraph (Action Program)
open RecursiveRows (Environment)

variable {n : Nat} {Key Slot : Type}

def applyAction : Action n Key → RowExpr Key (Fin n) Slot → RowExpr Key (Fin n) Slot
  | .protect scope permission, row => .protect scope permission row
  | .release scope permission, row => .release scope permission row
  | .residual handled, row => .residual handled row

theorem eval_applyAction [DecidableEq Key] (action : Action n Key)
    (row : RowExpr Key (Fin n) Slot) (rows : Environment n Key Slot) (output : Occurrence n Key) :
    (applyAction action row).eval (RecursiveRows.algebra n Key) rows output ↔
      action.image (row.eval (RecursiveRows.algebra n Key) rows) output := by
  cases action with
  | protect scope permission =>
      simp [applyAction, RowExpr.eval, RecursiveRows.algebra, Action.image, Action.run]
  | release scope permission =>
      simp [applyAction, RowExpr.eval, RecursiveRows.algebra, Action.image, Action.run]
  | residual handled => exact (Action.residual_image handled _ output).symm

/-- The first program action is the innermost row operation. -/
def wrap : Program n Key → RowExpr Key (Fin n) Slot → RowExpr Key (Fin n) Slot
  | [], row => row
  | action :: rest, row => wrap rest (applyAction action row)

theorem eval_wrap [DecidableEq Key] (program : Program n Key)
    (row : RowExpr Key (Fin n) Slot) (rows : Environment n Key Slot) (output : Occurrence n Key) :
    (wrap program row).eval (RecursiveRows.algebra n Key) rows output ↔
      ∃ input, row.eval (RecursiveRows.algebra n Key) rows input ∧
        Program.run program input = some output := by
  induction program generalizing row output with
  | nil =>
      constructor
      · intro member; exact ⟨output, member, rfl⟩
      · rintro ⟨input, member, execution⟩
        cases Option.some.inj execution
        exact member
  | cons action rest ih =>
      rw [wrap, ih]
      constructor
      · rintro ⟨middle, middleMember, remainder⟩
        obtain ⟨input, inputMember, first⟩ := (eval_applyAction action row rows middle).mp middleMember
        exact ⟨input, inputMember, by simpa [Program.run, first] using remainder⟩
      · rintro ⟨input, member, execution⟩
        cases first : action.run input with
        | none => simp [Program.run, first] at execution
        | some middle =>
            exact ⟨middle, (eval_applyAction action row rows middle).mpr ⟨input, member, first⟩,
              by simpa [Program.run, first] using execution⟩

end Yulang.FinitePointGuards
