import Yulang.CommonSignedTransport

/-!
# Exact effect-row interpretation, including handler subtraction

Subtraction removes precisely handled keys at all-zero weight vectors. Negative
coordinates are retained. The operations are total on arbitrary Common row
parameters; only the finite syntax interpretation uses a fixed scope arity.
-/

namespace Yulang.CommonSignedRows

def Capturable (handled : List Nat) (occurrence : Common.Occurrence) : Prop :=
  occurrence.1 ∈ handled ∧ ∀ weight ∈ occurrence.2, weight = 0

theorem encode_capturable_iff (handled : List Nat) (occurrence : Directed.Occurrence n Nat) :
    Capturable handled (encodeOccurrence occurrence) ↔ Directed.Capturable handled occurrence := by
  simp only [Capturable, encodeOccurrence, Directed.Capturable, List.mem_ofFn]
  constructor
  · rintro ⟨key, weights⟩
    exact ⟨key, fun coordinate => weights (occurrence.weights coordinate) ⟨coordinate, rfl⟩⟩
  · rintro ⟨key, weights⟩
    refine ⟨key, ?_⟩
    rintro weight ⟨coordinate, rfl⟩
    exact weights coordinate

def commonResidual (handled : List Nat) (row : Common.Row) : Common.Row :=
  fun occurrence => row occurrence ∧ ¬ Capturable handled occurrence

theorem embedRow_residual (handled : List Nat) (row : Directed.Row n Nat) :
    embedRow (Directed.residual handled row) = commonResidual handled (embedRow row) := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨source, member, rfl⟩
    have filtered := List.mem_filter.mp member
    have notCaptured : ¬ Directed.Capturable handled source := by
      simpa using filtered.2
    exact ⟨⟨source, filtered.1, rfl⟩,
      fun captured => notCaptured ((encode_capturable_iff _ _).mp captured)⟩
  · rintro ⟨⟨source, member, rfl⟩, notCaptured⟩
    refine ⟨source, List.mem_filter.mpr ⟨member, ?_⟩, rfl⟩
    have denied : ¬ Directed.Capturable handled source :=
      fun captured => notCaptured ((encode_capturable_iff _ _).mpr captured)
    simpa using denied

/-- The complete row-interpretation contract: every finite scope interface,
every signed source row, all target rows, all masks and handled key lists. -/
theorem common_effect_row_interpretation_exact (n : Nat)
    (first last : Directed.Row n Nat) (scope : Fin n) (permission : Nat → Bool)
    (handled : List Nat) :
    (SignedStructural.RowLe first last ↔ Common.rowLe (embedRow first) (embedRow last)) ∧
    embedRow (first.map (Directed.protect scope permission)) =
      commonProtect scope.val permission (embedRow first) ∧
    embedRow (first.map (Directed.release scope permission)) =
      commonRelease scope.val permission (embedRow first) ∧
    embedRow (Directed.residual handled first) = commonResidual handled (embedRow first) :=
  ⟨embedRow_le_iff first last, embedRow_protect scope permission first,
    embedRow_release scope permission first, embedRow_residual handled first⟩

theorem nonzero_retained (handled : List Nat) (row : Common.Row)
    (occurrence : Common.Occurrence) (member : row occurrence) (weight : Int)
    (present : weight ∈ occurrence.2) (nonzero : weight ≠ 0) :
    commonResidual handled row occurrence :=
  ⟨member, fun captured => nonzero (captured.2 weight present)⟩

/-- The fixed declaration arity controls raw operation heads, but the row
carrier remains the full set of Common occurrences. -/
def commonAlgebra (n : Nat) : RowInference.RowAlgebra Nat (Fin n) where
  Row := Common.Row
  empty := Common.rowEmpty
  join := Common.rowJoin
  head := fun key => embedRow [Directed.raw (n := n) key]
  protect := fun scope permission => commonProtect scope.val permission
  release := fun scope permission => commonRelease scope.val permission
  residual := commonResidual
  le := Common.rowLe

theorem rowExpr_interpretation_exact (n : Nat)
    (assignment : α → Directed.Row n Nat) (expression : RowInference.RowExpr Nat (Fin n) α) :
    embedRow (expression.eval (RowInference.signedAlgebra n Nat) assignment) =
      expression.eval (commonAlgebra n) (fun name => embedRow (assignment name)) := by
  induction expression with
  | empty => exact embedRow_empty
  | head key => rfl
  | var name => rfl
  | union first last firstIH lastIH =>
      exact (embedRow_join _ _).trans (congr (congrArg Common.rowJoin firstIH) lastIH)
  | protect scope permission source ih =>
      exact (embedRow_protect scope permission _).trans
        (congrArg (commonProtect scope.val permission) ih)
  | release scope permission source ih =>
      exact (embedRow_release scope permission _).trans
        (congrArg (commonRelease scope.val permission) ih)
  | residual handled source ih =>
      exact (embedRow_residual handled _).trans (congrArg (commonResidual handled) ih)

theorem rowExpr_le_exact (n : Nat) (assignment : α → Directed.Row n Nat)
    (first last : RowInference.RowExpr Nat (Fin n) α) :
    (RowInference.signedAlgebra n Nat).le
      (first.eval (RowInference.signedAlgebra n Nat) assignment)
      (last.eval (RowInference.signedAlgebra n Nat) assignment) ↔
    Common.rowLe (first.eval (commonAlgebra n) (fun name => embedRow (assignment name)))
      (last.eval (commonAlgebra n) (fun name => embedRow (assignment name))) := by
  exact (embedRow_le_iff _ _).trans (Iff.of_eq (congr (congrArg Common.rowLe
    (rowExpr_interpretation_exact n assignment first))
    (rowExpr_interpretation_exact n assignment last)))

end Yulang.CommonSignedRows
