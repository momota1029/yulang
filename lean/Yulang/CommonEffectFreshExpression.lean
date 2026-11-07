import Yulang.CommonEffectFreshRows

/-! Actual finite signed expressions across an explicitly allocated leading
scope. Old scope IDs shift by one; original row parameters are embedded,
never identified with padded originals. The theorem is row-specific and
makes no unproved order claim about the one-sided whole-type embedding. -/
namespace Yulang.CommonEffectFreshExpression
open Common (Occurrence Row)
open CommonEffectRequestGeneration (Computation Permission RowExpr)
open CommonEffectFreshRows (liftOccurrence liftRow lift_injective lift_shift)
open CommonSignedRows (Capturable commonResidual transport)

theorem lift_empty : liftRow Common.rowEmpty = Common.rowEmpty := by
  funext occurrence
  apply propext
  simp [liftRow, Common.rowEmpty]

theorem lift_join (first last : Row) :
    liftRow (Common.rowJoin first last) = Common.rowJoin (liftRow first) (liftRow last) := by
  funext occurrence
  apply propext
  simp only [liftRow, Common.rowJoin]
  constructor
  · rintro ⟨source, member, same⟩
    exact member.elim (fun present => Or.inl ⟨source, present, same⟩) (fun present => Or.inr ⟨source, present, same⟩)
  · rintro (⟨source, member, same⟩ | ⟨source, member, same⟩)
    · exact ⟨source, Or.inl member, same⟩
    · exact ⟨source, Or.inr member, same⟩

theorem lift_rowLe_exact (first last : Row) : Common.rowLe (liftRow first) (liftRow last) ↔ Common.rowLe first last := by
  constructor
  · intro included occurrence member
    obtain ⟨source, present, same⟩ := included (liftOccurrence occurrence) ⟨occurrence, member, rfl⟩
    exact lift_injective same ▸ present
  · rintro included occurrence ⟨source, member, same⟩
    exact ⟨source, included source member, same⟩

theorem lift_capturable (handled : List Nat) (occurrence : Occurrence) :
    Capturable handled (liftOccurrence occurrence) ↔ Capturable handled occurrence := by
  simp [Capturable, liftOccurrence]

theorem lift_transport (scope : Nat) (permission : Permission) (delta : Int) (row : Row) :
    liftRow (transport scope permission.allows delta row) = transport (scope + 1) permission.allows delta (liftRow row) := by
  funext occurrence
  apply propext
  rw [CommonSignedRows.transport_member_iff]
  constructor
  · rintro ⟨source, member, same⟩
    obtain ⟨original, present, rfl⟩ := (CommonSignedRows.transport_member_iff _ _ _ _ _).mp member
    exact ⟨liftOccurrence original, ⟨original, present, rfl⟩, (lift_shift scope permission delta original).symm.trans same⟩
  · rintro ⟨_, ⟨original, present, rfl⟩, same⟩
    exact ⟨CommonSignedRows.shiftOccurrence scope permission.allows delta original,
      (CommonSignedRows.transport_member_iff _ _ _ _ _).mpr ⟨original, present, rfl⟩,
      (lift_shift scope permission delta original).trans same⟩

theorem lift_residual (handled : List Nat) (row : Row) :
    liftRow (commonResidual handled row) = commonResidual handled (liftRow row) := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨original, ⟨member, uncaptured⟩, rfl⟩
    exact ⟨⟨original, member, rfl⟩, fun captured => uncaptured ((lift_capturable handled original).mp captured)⟩
  · rintro ⟨⟨original, member, rfl⟩, uncaptured⟩
    exact ⟨original, ⟨member, fun captured => uncaptured ((lift_capturable handled original).mpr captured)⟩, rfl⟩

theorem zero_coordinates (scopes : Nat) : List.ofFn (fun _ : Fin scopes => (0 : Int)) = List.replicate scopes 0 := by
  induction scopes <;> simp_all [List.ofFn_succ, List.replicate_succ]

theorem head_member (scopes key : Nat) (occurrence : Occurrence) :
    (CommonSignedRows.commonAlgebra scopes).head key occurrence ↔ occurrence = (key, List.replicate scopes 0) := by
  simp [CommonSignedRows.commonAlgebra, CommonSignedRows.embedRow, CommonSignedRows.encodeOccurrence, Directed.raw, zero_coordinates, eq_comm]

theorem lift_head (scopes key : Nat) :
    liftRow ((CommonSignedRows.commonAlgebra scopes).head key) = (CommonSignedRows.commonAlgebra (scopes + 1)).head key := by
  funext occurrence
  apply propext
  simp only [liftRow, head_member, exists_eq_left]
  simp [liftOccurrence, List.replicate_succ, eq_comm]

def lift : RowExpr scopes α → RowExpr (scopes + 1) α
  | .var name => .var name
  | .empty => .empty
  | .head key => .head key
  | .union first last => .union (lift first) (lift last)
  | .protect scope permission body => .protect scope.succ permission (lift body)
  | .release scope permission body => .release scope.succ permission (lift body)
  | .residual handled body => .residual handled (lift body)

/-- Target value components are arbitrary; only the same row embedding is
required. In particular the theorem does not erase or reselect captures. -/
theorem eval_lift (row : RowExpr scopes α) (before after : α → Computation)
    (sameRows : ∀ name, (after name).2 = liftRow (before name).2) :
    (lift row).eval after = liftRow (row.eval before) := by
  induction row with
  | var name => exact sameRows name
  | empty => exact lift_empty.symm
  | head key => exact (lift_head scopes key).symm
  | union first last iha ihb => simp only [lift, RowExpr.eval, iha, ihb, lift_join]
  | protect scope permission body ih =>
    simpa only [lift, RowExpr.eval, ih, Fin.val_succ, CommonSignedRows.commonProtect] using
      (lift_transport scope.val permission 1 (body.eval before)).symm
  | release scope permission body ih =>
    simpa only [lift, RowExpr.eval, ih, Fin.val_succ, CommonSignedRows.commonRelease] using
      (lift_transport scope.val permission (-1) (body.eval before)).symm
  | residual handled body ih => simp only [lift, RowExpr.eval, ih, lift_residual]

theorem inclusion_lift_exact (first last : RowExpr scopes α) (before after : α → Computation)
    (sameRows : ∀ name, (after name).2 = liftRow (before name).2) :
    Common.rowLe ((lift first).eval after) ((lift last).eval after) ↔ Common.rowLe (first.eval before) (last.eval before) := by
  rw [eval_lift first before after sameRows, eval_lift last before after sameRows]
  exact lift_rowLe_exact _ _

end Yulang.CommonEffectFreshExpression
