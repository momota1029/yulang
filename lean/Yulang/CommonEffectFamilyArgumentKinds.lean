import Yulang.CommonEffectMixedFamilyAllocation

/-!
Kind admission for the original endpoints of invariant family arguments.
Every captured name is checked, including names below signed protection,
release, residual masks, and function-type row positions. The source table
may be finite and a missing name is rejected; metadata for resolved effect
keys and scope coordinates is unchanged.

This does not discover which declaration arguments are invariant. Its input
is the already distinguished family-argument syntax used by the allocator.
-/
namespace Yulang.CommonEffectFamilyArgumentKinds
open CommonEffectRequestGeneration (RowExpr)
open CommonEffectMixedKinds (Kind checkType TypeKinded check_type_exact)
open CommonEffectMixedFamilyAllocation (Argument)
open CommonEffectRowIntervalConstraints (Bounds)

def checkSignedRow (kinds : α → Option Kind) : RowExpr scopes α → Bool
  | .var name => kinds name == some .row
  | .empty | .head _ => true
  | .union first last => checkSignedRow kinds first && checkSignedRow kinds last
  | .protect _ _ source | .release _ _ source | .residual _ source =>
      checkSignedRow kinds source

inductive SignedRowKinded (kinds : α → Option Kind) : RowExpr scopes α → Prop where
  | var : kinds name = some .row → SignedRowKinded kinds (.var name)
  | empty : SignedRowKinded kinds .empty
  | head : SignedRowKinded kinds (.head key)
  | union : SignedRowKinded kinds first → SignedRowKinded kinds last →
      SignedRowKinded kinds (.union first last)
  | protect : SignedRowKinded kinds source → SignedRowKinded kinds (.protect scope permission source)
  | release : SignedRowKinded kinds source → SignedRowKinded kinds (.release scope permission source)
  | residual : SignedRowKinded kinds source → SignedRowKinded kinds (.residual handled source)

theorem check_signed_row_exact (kinds : α → Option Kind) (row : RowExpr scopes α) :
    checkSignedRow kinds row = true ↔ SignedRowKinded kinds row := by
  induction row with
  | var name =>
    simp only [checkSignedRow, beq_iff_eq]
    exact ⟨SignedRowKinded.var, fun h => by cases h; assumption⟩
  | empty => exact ⟨fun _ => .empty, fun _ => rfl⟩
  | head key => exact ⟨fun _ => .head, fun _ => rfl⟩
  | union first last firstIH lastIH =>
    simp only [checkSignedRow, Bool.and_eq_true, firstIH, lastIH]
    exact ⟨fun ⟨a, b⟩ => .union a b, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩
  | protect scope permission source ih =>
    simp only [checkSignedRow, ih]
    exact ⟨SignedRowKinded.protect, fun h => by cases h; assumption⟩
  | release scope permission source ih =>
    simp only [checkSignedRow, ih]
    exact ⟨SignedRowKinded.release, fun h => by cases h; assumption⟩
  | residual handled source ih =>
    simp only [checkSignedRow, ih]
    exact ⟨SignedRowKinded.residual, fun h => by cases h; assumption⟩

def checkBounds (kinds : α → Option Kind) (bounds : Bounds scopes α) : Bool :=
  bounds.lower.all (checkSignedRow kinds) && bounds.upper.all (checkSignedRow kinds)

def BoundsKinded (kinds : α → Option Kind) (bounds : Bounds scopes α) : Prop :=
  (∀ endpoint ∈ bounds.lower, SignedRowKinded kinds endpoint) ∧
    (∀ endpoint ∈ bounds.upper, SignedRowKinded kinds endpoint)

theorem check_bounds_exact (kinds : α → Option Kind) (bounds : Bounds scopes α) :
    checkBounds kinds bounds = true ↔ BoundsKinded kinds bounds := by
  simp only [checkBounds, Bool.and_eq_true, List.all_eq_true, check_signed_row_exact, BoundsKinded]

def checkArgument (kinds : α → Option Kind) : Argument scopes α → Bool
  | .value bounds => checkType kinds bounds.lower && checkType kinds bounds.upper
  | .row bounds => checkBounds kinds bounds

def ArgumentKinded (kinds : α → Option Kind) : Argument scopes α → Prop
  | .value bounds => TypeKinded kinds bounds.lower ∧ TypeKinded kinds bounds.upper
  | .row bounds => BoundsKinded kinds bounds

/-- Endpoint checks inspect both ends and every captured occurrence. They
do not silently accept an unresolved name because the outer argument kind
already agrees with the declaration. -/
theorem check_argument_exact (kinds : α → Option Kind) (argument : Argument scopes α) :
    checkArgument kinds argument = true ↔ ArgumentKinded kinds argument := by
  cases argument with
  | value bounds =>
    simp only [checkArgument, Bool.and_eq_true, check_type_exact, ArgumentKinded]
  | row bounds => exact check_bounds_exact kinds bounds

end Yulang.CommonEffectFamilyArgumentKinds
