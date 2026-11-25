import Yulang.GeneralDeclarativeI65I74MixedRecordPriority413

namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413
open GeneralDeclarations (Declaration)

/-- The scan's shape, forgetting proofs and source ordinals. The
opener count is saturated: two openers are unsupported in this scope. -/
inductive ScanFlag
  | unusable
  | bindings
  | oneOpening
  deriving DecidableEq, Repr

def ScanFlag.combine : ScanFlag → ScanFlag → ScanFlag
  | .bindings, f | f, .bindings => f
  | _,_ => .unusable

theorem flags_comm413 (a b : ScanFlag) : a.combine b = b.combine a := by
  cases a <;> cases b <;> rfl

theorem flags_assoc413 (a b c : ScanFlag) :
    (a.combine b).combine c = a.combine (b.combine c) := by
  cases a <;> cases b <;> cases c <;> rfl

def rowFlag413 {s q} (o : ActualOuterRecord s q) (d : Declaration) : ScanFlag :=
  match readRow413 o d with
  | none => .unusable
  | some (.binding _) => .bindings
  | some (.nested _) => .oneOpening

def foldedFlags413 {s q} (o : ActualOuterRecord s q) : List Declaration → ScanFlag
  | [] => .bindings
  | row :: rest => (rowFlag413 o row).combine (foldedFlags413 o rest)

def shapeFlag413 {s q} {o : ActualOuterRecord s q} {rows} :
    Option (ListShape o rows) → ScanFlag
  | none => .unusable
  | some (.plain _) => .bindings
  | some (.mixed _) => .oneOpening

theorem full_scan_flags_exact413 {s q} (o : ActualOuterRecord s q) (rows : List Declaration) :
    shapeFlag413 (scanAll413 o rows) = foldedFlags413 o rows := by
  induction rows with
  | nil => rfl
  | cons d rest ih =>
    rw [foldedFlags413,← ih]
    cases first : readRow413 o d with
    | none =>
      cases remaining : scanAll413 o rest with
      | none => simp [scanAll413,rowFlag413,shapeFlag413,first,remaining,ScanFlag.combine]
      | some data =>
        cases data <;> simp [scanAll413,rowFlag413,shapeFlag413,first,remaining,ScanFlag.combine]
    | some actual =>
      cases actual <;>
        cases remaining : scanAll413 o rest with
        | none => simp [scanAll413,rowFlag413,shapeFlag413,first,remaining,ScanFlag.combine]
        | some data =>
          cases data <;> simp [scanAll413,rowFlag413,shapeFlag413,first,remaining,ScanFlag.combine]

theorem folded_flags_independent_of_order413 {s q} (o : ActualOuterRecord s q)
    {first second : List Declaration} (perm : first.Perm second) :
    foldedFlags413 o first = foldedFlags413 o second := by
  induction perm with
  | nil => rfl
  | cons d _ ih => simp only [foldedFlags413,ih]
  | swap d e keep =>
    simp only [foldedFlags413]
    rw [← flags_assoc413,← flags_assoc413,flags_comm413 (rowFlag413 o e) (rowFlag413 o d)]
  | trans _ _ left right => exact left.trans right

/-- Order cannot erase the valid complete mixed scan, with fixed root
and independent constructor/source-role tables. The actual indexed
tape is rebuilt, so the opener gets its new ordinal. -/
theorem full_scan_shape_independent_of_order413 {s q} (o : ActualOuterRecord s q)
    {first second : List Declaration} (perm : first.Perm second) :
    shapeFlag413 (scanAll413 o first) = shapeFlag413 (scanAll413 o second) := by
  rw [full_scan_flags_exact413,full_scan_flags_exact413]
  exact folded_flags_independent_of_order413 o perm

theorem mixed_scan_recovers_tape_after_permutation413 {s q} {o : ActualOuterRecord s q}
    {first second : List Declaration} (perm : first.Perm second) {old : MixedTape o first}
    (before : scanAll413 o first = some (.mixed old)) :
    ∃ current : MixedTape o second, scanAll413 o second = some (.mixed current) := by
  have symmetry := full_scan_shape_independent_of_order413 o perm
  rw [before] at symmetry
  cases exact : scanAll413 o second with
  | none => simp [exact,shapeFlag413] at symmetry
  | some x =>
    cases x with
    | plain => simp [exact,shapeFlag413] at symmetry
    | mixed tape => exact ⟨tape,rfl⟩

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413
