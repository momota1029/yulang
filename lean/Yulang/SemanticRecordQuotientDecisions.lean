import Yulang.SemanticRecordChecker
import Yulang.SemanticRecordQuotient

/-!
# Executable order and equality on semantic record types

The raw ground checker is independent of the representative of a semantic
type. It therefore descends through the quotient directly, without selecting
a canonical syntax tree. Its two-direction check decides actual quotient
equality. This does not construct the display normal form from decision 35.
-/

namespace Yulang.SemanticRecordQuotientDecisions

open StructuralBase (Ty)
open SemanticRecords (Subtype Equivalent)
open SemanticRecordQuotient (QTy mk le)

universe u

variable {Row : Type u} {leRow : Row → Row → Prop}

theorem raw_check_congr [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {a a' b b' : Ty Row} (left : Equivalent leRow a a') (right : Equivalent leRow b b') :
    SemanticRecordChecker.check rows a b = SemanticRecordChecker.check rows a' b' := by
  apply Bool.eq_iff_iff.mpr
  change SemanticRecordChecker.check rows a b = true ↔ SemanticRecordChecker.check rows a' b' = true
  rw [SemanticRecordChecker.check_true_iff rows rowExact rowRefl rowTrans,
    SemanticRecordChecker.check_true_iff rows rowExact rowRefl rowTrans]
  exact ⟨fun below => .trans left.2 (.trans below right.1),
    fun below => .trans left.1 (.trans below right.2)⟩

/-- The proof arguments establish well-definedness and are erased during
execution. The only comparison called at runtime is the finite raw checker. -/
def check [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c) :
    QTy leRow → QTy leRow → Bool :=
  Quotient.lift₂ (SemanticRecordChecker.check rows)
    (fun _ _ _ _ left right => raw_check_congr rows rowExact rowRefl rowTrans left right)

@[simp] theorem check_mk [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (a b : Ty Row) :
    check rows rowExact rowRefl rowTrans (mk a) (mk b) = SemanticRecordChecker.check rows a b := rfl

theorem check_true_iff [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (a b : QTy leRow) : check rows rowExact rowRefl rowTrans a b = true ↔ le a b := by
  refine Quotient.inductionOn₂ a b ?_
  intro left right
  exact SemanticRecordChecker.check_true_iff rows rowExact rowRefl rowTrans left right

def equal [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (a b : QTy leRow) : Bool :=
  check rows rowExact rowRefl rowTrans a b && check rows rowExact rowRefl rowTrans b a

theorem equal_true_iff [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (a b : QTy leRow) : equal rows rowExact rowRefl rowTrans a b = true ↔ a = b := by
  simp only [equal, Bool.and_eq_true_iff, check_true_iff rows rowExact rowRefl rowTrans]
  exact (SemanticRecordQuotient.eq_iff_mutual_subtype a b).symm

/-- An executable decision procedure for the quotient order. -/
def decideLe [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (a b : QTy leRow) : Decidable (le a b) :=
  if accepted : check rows rowExact rowRefl rowTrans a b = true then
    .isTrue ((check_true_iff rows rowExact rowRefl rowTrans a b).mp accepted)
  else
    .isFalse (fun below => accepted ((check_true_iff rows rowExact rowRefl rowTrans a b).mpr below))

/-- Equality is decided by mutual subtyping, with no canonical representative
or classical choice of a representative in the executable definition. -/
def decideEq [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c) : DecidableEq (QTy leRow) :=
  fun a b =>
    if accepted : equal rows rowExact rowRefl rowTrans a b = true then
      .isTrue ((equal_true_iff rows rowExact rowRefl rowTrans a b).mp accepted)
    else
      .isFalse (fun same => accepted ((equal_true_iff rows rowExact rowRefl rowTrans a b).mpr same))

end Yulang.SemanticRecordQuotientDecisions
