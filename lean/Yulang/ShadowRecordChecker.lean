import Yulang.ShadowRecordNormalization

/-!
# Exact ground checking and cut elimination for decision 40

The executable normalization uses only the previous, proved ground checker
to expose semantic record heads. Its exact interpretation theorem reduces
the full new relation to that previous checker. Inputs may have arbitrary
finite opaque tails and lattice syntax; no semantic comparison oracle,
successful cache, guessed type, or external fuel is supplied.

Rows still require a decidable preorder, as in the previous ground checker.
The normalization is not a canonical display representation, and this file
does not decide unknown graph variables or regular recursive value types.
-/

namespace Yulang.ShadowRecordChecker

open StructuralBase (Ty)
open ShadowSemanticRecords (Subtype Equivalent)
open ShadowRecordNormalization (normalize)

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

def check [DecidableEq Row] (rows : Row → Row → Bool) (source target : Ty Row) : Bool :=
  RigidRecordChecker.check rows (normalize rows source) (normalize rows target)

theorem check_true_iff [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (source target : Ty Row) : check rows source target = true ↔ Subtype leRow source target :=
  (RigidRecordChecker.check_true_iff rows rowExact rowRefl rowTrans _ _).trans
    (ShadowRecordNormalization.normalize_exact rows rowExact rowRefl rowTrans source target)

theorem check_false_iff [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (source target : Ty Row) : check rows source target = false ↔ ¬ Subtype leRow source target := by
  rw [← check_true_iff rows rowExact rowRefl rowTrans source target]
  exact Bool.eq_false_iff

/-- The actual old cut-free comparison of the computed normal forms. Its
atomic premises are Boolean checks at the preceding structural layer. -/
def Comparison [DecidableEq Row] (rows : Row → Row → Bool) (source target : Ty Row) : Prop :=
  RigidRecordChecker.Comparison rows (normalize rows source) (normalize rows target)

theorem comparison_iff_check [DecidableEq Row] (rows : Row → Row → Bool)
    (source target : Ty Row) : Comparison rows source target ↔ check rows source target = true :=
  RigidRecordChecker.comparison_iff_check rows _ _

/-- Arbitrary cuts in the new relation reduce to finite cut-free comparisons
after the proved, terminating shadow normalization. -/
theorem cut_elimination [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (source target : Ty Row) : Comparison rows source target ↔ Subtype leRow source target :=
  (comparison_iff_check rows source target).trans
    (check_true_iff rows rowExact rowRefl rowTrans source target)

theorem check_congr [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {source source' target target' : Ty Row}
    (first : Equivalent leRow source source') (last : Equivalent leRow target target') :
    check rows source target = check rows source' target' := by
  apply Bool.eq_iff_iff.mpr
  rw [check_true_iff rows rowExact rowRefl rowTrans,
    check_true_iff rows rowExact rowRefl rowTrans]
  exact ⟨fun below => .trans first.2 (.trans below last.1),
    fun below => .trans first.1 (.trans below last.2)⟩

/-- Hidden payloads do not affect any demanded type, including opaque ones. -/
theorem check_hidden_payload [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (label : Nat) (visible first last rest target : Ty Row) :
    check rows (.record label visible (.record label first rest)) target =
      check rows (.record label visible (.record label last rest)) target :=
  check_congr rows rowExact rowRefl rowTrans
    (ShadowSemanticRecords.hidden_payload_equivalent label visible first last rest) (.refl target)

end Yulang.ShadowRecordChecker
