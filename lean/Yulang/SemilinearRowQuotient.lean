import Yulang.SemilinearRowAlgebra
import Yulang.StructuralRowResolution

/-!
# Exact ground comparison modulo semilinear row meaning

Finite semilinear codes may denote the same infinite row. Their quotient by
the already decidable set equality has computable equality and injects into
the existing `RecursiveRows.SetRow` carrier. The structural checker therefore
decides the original set-row subtype relation, including reflexivity on every
raw ground type. No canonical semilinear normal form is assumed.
-/

namespace Yulang.SemilinearRowQuotient

open StructuralBase StructuralRowResolution

variable {n : Nat} {Key : Type} [DecidableEq Key]

def equivalence (n : Nat) (Key : Type) [DecidableEq Key] :
    Setoid (SemilinearRowAlgebra.Row n Key) where
  r left right := SemilinearRowAlgebra.decode left = SemilinearRowAlgebra.decode right
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev Row (n : Nat) (Key : Type) [DecidableEq Key] := Quotient (equivalence n Key)

instance equivalentDecidable (left right : SemilinearRowAlgebra.Row n Key) :
    Decidable ((equivalence n Key).r left right) :=
  if same : SemilinearRowAlgebra.checkEqual left right = true then
    .isTrue ((SemilinearRowAlgebra.checkEqual_sets left right).mp same)
  else
    .isFalse (fun equal => same ((SemilinearRowAlgebra.checkEqual_sets left right).mpr equal))

def encode (row : SemilinearRowAlgebra.Row n Key) : Row n Key := Quotient.mk _ row

def decode : Row n Key → RecursiveRows.SetRow n Key :=
  Quotient.lift SemilinearRowAlgebra.decode (fun _ _ same => same)

@[simp] theorem decode_encode (row : SemilinearRowAlgebra.Row n Key) :
    decode (encode row) = SemilinearRowAlgebra.decode row := rfl

theorem decode_injective : Function.Injective (decode (n := n) (Key := Key)) := by
  intro left right
  induction left using Quotient.inductionOn with
  | h left =>
      induction right using Quotient.inductionOn with
      | h right => exact fun same => Quotient.sound same

def Included (left right : Row n Key) : Prop :=
  ∀ occurrence, decode left occurrence → decode right occurrence

theorem included_refl (row : Row n Key) : Included row row := fun _ member => member

theorem included_trans {left middle right : Row n Key}
    (first : Included left middle) (second : Included middle right) : Included left right :=
  fun occurrence member => second occurrence (first occurrence member)

theorem checkSubset_respects (left right left' right' : SemilinearRowAlgebra.Row n Key)
    (first : SemilinearRowAlgebra.decode left = SemilinearRowAlgebra.decode left')
    (second : SemilinearRowAlgebra.decode right = SemilinearRowAlgebra.decode right') :
    SemilinearRowAlgebra.checkSubset left right =
      SemilinearRowAlgebra.checkSubset left' right' := by
  apply Bool.eq_iff_iff.mpr
  rw [SemilinearRowAlgebra.checkSubset_sets, SemilinearRowAlgebra.checkSubset_sets, first, second]

def checkSubset (left right : Row n Key) : Bool :=
  Quotient.liftOn₂ left right SemilinearRowAlgebra.checkSubset checkSubset_respects

theorem checkSubset_exact (left right : Row n Key) :
    checkSubset left right = true ↔ Included left right := by
  induction left using Quotient.inductionOn with
  | h left =>
      induction right using Quotient.inductionOn with
      | h right => exact SemilinearRowAlgebra.checkSubset_sets left right

abbrev GroundType (n : Nat) (Key : Type) [DecidableEq Key] := Ty (Row n Key)

def encodeType (type : SemilinearRowAlgebra.GroundType n Key) : GroundType n Key := mapRows encode type

def decodeType (type : GroundType n Key) : Ty (RecursiveRows.SetRow n Key) := mapRows decode type

def checkType (source target : GroundType n Key) : Bool := StructuralDecisions.check checkSubset source target

theorem checkType_exact (source target : GroundType n Key) :
    checkType source target = true ↔
      Subtype (RecursiveRows.algebra n Key).le (decodeType source) (decodeType target) := by
  rw [checkType, StructuralDecisions.check_exact checkSubset
    (fun left right => checkSubset_exact left right) (fun first second => included_trans first second)]
  exact subtype_map_iff decode decode_injective
    (leA := Included) (leB := (RecursiveRows.algebra n Key).le) (fun _ _ => Iff.rfl)
    (fun first second occurrence member => second occurrence (first occurrence member)) source target

theorem checkType_rejects (source target : GroundType n Key) :
    checkType source target = false ↔
      ¬ Subtype (RecursiveRows.algebra n Key).le (decodeType source) (decodeType target) := by
  rw [← Bool.not_eq_true, checkType_exact]

/-- Unlike syntactic equality of codes, this comparison uses exact row meaning
even in the reflexive case of an otherwise malformed raw record spine. -/
def compareCodes (source target : SemilinearRowAlgebra.GroundType n Key) : Bool :=
  checkType (encodeType source) (encodeType target)

theorem compareCodes_exact (source target : SemilinearRowAlgebra.GroundType n Key) :
    compareCodes source target = true ↔
      Subtype (RecursiveRows.algebra n Key).le
        (mapRows SemilinearRowAlgebra.decode source) (mapRows SemilinearRowAlgebra.decode target) := by
  rw [compareCodes, checkType_exact]
  simp only [encodeType, decodeType, mapRows_comp]
  rfl

end Yulang.SemilinearRowQuotient
