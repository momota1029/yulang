import Yulang.CommonCanonicalIntervals

/-!
# Complete family codes for shared scalar-result arrows

The input is one generalized slot, which may also occur arbitrarily often
in the scalar union/intersection result. Other generalized result slots are
independent; captured slots and the incoming/outgoing row IDs stay fixed.
This is a mixed-polarity language: `a -> a` and `a -> b` are both present,
and their distinct instance families are not identified.

The least possible result at an arbitrary required argument `A` is computed
by assigning `A` to the shared input slot and bottom to every other local
slot. Its finite scalar code, together with both row IDs, completely decides
equality of the subtype-instance families, across different local arities.
Every parameter and target ranges over arbitrary common types, including
regular types; no candidate reparameterization or semantic oracle is given.

This closed fragment has one arrow, a generalized variable as its domain,
and a scalar result. Arbitrary arrow-domain expressions, nested constructor
results, generalized rows, role obligations and full public readback are
outside this module. A separate adapter uses the existing public interface
semantics rather than redefining that semantics here.
-/

namespace Yulang.CommonCanonicalArrowFamilies

open Common (Ty Row Subtype Equivalent)
open ProducerCanonicalOpen (Expr Atom)

variable {fixed rowSlots generalized other : Nat}

structure Scheme (fixed rowSlots generalized : Nat) where
  incoming : Fin rowSlots
  outgoing : Fin rowSlots
  input : Fin generalized
  output : Expr (fixed + generalized)

def selected (input : Fin generalized) (value : Ty) : Fin generalized → Ty :=
  fun index => if index = input then value else .bottom

@[simp] theorem selected_input (input : Fin generalized) (value : Ty) :
    selected input value input = value := by simp [selected]

def transfer (scheme : Scheme fixed rowSlots generalized) : Expr (fixed + 1) :=
  CommonCanonicalParameters.substituteExpr
    (Fin.addCases (fun index => .atom (.var index.castSucc))
      (fun index => if index = scheme.input then .atom (.var (Fin.last fixed)) else .bottom))
    scheme.output

def applyTransfer (scheme : Scheme fixed rowSlots generalized)
    (captured : Fin fixed → Ty) (input : Ty) : Ty :=
  CommonCanonicalOpen.instantiate (Fin.lastCases input captured) (transfer scheme)

def instantiate (scheme : Scheme fixed rowSlots generalized) (rows : Fin rowSlots → Row)
    (captured : Fin fixed → Ty) (parameters : Fin generalized → Ty) : Ty :=
  Common.arrow (parameters scheme.input) (rows scheme.incoming)
    (CommonCanonicalOpen.instantiate (Fin.addCases captured parameters) scheme.output) (rows scheme.outgoing)

def Instances (scheme : Scheme fixed rowSlots generalized) (rows : Fin rowSlots → Row)
    (captured : Fin fixed → Ty) (target : Ty) : Prop :=
  ∃ parameters : Fin generalized → Ty, Subtype (instantiate scheme rows captured parameters) target

def FamilyEquivalent (first : Scheme fixed rowSlots generalized) (last : Scheme fixed rowSlots other) : Prop :=
  ∀ rows : Fin rowSlots → Row, ∀ captured : Fin fixed → Ty, ∀ target : Ty,
    Instances first rows captured target ↔ Instances last rows captured target

theorem applyTransfer_eq (scheme : Scheme fixed rowSlots generalized)
    (captured : Fin fixed → Ty) (input : Ty) :
    applyTransfer scheme captured input =
      CommonCanonicalOpen.instantiate (Fin.addCases captured (selected scheme.input input)) scheme.output := by
  rw [applyTransfer, transfer, CommonCanonicalParameters.instantiate_substituteExpr]
  congr 1
  funext index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index
  · simp [CommonCanonicalOpen.instantiate, CommonCanonicalOpen.atomType]
  · by_cases same : index = scheme.input <;>
      simp [same, selected, CommonCanonicalOpen.instantiate, CommonCanonicalOpen.atomType]

theorem transfer_le_output (scheme : Scheme fixed rowSlots generalized)
    (captured : Fin fixed → Ty) (parameters : Fin generalized → Ty) (input : Ty)
    (below : Subtype input (parameters scheme.input)) :
    Subtype (applyTransfer scheme captured input)
      (CommonCanonicalOpen.instantiate (Fin.addCases captured parameters) scheme.output) := by
  rw [applyTransfer_eq]
  apply CommonCanonicalIntervals.instantiate_mono
  intro index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index
  · simpa only [Fin.addCases_left] using Common.subtype_refl (captured index)
  · simp only [Fin.addCases_right, selected]
    split
    · rename_i same
      simpa only [same] using below
    · exact CommonBoundCoalescing.bottom_le _

theorem instantiate_selected (scheme : Scheme fixed rowSlots generalized) (rows : Fin rowSlots → Row)
    (captured : Fin fixed → Ty) (input : Ty) :
    instantiate scheme rows captured (selected scheme.input input) =
      Common.arrow input (rows scheme.incoming) (applyTransfer scheme captured input) (rows scheme.outgoing) := by
  simp only [instantiate, selected_input, applyTransfer_eq]

/-- All domain/output sharing is accounted for by the computed transfer.
The required argument, both required rows and the output are arbitrary. -/
theorem instances_arrow_exact (scheme : Scheme fixed rowSlots generalized) (rows : Fin rowSlots → Row)
    (captured : Fin fixed → Ty) (input output : Ty) (incoming outgoing : Row) :
    Instances scheme rows captured (Common.arrow input incoming output outgoing) ↔
      Common.rowLe incoming (rows scheme.incoming) ∧
        Subtype (applyTransfer scheme captured input) output ∧ Common.rowLe (rows scheme.outgoing) outgoing := by
  constructor
  · rintro ⟨parameters, below⟩
    have parts := (Common.common_arrow_iff _ _ _ _ _ _ _ _).mp below
    exact ⟨parts.2.1, Common.subtype_trans (transfer_le_output scheme captured parameters input parts.1)
      parts.2.2.1, parts.2.2.2⟩
  · rintro ⟨incomingBelow, outputBelow, outgoingBelow⟩
    refine ⟨selected scheme.input input, ?_⟩
    rw [instantiate_selected]
    exact (Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
      ⟨Common.subtype_refl _, incomingBelow, outputBelow, outgoingBelow⟩

private theorem row_ids_equal {first last : Fin rowSlots}
    (below : ∀ rows : Fin rowSlots → Row, Common.rowLe (rows first) (rows last)) : first = last := by
  exact (below (fun index _ => index = first) (0, []) rfl).symm

/-- Semantic family equality forces the same row identities, even though
the generalized type parameters on the two sides may have different sizes. -/
theorem family_rows_equal (first : Scheme fixed rowSlots generalized) (last : Scheme fixed rowSlots other)
    (same : FamilyEquivalent first last) : first.incoming = last.incoming ∧ first.outgoing = last.outgoing := by
  have forward (rows : Fin rowSlots → Row) :
      Common.rowLe (rows first.incoming) (rows last.incoming) ∧
        Common.rowLe (rows last.outgoing) (rows first.outgoing) := by
    have member := (instances_arrow_exact first rows (fun _ => .bottom) .top .top
      (rows first.incoming) (rows first.outgoing)).mpr
      ⟨Common.rowLe_refl _, CommonBoundCoalescing.le_top _, Common.rowLe_refl _⟩
    have found := (instances_arrow_exact last rows (fun _ => .bottom) .top .top
      (rows first.incoming) (rows first.outgoing)).mp ((same rows _ _).mp member)
    exact ⟨found.1, found.2.2⟩
  exact ⟨row_ids_equal (fun rows => (forward rows).1),
    (row_ids_equal (fun rows => (forward rows).2)).symm⟩

theorem family_transfer_equal (first : Scheme fixed rowSlots generalized) (last : Scheme fixed rowSlots other)
    (same : FamilyEquivalent first last) (captured : Fin fixed → Ty) (input : Ty) :
    Equivalent (applyTransfer first captured input) (applyTransfer last captured input) := by
  let rows : Fin rowSlots → Row := fun _ => Common.rowEmpty
  have test {n : Nat} (scheme : Scheme fixed rowSlots n) :
      Instances scheme rows captured (Common.arrow input Common.rowEmpty (applyTransfer scheme captured input)
        Common.rowEmpty) :=
    (instances_arrow_exact scheme rows captured input _ _ _).mpr
      ⟨Common.rowLe_refl _, Common.subtype_refl _, Common.rowLe_refl _⟩
  exact ⟨((instances_arrow_exact first rows captured input _ _ _).mp
    ((same rows captured _).mpr (test last))).2.1,
    ((instances_arrow_exact last rows captured input _ _ _).mp
      ((same rows captured _).mp (test first))).2.1⟩

theorem familyEquivalent_iff_transfer (first : Scheme fixed rowSlots generalized) (last : Scheme fixed rowSlots other) :
    FamilyEquivalent first last ↔ first.incoming = last.incoming ∧ first.outgoing = last.outgoing ∧
      ∀ captured input, Equivalent (applyTransfer first captured input) (applyTransfer last captured input) := by
  constructor
  · intro same
    exact ⟨(family_rows_equal first last same).1, (family_rows_equal first last same).2,
      family_transfer_equal first last same⟩
  · rintro ⟨incomingSame, outgoingSame, outputSame⟩ rows captured target
    have transport {n m : Nat} (source : Scheme fixed rowSlots n) (destination : Scheme fixed rowSlots m)
        (incoming : source.incoming = destination.incoming) (outgoing : source.outgoing = destination.outgoing)
        (transferBelow : ∀ input, Subtype (applyTransfer destination captured input)
          (applyTransfer source captured input)) :
        Instances source rows captured target → Instances destination rows captured target := by
      rintro ⟨parameters, below⟩
      refine ⟨selected destination.input (parameters source.input), Common.subtype_trans ?_ below⟩
      rw [instantiate_selected]
      apply (Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
      exact ⟨Common.subtype_refl _, by simpa only [incoming] using Common.rowLe_refl (rows destination.incoming),
        Common.subtype_trans (transferBelow _) (transfer_le_output source captured parameters _ (Common.subtype_refl _)),
        by simpa only [outgoing] using Common.rowLe_refl (rows destination.outgoing)⟩
    exact ⟨transport first last incomingSame outgoingSame (fun input => (outputSame captured input).2),
      transport last first incomingSame.symm outgoingSame.symm (fun input => (outputSame captured input).1)⟩

abbrev Code (fixed rowSlots : Nat) :=
  Fin rowSlots × Fin rowSlots × List (List (Atom (fixed + 1)))

def canonicalEncoding (scheme : Scheme fixed rowSlots generalized) : Code fixed rowSlots :=
  (scheme.incoming, scheme.outgoing, CommonCanonicalOpen.canonicalEncoding (transfer scheme))

/-- Complete computable canonicality for the whole declared arrow language.
There is no positivity condition, same-arity condition or supplied replacement.
Shared negative/positive occurrences of the selected input remain correlated. -/
theorem canonicalEncoding_exact (first : Scheme fixed rowSlots generalized) (last : Scheme fixed rowSlots other) :
    FamilyEquivalent first last ↔ canonicalEncoding first = canonicalEncoding last := by
  rw [familyEquivalent_iff_transfer]
  simp only [canonicalEncoding, Prod.mk.injEq]
  rw [← CommonCanonicalOpen.canonicalEncoding_exact]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro same parameters
    have reconstruction : Fin.lastCases (parameters (Fin.last fixed))
        (fun index => parameters index.castSucc) = parameters := by
      funext index
      refine Fin.lastCases ?_ (fun index => ?_) index <;> simp
    simpa only [applyTransfer, reconstruction] using
      same (fun index => parameters index.castSucc) (parameters (Fin.last fixed))
  · intro same captured input
    exact same (Fin.lastCases input captured)

end Yulang.CommonCanonicalArrowFamilies
