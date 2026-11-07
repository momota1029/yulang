import Yulang.CommonCanonicalCurriedTransfer

/-!
# Complete codes for a fixed finite curried-arrow depth

All schemes compared here have the same arbitrary number of curried
arguments. Their generalized parameter counts, input-sharing patterns and
scalar results may differ freely. Fixed captured identities and each
argument's incoming/outgoing row identities remain observable.

The simultaneous transfer code completely characterizes the full subtype
instance family, including targets that are not written as an arrow spine.
The proof constructs witnesses by finite unions of required input types;
there is no candidate-reparameterization premise or semantic search oracle.

Comparisons between different arrow depths, nonvariable domain syntax,
constructor results, generalized rows, role obligations and arbitrary public
interfaces are not claimed by this fixed-depth theorem.
-/

namespace Yulang.CommonCanonicalCurriedFamilies

open Common (Ty Row Subtype Equivalent)
open ProducerCanonicalOpen (Atom)
open CommonCanonicalCurriedTransfer

variable {fixed rowSlots arguments generalized other : Nat}

def FamilyEquivalent (first : Scheme fixed rowSlots arguments generalized)
    (last : Scheme fixed rowSlots arguments other) : Prop :=
  ∀ rows : Fin rowSlots → Row, ∀ captured : Fin fixed → Ty, ∀ target : Ty,
    Instances first rows captured target ↔ Instances last rows captured target

private theorem row_ids_equal {first last : Fin rowSlots}
    (below : ∀ rows : Fin rowSlots → Row, Common.rowLe (rows first) (rows last)) : first = last :=
  (below (fun index _ => index = first) (0, []) rfl).symm

theorem family_rows_equal (first : Scheme fixed rowSlots arguments generalized)
    (last : Scheme fixed rowSlots arguments other) (same : FamilyEquivalent first last) :
    first.incoming = last.incoming ∧ first.outgoing = last.outgoing := by
  have forward (rows : Fin rowSlots → Row) (position : Fin arguments) :
      Common.rowLe (rows (first.incoming position)) (rows (last.incoming position)) ∧
        Common.rowLe (rows (last.outgoing position)) (rows (first.outgoing position)) := by
    have member := (instances_spine_exact first rows (fun _ => .bottom) (fun _ => .top)
      (fun index => rows (first.incoming index)) (fun index => rows (first.outgoing index)) .top).mpr
      ⟨fun _ => ⟨Common.rowLe_refl _, Common.rowLe_refl _⟩, CommonBoundCoalescing.le_top _⟩
    exact ((instances_spine_exact last rows _ _ _ _ _).mp ((same rows _ _).mp member)).1 position
  constructor
  · funext position
    exact row_ids_equal (fun rows => (forward rows position).1)
  · funext position
    exact (row_ids_equal (fun rows => (forward rows position).2)).symm

theorem family_transfer_equal (first : Scheme fixed rowSlots arguments generalized)
    (last : Scheme fixed rowSlots arguments other) (same : FamilyEquivalent first last)
    (captured : Fin fixed → Ty) (inputs : Fin arguments → Ty) :
    Equivalent (applyTransfer first captured inputs) (applyTransfer last captured inputs) := by
  let rows : Fin rowSlots → Row := fun _ => Common.rowEmpty
  have test {n : Nat} (scheme : Scheme fixed rowSlots arguments n) :
      Instances scheme rows captured (spine arguments inputs (fun _ => Common.rowEmpty)
        (fun _ => Common.rowEmpty) (applyTransfer scheme captured inputs)) :=
    (instances_spine_exact scheme rows captured inputs _ _ _).mpr
      ⟨fun _ => ⟨Common.rowLe_refl _, Common.rowLe_refl _⟩, Common.subtype_refl _⟩
  exact ⟨((instances_spine_exact first rows captured inputs _ _ _).mp
    ((same rows captured _).mpr (test last))).2,
    ((instances_spine_exact last rows captured inputs _ _ _).mp
      ((same rows captured _).mp (test first))).2⟩

theorem familyEquivalent_iff_transfer (first : Scheme fixed rowSlots arguments generalized)
    (last : Scheme fixed rowSlots arguments other) :
    FamilyEquivalent first last ↔ first.incoming = last.incoming ∧ first.outgoing = last.outgoing ∧
      ∀ captured inputs, Equivalent (applyTransfer first captured inputs) (applyTransfer last captured inputs) := by
  constructor
  · intro same
    exact ⟨(family_rows_equal first last same).1, (family_rows_equal first last same).2,
      family_transfer_equal first last same⟩
  · rintro ⟨incomingSame, outgoingSame, outputSame⟩ rows captured target
    have transport {n m : Nat} (source : Scheme fixed rowSlots arguments n) (destination : Scheme fixed rowSlots arguments m)
        (incoming : source.incoming = destination.incoming) (outgoing : source.outgoing = destination.outgoing)
        (transferBelow : ∀ inputs, Subtype (applyTransfer destination captured inputs)
          (applyTransfer source captured inputs)) :
        Instances source rows captured target → Instances destination rows captured target := by
      rintro ⟨parameters, below⟩
      let inputs : Fin arguments → Ty := fun position => parameters (source.input position)
      refine ⟨selected destination inputs, Common.subtype_trans ?_ below⟩
      apply (spine_below_iff _ _ _ _ _ _ _ _ _).mpr
      constructor
      · intro position
        exact ⟨input_le_selected destination inputs position,
          by simpa only [incoming] using Common.rowLe_refl (rows (destination.incoming position)),
          by simpa only [outgoing] using Common.rowLe_refl (rows (destination.outgoing position))⟩
      · rw [← applyTransfer_eq]
        exact Common.subtype_trans (transferBelow inputs)
          (transfer_le_output source captured inputs parameters (fun _ => Common.subtype_refl _))
    exact ⟨transport first last incomingSame outgoingSame (fun inputs => (outputSame captured inputs).2),
      transport last first incomingSame.symm outgoingSame.symm (fun inputs => (outputSame captured inputs).1)⟩

private theorem ofFn_eq_iff (first last : Fin n → α) : List.ofFn first = List.ofFn last ↔ first = last := by
  constructor
  · intro same
    funext index
    have observed := congrArg (fun values => values[index.val]?) same
    simpa [List.getElem?_ofFn, index.isLt] using observed
  · exact congrArg List.ofFn

abbrev Code (fixed rowSlots arguments : Nat) :=
  List (Fin rowSlots) × List (Fin rowSlots) × List (List (Atom (fixed + arguments)))

def canonicalEncoding (scheme : Scheme fixed rowSlots arguments generalized) : Code fixed rowSlots arguments :=
  (List.ofFn scheme.incoming, List.ofFn scheme.outgoing, CommonCanonicalOpen.canonicalEncoding (transfer scheme))

/-- For every fixed finite arrow depth, every captured/row context and any
two local arities, this is a complete computed code for the existing common
subtype-instance family. All sharing patterns are allowed by the grammar. -/
theorem canonicalEncoding_exact (first : Scheme fixed rowSlots arguments generalized)
    (last : Scheme fixed rowSlots arguments other) :
    FamilyEquivalent first last ↔ canonicalEncoding first = canonicalEncoding last := by
  rw [familyEquivalent_iff_transfer]
  simp only [canonicalEncoding, Prod.mk.injEq, ofFn_eq_iff]
  rw [← CommonCanonicalOpen.canonicalEncoding_exact]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro same parameters
    have reconstruction : Fin.addCases (fun index => parameters (index.castAdd arguments))
        (fun index => parameters (Fin.natAdd fixed index)) = parameters := by
      funext index
      refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;> simp
    simpa only [applyTransfer, reconstruction] using
      same (fun index => parameters (index.castAdd arguments)) (fun index => parameters (Fin.natAdd fixed index))
  · intro same captured inputs
    exact same (Fin.addCases captured inputs)

namespace Examples

/-- `forall a, a -> a -> a`, with all four arrow rows sharing one fixed ID. -/
def shared : Scheme 0 1 2 1 := ⟨fun _ => 0, fun _ => 0, fun _ => 0, .atom (.var 0)⟩

/-- `forall a b, a -> b -> a | b`, in the same fixed row context. -/
def joined : Scheme 0 1 2 2 :=
  ⟨fun _ => 0, fun _ => 0, id, .union (.atom (.var 0)) (.atom (.var 1))⟩

/-- `forall a b, a -> b -> a`: the second input no longer reaches the result. -/
def firstOnly : Scheme 0 1 2 2 := ⟨fun _ => 0, fun _ => 0, id, .atom (.var 0)⟩

theorem shared_joined_code : canonicalEncoding shared = canonicalEncoding joined := by decide +kernel

theorem shared_joined_instances : FamilyEquivalent shared joined :=
  (canonicalEncoding_exact shared joined).mpr shared_joined_code

theorem second_argument_sharing_matters : ¬ FamilyEquivalent shared firstOnly := by
  intro same
  have code := (canonicalEncoding_exact shared firstOnly).mp same
  have different : canonicalEncoding shared ≠ canonicalEncoding firstOnly := by decide +kernel
  exact different code

end Examples

end Yulang.CommonCanonicalCurriedFamilies
