import Yulang.RigidRecordDemands
import Yulang.RigidRecordLatticeCheck

/-!
# Executable first-field demands

The source is traversed directly, without asking the structural comparison
layer to compare an equally deep tail against a whole demanded spine.
Only visible field payload comparisons call the preceding depth layer.
-/

namespace Yulang.RigidRecordDemandCheck

open StructuralBase (Ty IsRecord)
open RigidSemanticRecords (Subtype)
open RigidRecordFields (erase erase_record lookup_erase)
open RigidRecordDemands (Fits)
open RigidRecordLatticeCheck (depth)

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

def emptyCheck : Ty Row → Bool
  | .emptyRecord => true
  | _ => false

def headCheck (compare : Ty Row → Ty Row → Bool) (label : Nat) (value target : Ty Row) : Bool :=
  match target.lookup label with
  | none => true
  | some expected => compare value expected

def check (compare : Ty Row → Ty Row → Bool) : Ty Row → Ty Row → Bool
  | .bottom, _ => true
  | .top, _ => false
  | .union left right, target => check compare left target && check compare right target
  | .inter left right, target => check compare left target || check compare right target
  | .emptyRecord, target => emptyCheck target
  | .record label value rest, target =>
      headCheck compare label value target && check compare rest (erase label target)
  | _, _ => false

theorem emptyCheck_iff {target : Ty Row} (rigid : IsRecord target) :
    emptyCheck target = true ↔ Fits leRow .emptyRecord target := by
  cases rigid with
  | empty => simp [emptyCheck, Fits, Ty.lookup]
  | @field rest label value _ =>
      constructor
      · intro impossible; cases impossible
      · intro fits
        exact False.elim (fits label value (by simp [Ty.lookup]))

theorem headCheck_sound (compare : Ty Row → Ty Row → Bool)
    (sound : ∀ a b, compare a b = true → Subtype leRow a b)
    {label : Nat} {value target : Ty Row} (accepted : headCheck compare label value target = true) :
    ∀ expected, target.lookup label = some expected → Subtype leRow value expected := by
  intro expected found
  exact sound value expected (by simpa [headCheck, found] using accepted)

theorem check_fits (compare : Ty Row → Ty Row → Bool)
    (sound : ∀ a b, compare a b = true → Subtype leRow a b)
    {source target : Ty Row} (rigid : IsRecord target)
    (accepted : check compare source target = true) : Fits leRow source target := by
  induction source generalizing target with
  | bottom => trivial
  | top | base | pair | variant | arrow => cases accepted
  | union left right first last =>
      exact ⟨first rigid (Bool.and_eq_true_iff.mp accepted).1,
        last rigid (Bool.and_eq_true_iff.mp accepted).2⟩
  | inter left right first last =>
      simp only [check, Bool.or_eq_true] at accepted
      exact accepted.elim
        (fun proof => Or.inl (first rigid proof)) (fun proof => Or.inr (last rigid proof))
  | emptyRecord => exact (emptyCheck_iff rigid).mp accepted
  | record label value rest _ tail =>
      exact ⟨headCheck_sound compare sound (Bool.and_eq_true_iff.mp accepted).1,
        tail (erase_record label rigid) (Bool.and_eq_true_iff.mp accepted).2⟩

theorem check_sound (compare : Ty Row → Ty Row → Bool)
    (sound : ∀ a b, compare a b = true → Subtype leRow a b)
    {source target : Ty Row} (rigid : IsRecord target)
    (accepted : check compare source target = true) : Subtype leRow source target :=
  RigidRecordDemands.fits_sound rigid (check_fits compare sound rigid accepted)

theorem erase_depth (label : Nat) (type : Ty Row) : depth (erase label type) ≤ depth type := by
  induction type with
  | record name value rest _ ih =>
      by_cases same : label = name
      · subst name
        simp only [erase, ↓reduceIte, depth]
        omega
      · simp only [erase, same, ↓reduceIte, depth]
        omega
  | _ => exact Nat.le_refl _

theorem field_depth {type value : Ty Row} {label : Nat} (found : type.lookup label = some value) :
    depth value < depth type := by
  induction type with
  | record name head tail _ ih =>
      by_cases same : label = name
      · simp [Ty.lookup, same] at found
        subst value
        simp only [depth]
        omega
      · have rest : tail.lookup label = some value := by simpa [Ty.lookup, same] using found
        have smaller := ih rest
        simp only [depth]
        omega
  | _ => simp [Ty.lookup] at found

theorem fits_checked (compare : Ty Row → Ty Row → Bool)
    (complete : ∀ a b, depth a ≤ bound → depth b ≤ bound →
      Subtype leRow a b → compare a b = true)
    {source target : Ty Row} (rigid : IsRecord target)
    (sourceBound : depth source ≤ bound + 1) (targetBound : depth target ≤ bound + 1)
    (fits : Fits leRow source target) : check compare source target = true := by
  induction source generalizing target with
  | bottom => rfl
  | top | base | pair | variant | arrow => cases fits
  | union left right first last =>
      have leftBound : depth left ≤ bound + 1 := Nat.le_trans (Nat.le_max_left _ _) sourceBound
      have rightBound : depth right ≤ bound + 1 := Nat.le_trans (Nat.le_max_right _ _) sourceBound
      exact Bool.and_eq_true_iff.mpr
        ⟨first rigid leftBound targetBound fits.1, last rigid rightBound targetBound fits.2⟩
  | inter left right first last =>
      simp only [check, Bool.or_eq_true]
      rcases fits with fits | fits
      · exact Or.inl (first rigid (Nat.le_trans (Nat.le_max_left _ _) sourceBound) targetBound fits)
      · exact Or.inr (last rigid (Nat.le_trans (Nat.le_max_right _ _) sourceBound) targetBound fits)
  | emptyRecord => exact (emptyCheck_iff rigid).mpr fits
  | record label value rest _ tail =>
      apply Bool.and_eq_true_iff.mpr
      constructor
      · cases found : target.lookup label with
        | none => simp [headCheck, found]
        | some expected =>
            have expectedDepth := field_depth found
            have valueBound : depth value ≤ bound := by simp only [depth] at sourceBound; omega
            simpa [headCheck, found] using
              complete value expected valueBound (by omega) (fits.1 expected found)
      · have restBound : depth rest ≤ bound + 1 := by simp only [depth] at sourceBound; omega
        exact tail (erase_record label rigid) restBound
          (Nat.le_trans (erase_depth label target) targetBound) fits.2

theorem check_complete (compare : Ty Row → Ty Row → Bool)
    (complete : ∀ a b, depth a ≤ bound → depth b ≤ bound →
      Subtype leRow a b → compare a b = true)
    {source target : Ty Row} (rigid : IsRecord target)
    (sourceBound : depth source ≤ bound + 1) (targetBound : depth target ≤ bound + 1)
    (below : Subtype leRow source target) : check compare source target = true :=
  fits_checked compare complete rigid sourceBound targetBound
    ((RigidRecordDemands.subtype_iff_fits source rigid).mp below)

end Yulang.RigidRecordDemandCheck
