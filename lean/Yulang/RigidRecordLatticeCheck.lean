import Yulang.RigidRecordAtomNormal

/-!
# Finite lattice checking with bounded structural atom comparisons

This layer reuses the existing cut-free lattice checker on an explicit
encoding. The supplied atom function is a finite computation. Its soundness
and bounded completeness are the precise obligations discharged by the
constructor-depth recursion in the ground semantic record checker.
-/

namespace Yulang.RigidRecordLatticeCheck

open StructuralBase (Ty IsRecord)
open RigidSemanticRecords (Subtype Equivalent)
open RigidRecordAtoms (Atomic encode decode rows)

universe u

variable {Row : Type u} {leRow : Row → Row → Prop}

/-- Lattice connectives do not increase structural depth. -/
def depth : Ty Row → Nat
  | .base _ | .bottom | .top | .emptyRecord => 0
  | .union a b | .inter a b => max (depth a) (depth b)
  | .pair a b | .record _ a b | .arrow a _ b _ => max (depth a) (depth b) + 1
  | .variant _ a => depth a + 1

def rowCheck (atoms : Ty Row → Ty Row → Bool) : Option (Ty Row) → Option (Ty Row) → Bool
  | none, none => true
  | some a, some b => atoms a b
  | _, _ => false

def check [DecidableEq Row] (atoms : Ty Row → Ty Row → Bool) (source target : Ty Row) : Bool :=
  StructuralDecisions.check (rowCheck atoms) (encode source) (encode target)

theorem decode_subtype
    (relation : Option (Ty Row) → Option (Ty Row) → Prop)
    (rowSound : ∀ a b, relation a b → Subtype leRow (a.getD .bottom) (b.getD .bottom))
    {a b : Ty (Option (Ty Row))} (subtype : StructuralBase.Subtype relation a b) :
    Subtype leRow (decode a) (decode b) := by
  induction subtype with
  | refl => exact .refl _
  | trans _ _ first last => exact .trans first last
  | bottom => exact .bottom _
  | top => exact .top _
  | unionLeft => exact .unionLeft _ _
  | unionRight => exact .unionRight _ _
  | unionElim _ _ first last => exact .unionElim first last
  | interLeft => exact .interLeft _ _
  | interRight => exact .interRight _ _
  | interIntro _ _ first last => exact .interIntro first last
  | pair => exact .refl _
  | variant => exact .refl _
  | arrow _ _ _ outputRows => exact rowSound _ _ outputRows
  | record source target =>
      rw [RigidRecordAtoms.decode_record source, RigidRecordAtoms.decode_record target]
      exact .refl _

theorem check_sound [DecidableEq Row] (atoms : Ty Row → Ty Row → Bool)
    (atomSound : ∀ a b, atoms a b = true → Subtype leRow a b)
    {source target : Ty Row} (accepted : check atoms source target = true) :
    Subtype leRow source target := by
  have comparison := StructuralDecisions.check_sound (rowCheck atoms) (fun _ _ => Iff.rfl) accepted
  have sound := decode_subtype (leRow := leRow) (fun a b => rowCheck atoms a b = true)
    (fun a b checked => by
      cases a <;> cases b <;> simp_all [rowCheck]
      exact .refl _) comparison.sound
  simpa using sound

inductive Encoded (bound : Nat) : Ty (Option (Ty Row)) → Prop where
  | bottom : Encoded bound .bottom
  | top : Encoded bound .top
  | union : Encoded bound a → Encoded bound b → Encoded bound (.union a b)
  | inter : Encoded bound a → Encoded bound b → Encoded bound (.inter a b)
  | atom : Atomic a → depth a ≤ bound →
      Encoded bound (.arrow .bottom none .bottom (some a))

theorem encode_bounded (type : Ty Row) (bounded : depth type ≤ bound) : Encoded bound (encode type) := by
  induction type with
  | bottom => exact .bottom
  | top => exact .top
  | union a b first last =>
      exact .union (first (Nat.le_trans (Nat.le_max_left _ _) bounded))
        (last (Nat.le_trans (Nat.le_max_right _ _) bounded))
  | inter a b first last =>
      exact .inter (first (Nat.le_trans (Nat.le_max_left _ _) bounded))
        (last (Nat.le_trans (Nat.le_max_right _ _) bounded))
  | _ => exact .atom trivial bounded

theorem Encoded.not_record {type : Ty (Option (Ty Row))} (bounded : Encoded bound type) :
    ¬ IsRecord type := by
  cases bounded <;> intro impossible <;> cases impossible

theorem comparison_checked [DecidableEq Row] (atoms : Ty Row → Ty Row → Bool)
    (atomComplete : ∀ a b, Atomic a → Atomic b → depth a ≤ bound → depth b ≤ bound →
      Subtype leRow a b → atoms a b = true)
    {source target : Ty (Option (Ty Row))}
    (comparison : StructuralDecisions.Comparison (rows leRow) source target)
    (sourceBound : Encoded bound source) (targetBound : Encoded bound target) :
    StructuralDecisions.check (rowCheck atoms) source target = true := by
  induction comparison with
  | refl => rw [StructuralDecisions.check.eq_def]; simp
  | bottom => rw [StructuralDecisions.check.eq_def]; simp
  | top => rw [StructuralDecisions.check.eq_def]; simp
  | unionElim _ _ first last =>
      cases sourceBound with
      | union leftBound rightBound =>
          rw [StructuralDecisions.check.eq_def]
          simp [first leftBound targetBound, last rightBound targetBound]
  | interIntro _ _ first last =>
      cases targetBound with
      | inter leftBound rightBound =>
          rw [StructuralDecisions.check.eq_def]
          simp [first sourceBound leftBound, last sourceBound rightBound]
  | unionLeft _ first =>
      cases targetBound with
      | union leftBound _ =>
          rw [StructuralDecisions.check.eq_def]
          simp [first sourceBound leftBound]
  | unionRight _ last =>
      cases targetBound with
      | union _ rightBound =>
          rw [StructuralDecisions.check.eq_def]
          simp [last sourceBound rightBound]
  | interLeft _ first =>
      cases sourceBound with
      | inter leftBound _ =>
          rw [StructuralDecisions.check.eq_def]
          simp [first leftBound targetBound]
  | interRight _ last =>
      cases sourceBound with
      | inter _ rightBound =>
          rw [StructuralDecisions.check.eq_def]
          simp [last rightBound targetBound]
  | pair | variant => cases sourceBound
  | arrow _ _ _ outputRows =>
      cases sourceBound with
      | atom sourceAtom sourceDepth =>
          cases targetBound with
          | atom targetAtom targetDepth =>
              have outputChecked := atomComplete _ _ sourceAtom targetAtom sourceDepth targetDepth outputRows.sound
              have bottomChecked : StructuralDecisions.check (rowCheck atoms)
                  (Ty.bottom : Ty (Option (Ty Row))) .bottom = true := by
                rw [StructuralDecisions.check.eq_def]
                simp
              rw [StructuralDecisions.check.eq_def]
              simp [rowCheck, outputChecked, bottomChecked]
  | record sourceShape => exact False.elim (sourceBound.not_record sourceShape)

theorem check_complete [DecidableEq Row] (atoms : Ty Row → Ty Row → Bool)
    (atomComplete : ∀ a b, Atomic a → Atomic b → depth a ≤ bound → depth b ≤ bound →
      Subtype leRow a b → atoms a b = true)
    {source target : Ty Row} (sourceBound : depth source ≤ bound) (targetBound : depth target ≤ bound)
    (below : Subtype leRow source target) : check atoms source target = true :=
  comparison_checked atoms atomComplete ((RigidRecordAtoms.outer_cut_exact source target).mpr below)
    (encode_bounded source sourceBound) (encode_bounded target targetBound)

end Yulang.RigidRecordLatticeCheck
