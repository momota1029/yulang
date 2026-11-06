import Yulang.SemanticRecordLatticeCheck

/-!
# Executable ground comparison for the minimal semantic record congruence

Finite constructor-depth layers discharge all structural atom comparisons.
Each layer computes finite record views by scanning the original outer atoms.
The public entry chooses the required depth from its two input types; callers
do not supply a structural oracle, a proper-spine representative, or fuel.

The relation decided here is exactly `SemanticRecords.Subtype`. In particular
this foundational relation does not yet contain additional admissible-tail
width rules beyond the historical proper-spine rule.
-/

namespace Yulang.SemanticRecordChecker

open StructuralBase (Ty IsRecord)
open SemanticRecords (Subtype Equivalent)
open SemanticRecordAtoms (Atomic atoms)
open SemanticRecordViews (View)
open SemanticRecordLatticeCheck (depth)

universe u

variable {Row : Type u} {leRow : Row → Row → Prop}

theorem atom_depth {type atom : Ty Row} (member : atom ∈ atoms type) : depth atom ≤ depth type := by
  induction type with
  | bottom | top => cases member
  | union left right first last | inter left right first last =>
      rcases List.mem_append.mp member with member | member
      · exact Nat.le_trans (first member) (Nat.le_max_left _ _)
      · exact Nat.le_trans (last member) (Nat.le_max_right _ _)
  | _ => simp only [atoms, List.mem_singleton] at member; subst atom; exact Nat.le_refl _

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

def fieldsCheck (compare : Ty Row → Ty Row → Bool) (source target : Ty Row) : Bool :=
  (StructuralDecisions.labels target).all fun label =>
    match source.lookup label, target.lookup label with
    | some actual, some expected => compare actual expected
    | _, _ => false

theorem fieldsCheck_sound (compare : Ty Row → Ty Row → Bool)
    (sound : ∀ a b, compare a b = true → Subtype leRow a b)
    {source target : Ty Row} (sourceShape : IsRecord source) (targetShape : IsRecord target)
    (checked : fieldsCheck compare source target = true) : Subtype leRow source target := by
  apply Subtype.record sourceShape targetShape
  · intro label expected expectedFound
    have checkedField := List.all_eq_true.mp checked label
      (StructuralDecisions.lookup_mem_labels target label expected expectedFound)
    cases actualFound : source.lookup label with
    | none => simp [expectedFound, actualFound] at checkedField
    | some actual => exact ⟨actual, rfl⟩
  · intro label actual expected actualFound expectedFound
    have checkedField := List.all_eq_true.mp checked label
      (StructuralDecisions.lookup_mem_labels target label expected expectedFound)
    exact sound actual expected (by simpa [actualFound, expectedFound] using checkedField)

theorem fieldsCheck_complete (compare : Ty Row → Ty Row → Bool)
    (complete : ∀ a b, depth a ≤ bound → depth b ≤ bound →
      Subtype leRow a b → compare a b = true)
    {source target : Ty Row} (sourceShape : IsRecord source) (targetShape : IsRecord target)
    (sourceBound : depth source ≤ bound + 1) (targetBound : depth target ≤ bound + 1)
    (below : Subtype leRow source target) : fieldsCheck compare source target = true := by
  obtain ⟨width, values⟩ := SemanticRecordViews.proper_fields sourceShape targetShape below
  apply List.all_eq_true.mpr
  intro label member
  obtain ⟨expected, expectedFound⟩ := StructuralDecisions.mem_labels_has_lookup target label member
  obtain ⟨actual, actualFound⟩ := width label expected expectedFound
  have actualDepth := field_depth actualFound
  have expectedDepth := field_depth expectedFound
  simp only [actualFound, expectedFound]
  exact complete actual expected (by omega) (by omega) (values label actual expected actualFound expectedFound)

structure Layer (Row : Type u) where
  compare : Ty Row → Ty Row → Bool
  view : Ty Row → Option (Ty Row)

def atomView (previous : Ty Row → Option (Ty Row)) : Ty Row → Option (Ty Row)
  | .emptyRecord => some .emptyRecord
  | .record label value rest => (previous rest).map (Ty.record label value)
  | _ => none

def atomCheck [DecidableEq Row] (rows : Row → Row → Bool) (previous : Layer Row)
    (source target : Ty Row) : Bool :=
  decide (source = target) ||
  (match source, target with
    | .pair a b, .pair c d => previous.compare a c && previous.compare b d
    | _, _ => false) ||
  (match source, target with
    | .variant name a, .variant other b => decide (name = other) && previous.compare a b
    | _, _ => false) ||
  (match source, target with
    | .arrow a ar b br, .arrow c cr d dr =>
        previous.compare c a && rows cr ar && previous.compare b d && rows br dr
    | _, _ => false) ||
  (match source, target with
    | .record name a r, .record other b s =>
        decide (name = other) && previous.compare a b && previous.compare b a &&
          previous.compare r s && previous.compare s r
    | _, _ => false) ||
  (match atomView previous.view source, atomView previous.view target with
    | some a, some b => fieldsCheck previous.compare a b
    | _, _ => false)

def scanView (compare : Ty Row → Ty Row → Bool) (view : Ty Row → Option (Ty Row))
    (type : Ty Row) : List (Ty Row) → Option (Ty Row)
  | [] => none
  | atom :: rest =>
      match view atom with
      | none => scanView compare view type rest
      | some proper =>
          if compare type atom && compare atom type then some proper
          else scanView compare view type rest

def next [DecidableEq Row] (rows : Row → Row → Bool) (previous : Layer Row) : Layer Row :=
  let compare := SemanticRecordLatticeCheck.check (atomCheck rows previous)
  ⟨compare, fun type => scanView compare (atomView previous.view) type (atoms type)⟩

def initial [DecidableEq Row] : Layer Row :=
  ⟨fun a b => decide (a = b), fun _ => none⟩

def layers [DecidableEq Row] (rows : Row → Row → Bool) : Nat → Layer Row
  | 0 => next rows initial
  | n + 1 => next rows (layers rows n)

def check [DecidableEq Row] (rows : Row → Row → Bool) (source target : Ty Row) : Bool :=
  (layers rows (max (depth source) (depth target))).compare source target

def Sound (data : Layer Row) : Prop :=
  (∀ a b, data.compare a b = true → Subtype leRow a b) ∧
  (∀ type proper, data.view type = some proper → IsRecord proper ∧ Equivalent leRow type proper)

def CompleteAt (data : Layer Row) (bound : Nat) : Prop :=
  (∀ a b, depth a ≤ bound → depth b ≤ bound → Subtype leRow a b → data.compare a b = true) ∧
  (∀ type, depth type ≤ bound → (∃ proper, IsRecord proper ∧ Equivalent leRow type proper) →
    ∃ proper, data.view type = some proper) ∧
  (∀ type proper, depth type ≤ bound → data.view type = some proper → depth proper ≤ bound)

theorem initial_sound [DecidableEq Row] : Sound (leRow := leRow) (initial : Layer Row) := by
  constructor
  · intro a b equal
    have same : a = b := of_decide_eq_true equal
    subst b
    exact .refl _
  · intro type proper impossible
    cases impossible

theorem atomView_sound (previous : Ty Row → Option (Ty Row))
    (viewSound : ∀ type proper, previous type = some proper → IsRecord proper ∧ Equivalent leRow type proper)
    {type proper : Ty Row} (found : atomView previous type = some proper) :
    IsRecord proper ∧ Equivalent leRow type proper := by
  cases type with
  | emptyRecord => cases found; exact ⟨.empty, .refl _⟩
  | record label value rest =>
      cases previousFound : previous rest with
      | none => simp [atomView, previousFound] at found
      | some tail =>
          have equal : Ty.record label value tail = proper := by simpa [atomView, previousFound] using found
          subst proper
          obtain ⟨shape, same⟩ := viewSound rest tail previousFound
          exact ⟨.field shape, SemanticRecords.record_congr label (.refl _) same⟩
  | _ => cases found

theorem atomCheck_sound [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b) (previous : Layer Row) (sound : Sound (leRow := leRow) previous)
    {source target : Ty Row} (accepted : atomCheck rows previous source target = true) :
    Subtype leRow source target := by
  simp only [atomCheck, Bool.or_eq_true, or_assoc] at accepted
  rcases accepted with same | pair | variant | arrow | congr | record
  · have equal := of_decide_eq_true same
    subst target
    exact .refl _
  · split at pair
    · exact .pair (sound.1 _ _ (Bool.and_eq_true_iff.mp pair).1) (sound.1 _ _ (Bool.and_eq_true_iff.mp pair).2)
    · cases pair
  · split at variant
    · obtain ⟨label, value⟩ := Bool.and_eq_true_iff.mp variant
      have sameLabel := of_decide_eq_true label
      subst_vars
      exact .variant (sound.1 _ _ value)
    · cases variant
  · split at arrow
    · simp only [Bool.and_eq_true_iff] at arrow
      exact .arrow (sound.1 _ _ arrow.1.1.1) ((rowExact _ _).mp arrow.1.1.2)
        (sound.1 _ _ arrow.1.2) ((rowExact _ _).mp arrow.2)
    · cases arrow
  · split at congr
    · simp only [Bool.and_eq_true_iff] at congr
      have sameLabel := of_decide_eq_true congr.1.1.1.1
      subst_vars
      exact .recordCongr (sound.1 _ _ congr.1.1.1.2) (sound.1 _ _ congr.1.1.2)
        (sound.1 _ _ congr.1.2) (sound.1 _ _ congr.2)
    · cases congr
  · split at record
    · rename_i a b sourceFound targetFound
      obtain ⟨sourceShape, sourceEq⟩ := atomView_sound previous.view sound.2 sourceFound
      obtain ⟨targetShape, targetEq⟩ := atomView_sound previous.view sound.2 targetFound
      exact .trans sourceEq.1 (.trans (fieldsCheck_sound previous.compare sound.1 sourceShape targetShape record) targetEq.2)
    · cases record

theorem scanView_result (compare : Ty Row → Ty Row → Bool) (view : Ty Row → Option (Ty Row))
    (type : Ty Row) (choices : List (Ty Row)) {proper : Ty Row}
    (found : scanView compare view type choices = some proper) :
    ∃ atom ∈ choices, view atom = some proper ∧ compare type atom = true ∧ compare atom type = true := by
  induction choices with
  | nil => cases found
  | cons atom rest ih =>
      cases viewed : view atom with
      | none =>
          obtain ⟨other, member, accepted⟩ := ih (by simpa [scanView, viewed] using found)
          exact ⟨other, List.mem_cons_of_mem _ member, accepted⟩
      | some value =>
          cases accepted : compare type atom && compare atom type with
          | false =>
              obtain ⟨other, member, checked⟩ := ih (by simpa [scanView, viewed, accepted] using found)
              exact ⟨other, List.mem_cons_of_mem _ member, checked⟩
          | true =>
              have equal : value = proper := by simpa [scanView, viewed, accepted] using found
              subst proper
              exact ⟨atom, List.mem_cons_self, viewed, (Bool.and_eq_true_iff.mp accepted).1, (Bool.and_eq_true_iff.mp accepted).2⟩

theorem next_sound [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b) (previous : Layer Row) (sound : Sound (leRow := leRow) previous) :
    Sound (leRow := leRow) (next rows previous) := by
  have checked : ∀ {a b : Ty Row},
      SemanticRecordLatticeCheck.check (atomCheck rows previous) a b = true → Subtype leRow a b := by
    intro a b accepted
    exact SemanticRecordLatticeCheck.check_sound (atomCheck rows previous)
      (fun _ _ accepted => atomCheck_sound rows rowExact previous sound accepted) accepted
  constructor
  · exact fun _ _ accepted => checked accepted
  · intro type proper found
    obtain ⟨atom, _, viewed, forward, backward⟩ := scanView_result _ _ _ _ found
    obtain ⟨shape, equivalent⟩ := atomView_sound previous.view sound.2 viewed
    exact ⟨shape, (show Equivalent leRow type atom from ⟨checked forward, checked backward⟩).trans equivalent⟩

theorem atomView_complete (previous : Layer Row) (complete : CompleteAt (leRow := leRow) previous bound)
    {type : Ty Row} {fields : SemanticRecordViews.Fields Row}
    (bounded : depth type ≤ bound + 1) (view : View leRow type fields) :
    ∃ proper, atomView previous.view type = some proper := by
  cases view with
  | empty => exact ⟨.emptyRecord, rfl⟩
  | @field rest tail label value equivalent =>
      have restBound : depth rest ≤ bound := by simp only [depth] at bounded; omega
      obtain ⟨proper, found⟩ := complete.2.1 rest restBound
        ⟨_, SemanticRecordViews.spine_record tail, equivalent⟩
      exact ⟨.record label value proper, by simp [atomView, found]⟩

theorem atomView_bounded (previous : Layer Row) (complete : CompleteAt (leRow := leRow) previous bound)
    {type proper : Ty Row} (bounded : depth type ≤ bound + 1)
    (found : atomView previous.view type = some proper) : depth proper ≤ bound + 1 := by
  cases type with
  | emptyRecord => cases found; simp [depth]
  | record label value rest =>
      cases previousFound : previous.view rest with
      | none => simp [atomView, previousFound] at found
      | some tail =>
          have equal : Ty.record label value tail = proper := by simpa [atomView, previousFound] using found
          subst proper
          have restBound : depth rest ≤ bound := by simp only [depth] at bounded; omega
          have tailBound := complete.2.2 rest tail restBound previousFound
          simp only [depth] at bounded ⊢
          omega
  | _ => cases found

theorem atomic_view_of_equivalent {type proper : Ty Row} (atom : Atomic type)
    (shape : IsRecord proper) (same : Equivalent leRow type proper) :
    ∃ fields, View leRow type fields := by
  have chain := (SemanticRecordAtoms.atomic_iff_chain atom (SemanticRecordAtoms.isRecord_atomic shape)).mp same.1
  exact (SemanticRecordViews.Chain.view_iff chain).mpr (SemanticRecordViews.record_has_view shape)

theorem atomCheck_complete [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (previous : Layer Row) (sound : Sound (leRow := leRow) previous)
    (complete : CompleteAt (leRow := leRow) previous bound)
    {source target : Ty Row} (sourceAtom : Atomic source) (targetAtom : Atomic target)
    (sourceBound : depth source ≤ bound + 1) (targetBound : depth target ≤ bound + 1)
    (below : Subtype leRow source target) : atomCheck rows previous source target = true := by
  have chain := (SemanticRecordAtoms.atomic_iff_chain sourceAtom targetAtom).mp below
  have shape := SemanticRecordAtomNormal.Chain.shape rowRefl rowTrans chain
  cases shape with
  | base => simp [atomCheck]
  | @pair a c b d first last =>
      have ac := complete.1 a c (by simp only [depth] at sourceBound; omega)
        (by simp only [depth] at targetBound; omega) first
      have bd := complete.1 b d (by simp only [depth] at sourceBound; omega)
        (by simp only [depth] at targetBound; omega) last
      simp [atomCheck, ac, bd]
  | @variant a b label payload =>
      have checked := complete.1 a b (by simp only [depth] at sourceBound; omega)
        (by simp only [depth] at targetBound; omega) payload
      simp [atomCheck, checked]
  | @arrow input input' inputRow inputRow' output output' outputRow outputRow' before beforeRow after afterRow =>
      have inputChecked := complete.1 input input' (by simp only [depth] at targetBound; omega)
        (by simp only [depth] at sourceBound; omega) before
      have outputChecked := complete.1 output output' (by simp only [depth] at sourceBound; omega)
        (by simp only [depth] at targetBound; omega) after
      simp [atomCheck, inputChecked, outputChecked, (rowExact _ _).mpr beforeRow, (rowExact _ _).mpr afterRow]
  | records sourceRecord targetRecord =>
      cases sourceFound : atomView previous.view source with
      | some left =>
          obtain ⟨sourceShape, sourceEq⟩ := atomView_sound previous.view sound.2 sourceFound
          have sourceView := atomic_view_of_equivalent sourceAtom sourceShape sourceEq
          obtain ⟨fields, targetView⟩ := (SemanticRecordViews.Chain.view_iff chain).mp sourceView
          obtain ⟨right, targetFound⟩ := atomView_complete previous complete targetBound targetView
          obtain ⟨targetShape, targetEq⟩ := atomView_sound previous.view sound.2 targetFound
          have fieldsBelow := Subtype.trans sourceEq.2 (Subtype.trans below targetEq.1)
          have checked := fieldsCheck_complete previous.compare complete.1 sourceShape targetShape
            (atomView_bounded previous complete sourceBound sourceFound)
            (atomView_bounded previous complete targetBound targetFound) fieldsBelow
          simp [atomCheck, sourceFound, targetFound, checked]
      | none =>
          have noView : ¬ ∃ fields, View leRow source fields := by
            rintro ⟨fields, view⟩
            obtain ⟨proper, found⟩ := atomView_complete previous complete sourceBound view
            rw [sourceFound] at found
            cases found
          have sourceRaw : SemanticRecordAtomNormal.RawRecord source := by
            cases source with
            | emptyRecord => simp [atomView] at sourceFound
            | record => trivial
            | _ => cases sourceRecord
          have same := SemanticRecordAtomNormal.Chain.opaque chain sourceRaw noView
          cases same with
          | @field a b r s label head tail =>
              have aBound : depth a ≤ bound := by simp only [depth] at sourceBound; omega
              have bBound : depth b ≤ bound := by simp only [depth] at targetBound; omega
              have rBound : depth r ≤ bound := by simp only [depth] at sourceBound; omega
              have sBound : depth s ≤ bound := by simp only [depth] at targetBound; omega
              simp [atomCheck, complete.1 a b aBound bBound head.1, complete.1 b a bBound aBound head.2,
                complete.1 r s rBound sBound tail.1, complete.1 s r sBound rBound tail.2]

theorem scanView_exists (compare : Ty Row → Ty Row → Bool) (view : Ty Row → Option (Ty Row))
    (type : Ty Row) (choices : List (Ty Row)) {atom proper : Ty Row}
    (member : atom ∈ choices) (viewed : view atom = some proper)
    (forward : compare type atom = true) (backward : compare atom type = true) :
    ∃ result, scanView compare view type choices = some result := by
  induction choices with
  | nil => cases member
  | cons head rest ih =>
      cases headViewed : view head with
      | none =>
          have inside : atom ∈ rest := by
            rcases List.mem_cons.mp member with same | inside
            · subst head; rw [headViewed] at viewed; cases viewed
            · exact inside
          obtain ⟨result, found⟩ := ih inside
          exact ⟨result, by simpa [scanView, headViewed] using found⟩
      | some value =>
          cases checked : compare type head && compare head type with
          | true => exact ⟨value, by simp [scanView, headViewed, checked]⟩
          | false =>
              have inside : atom ∈ rest := by
                rcases List.mem_cons.mp member with same | inside
                · subst head; simp [forward, backward] at checked
                · exact inside
              obtain ⟨result, found⟩ := ih inside
              exact ⟨result, by simpa [scanView, headViewed, checked] using found⟩

theorem next_complete_aux [DecidableEq Row] (rows : Row → Row → Bool) (previous : Layer Row)
    (atomComplete : ∀ a b, Atomic a → Atomic b → depth a ≤ bound → depth b ≤ bound →
      Subtype leRow a b → atomCheck rows previous a b = true)
    (viewComplete : ∀ type fields, depth type ≤ bound → View leRow type fields →
      ∃ proper, atomView previous.view type = some proper)
    (viewBounded : ∀ type proper, depth type ≤ bound → atomView previous.view type = some proper →
      depth proper ≤ bound) : CompleteAt (leRow := leRow) (next rows previous) bound := by
  have comparison : ∀ {a b : Ty Row}, depth a ≤ bound → depth b ≤ bound →
      Subtype leRow a b → SemanticRecordLatticeCheck.check (atomCheck rows previous) a b = true := by
    intro a b aBound bBound below
    exact SemanticRecordLatticeCheck.check_complete (atomCheck rows previous) atomComplete aBound bBound below
  refine ⟨fun _ _ aBound bBound below => comparison aBound bBound below, ?_, ?_⟩
  · intro type bounded witness
    obtain ⟨proper, shape, equivalent⟩ := witness
    obtain ⟨atom, member, ⟨fields, view⟩, same⟩ := SemanticRecordViews.equivalent_proper_atom shape equivalent
    have atomBound := Nat.le_trans (atom_depth member) bounded
    obtain ⟨viewed, found⟩ := viewComplete atom fields atomBound view
    exact scanView_exists _ _ _ _ member found
      (comparison bounded atomBound same.1) (comparison atomBound bounded same.2)
  · intro type proper bounded found
    obtain ⟨atom, member, viewed, _, _⟩ := scanView_result _ _ _ _ found
    exact viewBounded atom proper (Nat.le_trans (atom_depth member) bounded) viewed

theorem next_complete [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (previous : Layer Row) (sound : Sound (leRow := leRow) previous)
    (complete : CompleteAt (leRow := leRow) previous bound) :
    CompleteAt (leRow := leRow) (next rows previous) (bound + 1) :=
  next_complete_aux rows previous
    (fun _ _ aAtom bAtom aBound bBound below =>
      atomCheck_complete rows rowExact rowRefl rowTrans previous sound complete aAtom bAtom aBound bBound below)
    (fun _ _ bounded view => atomView_complete previous complete bounded view)
    (fun _ _ bounded found => atomView_bounded previous complete bounded found)

theorem atomCheck_zero [DecidableEq Row] (rows : Row → Row → Bool) (previous : Layer Row)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {source target : Ty Row} (sourceAtom : Atomic source) (targetAtom : Atomic target)
    (sourceBound : depth source ≤ 0) (targetBound : depth target ≤ 0)
    (below : Subtype leRow source target) : atomCheck rows previous source target = true := by
  have chain := (SemanticRecordAtoms.atomic_iff_chain sourceAtom targetAtom).mp below
  have shape := SemanticRecordAtomNormal.Chain.shape rowRefl rowTrans chain
  cases shape with
  | base => simp [atomCheck]
  | pair | variant | arrow => simp only [depth] at sourceBound; omega
  | records sourceRecord targetRecord =>
      cases source with
      | record => simp only [depth] at sourceBound; omega
      | emptyRecord =>
          cases target with
          | record => simp only [depth] at targetBound; omega
          | emptyRecord => simp [atomCheck]
          | _ => cases targetRecord
      | _ => cases sourceRecord

theorem first_complete [DecidableEq Row] (rows : Row → Row → Bool)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c) :
    CompleteAt (leRow := leRow) (next rows initial) 0 := by
  apply next_complete_aux rows initial
  · exact fun _ _ aAtom bAtom aBound bBound below =>
      atomCheck_zero rows initial rowRefl rowTrans aAtom bAtom aBound bBound below
  · intro type fields bounded view
    cases view with
    | empty => exact ⟨.emptyRecord, rfl⟩
    | field => simp only [depth] at bounded; omega
  · intro type proper bounded found
    cases type with
    | emptyRecord => cases found; exact Nat.le_refl 0
    | record => simp [atomView, initial] at found
    | _ => cases found

theorem layers_sound [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b) (bound : Nat) :
    Sound (leRow := leRow) (layers rows bound) := by
  induction bound with
  | zero => exact next_sound rows rowExact initial initial_sound
  | succ bound ih => exact next_sound rows rowExact (layers rows bound) ih

theorem layers_complete [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c) (bound : Nat) :
    CompleteAt (leRow := leRow) (layers rows bound) bound := by
  induction bound with
  | zero => exact first_complete rows rowRefl rowTrans
  | succ bound ih =>
      exact next_complete rows rowExact rowRefl rowTrans (layers rows bound)
        (layers_sound rows rowExact bound) ih

/-- Exact executable ground comparison. Row reflexivity and transitivity,
and the exactness of the supplied row checker, are the only semantic
assumptions. The two finite input types are otherwise arbitrary. -/
theorem check_true_iff [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (source target : Ty Row) : check rows source target = true ↔ Subtype leRow source target := by
  constructor
  · exact (layers_sound rows rowExact _).1 source target
  · exact (layers_complete rows rowExact rowRefl rowTrans _).1 source target
      (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem check_false_iff [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (source target : Ty Row) : check rows source target = false ↔ ¬ Subtype leRow source target := by
  rw [← check_true_iff rows rowExact rowRefl rowTrans source target]
  exact Bool.eq_false_iff

def previous [DecidableEq Row] (rows : Row → Row → Bool) : Nat → Layer Row
  | 0 => initial
  | n + 1 => layers rows n

theorem layers_next [DecidableEq Row] (rows : Row → Row → Bool) (bound : Nat) :
    layers rows bound = next rows (previous rows bound) := by
  cases bound <;> rfl

/-- A cut-free finite lattice derivation whose atomic premises are the actual
computed comparisons at the preceding structural layer. No semantic atom
oracle remains in this judgment. -/
def Comparison [DecidableEq Row] (rows : Row → Row → Bool) (source target : Ty Row) : Prop :=
  StructuralDecisions.Comparison
    (fun a b => SemanticRecordLatticeCheck.rowCheck
      (atomCheck rows (previous rows (max (depth source) (depth target)))) a b = true)
    (SemanticRecordAtoms.encode source) (SemanticRecordAtoms.encode target)

theorem comparison_iff_check [DecidableEq Row] (rows : Row → Row → Bool) (source target : Ty Row) :
    Comparison rows source target ↔ check rows source target = true := by
  unfold check
  rw [layers_next]
  change StructuralDecisions.Comparison _ _ _ ↔ StructuralDecisions.check _ _ _ = true
  exact ⟨StructuralDecisions.check_complete _ (fun _ _ => Iff.rfl),
    StructuralDecisions.check_sound _ (fun _ _ => Iff.rfl)⟩

/-- Every declarative derivation, including arbitrary intermediate types in
transitivity, has a finite cut-free comparison with computed atom premises. -/
theorem cut_elimination [DecidableEq Row] (rows : Row → Row → Bool)
    (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (source target : Ty Row) : Comparison rows source target ↔ Subtype leRow source target :=
  (comparison_iff_check rows source target).trans (check_true_iff rows rowExact rowRefl rowTrans source target)

end Yulang.SemanticRecordChecker
