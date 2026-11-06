import Yulang.RigidRecordChecker
import Yulang.RigidRecordOpaqueBoundary
import Yulang.ShadowSemanticRecords

/-!
# Computable semantic head views for shadow normalization

These helpers inspect the already decided decision-39 relation. A head is
exposed only when the entire tail is equivalent to that outer atom. They do
not distribute record construction or deletion through a union/intersection.
Every selected residual tail has strictly smaller constructor depth.
-/

namespace Yulang.ShadowRecordHeadViews

open StructuralBase (Ty IsRecord)
open RigidSemanticRecords (Subtype Equivalent)
open RigidRecordAtoms (atoms)
open RigidRecordLatticeCheck (depth)

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

def HasProper (leRow : Row → Row → Prop) (type : Ty Row) : Prop :=
  ∃ proper, IsRecord proper ∧ Equivalent leRow type proper

theorem hasProper_congr {a b : Ty Row} (same : Equivalent leRow a b) :
    HasProper leRow a ↔ HasProper leRow b :=
  ⟨fun ⟨proper, shape, old⟩ => ⟨proper, shape, same.symm.trans old⟩,
    fun ⟨proper, shape, old⟩ => ⟨proper, shape, same.trans old⟩⟩

theorem hasProper_of_record {type : Ty Row} (shape : IsRecord type) : HasProper leRow type :=
  ⟨type, shape, .refl _⟩

theorem hasProper_record_iff (label : Nat) (value rest : Ty Row) :
    HasProper leRow (.record label value rest) ↔ HasProper leRow rest := by
  constructor
  · rintro ⟨proper, shape, same⟩
    obtain ⟨fields, view⟩ := RigidRecordChecker.atomic_view_of_equivalent
      (show RigidRecordAtoms.Atomic (.record label value rest) from trivial) shape same
    cases view with
    | field tail => exact ⟨_, RigidRecordViews.spine_record _, tail⟩
  · rintro ⟨proper, shape, same⟩
    exact ⟨.record label value proper, .field shape,
      RigidSemanticRecords.record_congr label (.refl _) same⟩

theorem opaque_of_not_proper {type : Ty Row} (absent : ¬ HasProper leRow type) :
    RigidRecordOpaqueBoundary.OpaqueTail leRow type :=
  fun proper shape same => absent ⟨proper, shape, same⟩

def proper [DecidableEq Row] (rows : Row → Row → Bool) (type : Ty Row) : Bool :=
  ((RigidRecordChecker.layers rows (depth type)).view type).isSome

def heads (label : Nat) (type : Ty Row) : List (Ty Row × Ty Row) :=
  (atoms type).filterMap fun atom =>
    match atom with
    | .record name value rest => if name = label then some (value, rest) else none
    | _ => none

theorem heads_mem_iff (label : Nat) (type value rest : Ty Row) :
    (value, rest) ∈ heads label type ↔ .record label value rest ∈ atoms type := by
  constructor
  · intro member
    obtain ⟨atom, inside, hit⟩ := List.mem_filterMap.mp member
    cases atom with
    | record name actual tail =>
        by_cases same : name = label
        · subst name
          have equal : (actual, tail) = (value, rest) := by simpa using hit
          cases equal
          exact inside
        · simp [same] at hit
    | _ => cases hit
  · intro member
    exact List.mem_filterMap.mpr ⟨.record label value rest, member, by simp⟩

def headView [DecidableEq Row] (rows : Row → Row → Bool) (label : Nat) (type : Ty Row) :
    Option (Ty Row × Ty Row) :=
  (heads label type).find? fun pair =>
    RigidRecordChecker.check rows type (.record label pair.1 pair.2) &&
      RigidRecordChecker.check rows (.record label pair.1 pair.2) type

theorem headView_member [DecidableEq Row] (rows : Row → Row → Bool)
    {label : Nat} {type value rest : Ty Row}
    (found : headView rows label type = some (value, rest)) :
    .record label value rest ∈ atoms type :=
  (heads_mem_iff label type value rest).mp (List.mem_of_find?_eq_some found)

theorem headView_depth [DecidableEq Row] (rows : Row → Row → Bool)
    {label : Nat} {type value rest : Ty Row}
    (found : headView rows label type = some (value, rest)) : depth rest < depth type := by
  have bounded := RigidRecordChecker.atom_depth (headView_member rows found)
  simp only [depth] at bounded
  omega

section Exact

variable [DecidableEq Row] (rows : Row → Row → Bool)
  (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
  (rowRefl : ∀ row, leRow row row)
  (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)

include rowExact rowRefl rowTrans

theorem proper_exact (type : Ty Row) : proper rows type = true ↔ HasProper leRow type := by
  unfold proper
  constructor
  · intro present
    obtain ⟨result, found⟩ := Option.isSome_iff_exists.mp present
    exact ⟨result, (RigidRecordChecker.layers_sound rows rowExact _).2 type result found⟩
  · intro existsProper
    obtain ⟨result, found⟩ :=
      (RigidRecordChecker.layers_complete rows rowExact rowRefl rowTrans (depth type)).2.1
        type (Nat.le_refl _) existsProper
    simp [found]

theorem proper_false_iff (type : Ty Row) :
    proper rows type = false ↔ ¬ HasProper leRow type := by
  rw [← proper_exact rows rowExact rowRefl rowTrans type]
  exact Bool.eq_false_iff

theorem proper_congr {a b : Ty Row} (same : Equivalent leRow a b) :
    proper rows a = proper rows b := by
  apply Bool.eq_iff_iff.mpr
  rw [proper_exact rows rowExact rowRefl rowTrans,
    proper_exact rows rowExact rowRefl rowTrans]
  exact hasProper_congr same

theorem headView_sound {label : Nat} {type value rest : Ty Row}
    (found : headView rows label type = some (value, rest)) :
    Equivalent leRow type (.record label value rest) := by
  have checkPair : (RigidRecordChecker.check rows type (.record label value rest) &&
      RigidRecordChecker.check rows (.record label value rest) type) = true :=
    List.find?_some (p := fun pair : Ty Row × Ty Row =>
      RigidRecordChecker.check rows type (.record label pair.1 pair.2) &&
        RigidRecordChecker.check rows (.record label pair.1 pair.2) type) found
  have checked := Bool.and_eq_true_iff.mp checkPair
  exact ⟨(RigidRecordChecker.check_true_iff rows rowExact rowRefl rowTrans _ _).mp checked.1,
    (RigidRecordChecker.check_true_iff rows rowExact rowRefl rowTrans _ _).mp checked.2⟩

theorem headView_exists_of_member {label : Nat} {type value rest : Ty Row}
    (member : .record label value rest ∈ atoms type)
    (same : Equivalent leRow type (.record label value rest)) :
    ∃ pair, headView rows label type = some pair := by
  apply Option.isSome_iff_exists.mp
  apply List.find?_isSome.mpr
  refine ⟨(value, rest), (heads_mem_iff label type value rest).mpr member, ?_⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨(RigidRecordChecker.check_true_iff rows rowExact rowRefl rowTrans _ _).mpr same.1,
      (RigidRecordChecker.check_true_iff rows rowExact rowRefl rowTrans _ _).mpr same.2⟩

/-- Opaque equality cannot change the visible head label. A matching head
can therefore be found among the finite atoms already in the input tail. -/
theorem headView_complete {label : Nat} {type value rest : Ty Row}
    (noProper : ¬ HasProper leRow type)
    (same : Equivalent leRow type (.record label value rest)) :
    ∃ pair, headView rows label type = some pair := by
  obtain ⟨atom, member, equivalent⟩ :=
    RigidRecordAtoms.equivalent_atomic_witness (by trivial) same
  have noView : ¬ ∃ fields, RigidRecordViews.View leRow (.record label value rest) fields := by
    rintro ⟨fields, view⟩
    exact noProper ⟨_, RigidRecordViews.spine_record _, same.trans view.equivalent⟩
  have chain := (RigidRecordAtoms.atomic_iff_chain
    (RigidRecordAtoms.mem_atoms_atomic member) (by trivial)).mp equivalent.1
  have matched := RigidRecordAtomNormal.Chain.opaque_target chain (by trivial) noView
  cases matched with
  | field _ _ =>
      exact headView_exists_of_member rows rowExact rowRefl rowTrans member
        (same.trans equivalent.symm)

theorem headView_record (label : Nat) (value rest : Ty Row) :
    headView rows label (.record label value rest) = some (value, rest) := by
  have checked : RigidRecordChecker.check rows (.record label value rest)
      (.record label value rest) = true :=
    (RigidRecordChecker.check_true_iff rows rowExact rowRefl rowTrans _ _).mpr (.refl _)
  simp [headView, heads, atoms, checked]

theorem headView_tail_opaque {label : Nat} {type value rest : Ty Row}
    (noProper : ¬ HasProper leRow type)
    (found : headView rows label type = some (value, rest)) : ¬ HasProper leRow rest := by
  intro properTail
  have equivalent := headView_sound rows rowExact rowRefl rowTrans found
  exact noProper ((hasProper_congr equivalent).mpr
    ((hasProper_record_iff label value rest).mpr properTail))

theorem headView_tails_equivalent {label : Nat} {left right a b r s : Ty Row}
    (noProper : ¬ HasProper leRow right) (same : Equivalent leRow left right)
    (first : headView rows label left = some (a, r))
    (last : headView rows label right = some (b, s)) : Equivalent leRow r s := by
  have source := headView_sound rows rowExact rowRefl rowTrans first
  have target := headView_sound rows rowExact rowRefl rowTrans last
  have opaqueTail := headView_tail_opaque rows rowExact rowRefl rowTrans noProper last
  exact ((RigidRecordOpaqueBoundary.opaque_comparison_iff label a b r
    (opaque_of_not_proper opaqueTail)).mp (source.symm.trans (same.trans target)).1).2

end Exact

end Yulang.ShadowRecordHeadViews
