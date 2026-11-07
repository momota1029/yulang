import Yulang.CommonRecordTailProfiles
import Yulang.CommonOuterLabels

/-!
# Finite inspection of all remaining record labels

The initial constructor cutoff and positive-depth payload profiles distinguish
only outer record/default labels and mask labels. Their finite support, plus
one fresh label, therefore suffices for the complete same-depth tail relation.
The resulting conditions are Boolean checks and ordinary proper-child subtype
comparisons. No residual quantifier over labels, depths or demand ranks is
stored as a tail obligation.
-/

namespace Yulang.CommonRecordTailFinite

open CommonSyntax (Layer)
open CommonPayloadProjection
open CommonRecordTailProfiles
open CommonOuterLabels

universe u v

variable {Row : Type u} {Index : Type v}

theorem initialField_outside (source : Layer Row Index) (hidden : List Nat)
    (first last : Nat) (firstHidden : first ∉ hidden) (lastHidden : last ∉ hidden)
    (firstOutside : first ∉ labels source) (lastOutside : last ∉ labels source) :
    initialField hidden first source = initialField hidden last source := by
  induction source generalizing hidden <;>
    simp_all [labels, initialField, List.mem_append, List.mem_cons]

theorem initialOptional_outside (source : Layer Row Index) (hidden : List Nat)
    (first last : Nat) (firstHidden : first ∉ hidden) (lastHidden : last ∉ hidden)
    (firstOutside : first ∉ labels source) (lastOutside : last ∉ labels source) :
    initialOptional hidden first source = initialOptional hidden last source := by
  induction source generalizing hidden <;>
    simp_all [labels, initialOptional, List.mem_append, List.mem_cons]

def support (hidden : List Nat) (source target : Common.Ty) : List Nat :=
  hidden ++ (labels source ++ labels target)

def inspectLabels (hidden : List Nat) (source target : Common.Ty) : List Nat :=
  representatives (support hidden source target)

theorem atLabel_outside (hidden : List Nat) (source target : Common.Ty) (first last : Nat)
    (firstOutside : first ∉ support hidden source target)
    (lastOutside : last ∉ support hidden source target) :
    AtLabel source target first ↔ AtLabel source target last := by
  simp only [support, List.mem_append, not_or] at firstOutside lastOutside
  have emptyFirst : first ∉ ([] : List Nat) := by simp
  have emptyLast : last ∉ ([] : List Nat) := by simp
  rw [AtLabel,
    initialField_outside source [] first last emptyFirst emptyLast firstOutside.2.1 lastOutside.2.1,
    initialField_outside target [] first last emptyFirst emptyLast firstOutside.2.2 lastOutside.2.2,
    initialOptional_outside source [] first last emptyFirst emptyLast firstOutside.2.1 lastOutside.2.1,
    initialOptional_outside target [] first last emptyFirst emptyLast firstOutside.2.2 lastOutside.2.2,
    fieldType_outside source [] first last emptyFirst emptyLast firstOutside.2.1 lastOutside.2.1,
    fieldType_outside target [] first last emptyFirst emptyLast firstOutside.2.2 lastOutside.2.2,
    optionalType_outside source [] first last emptyFirst emptyLast firstOutside.2.1 lastOutside.2.1,
    optionalType_outside target [] first last emptyFirst emptyLast firstOutside.2.2 lastOutside.2.2]
  rfl

/-- A finite label list covers all same-depth field and nontrivial optional
requirements, including labels absent from both source and target syntax. -/
theorem tail_finite_exact (hidden : List Nat) (source target : Common.Ty) :
    Common.RecordTailLe hidden source target ↔
      ∀ label ∈ inspectLabels hidden source target, label ∉ hidden → AtLabel source target label := by
  rw [tail_profiles_exact]
  apply forall_iff_representatives (support hidden source target)
    (fun label => label ∉ hidden → AtLabel source target label)
  intro first last firstOutside lastOutside
  have firstVisible : first ∉ hidden := by
    intro member
    apply firstOutside
    exact List.mem_append.mpr (Or.inl member)
  have lastVisible : last ∉ hidden := by
    intro member
    apply lastOutside
    exact List.mem_append.mpr (Or.inl member)
  simpa only [firstVisible, lastVisible, not_false_eq_true, true_implies] using
    atLabel_outside hidden source target first last firstOutside lastOutside

/-- The reference inspection uses exactly one representative beyond the
explicit labels. Repeated labels may be deduplicated by a later pass. -/
theorem inspectLabels_length (hidden : List Nat) (source target : Common.Ty) :
    (inspectLabels hidden source target).length =
      hidden.length + (labels source).length + (labels target).length + 1 := by
  simp [inspectLabels, representatives, support, Nat.add_assoc]

end Yulang.CommonRecordTailFinite
