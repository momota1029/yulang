import Yulang.CommonNominalOuterLabels
import Yulang.CommonNominalRecordTailProfiles

/-!
# A complete finite label inventory for regular nominal record tails

Every label mentioned by either original outer syntax, together with hidden
labels and one fresh representative, covers all remaining field/optional
observations. Guarded nominal/float/negative payloads remain uninspected.
This removes the label quantifier; compilation of the resulting payload
comparisons into a solved source family remains a separate step.
-/

namespace Yulang.CommonNominalFiniteRecordTail

open CommonNominalSyntax (Layer)
open CommonNominalCarrier (Ty RecordTailLe)
open CommonNominalOuterLabels (labels representatives)
open CommonNominalRecordTailProfiles (initialField initialOptional AtLabel)

theorem initial_field_outside (source : Layer Row Index) (hidden : List Nat) (first last : Nat)
    (firstHidden : first ∉ hidden) (lastHidden : last ∉ hidden)
    (firstOutside : first ∉ labels source) (lastOutside : last ∉ labels source) :
    initialField hidden first source = initialField hidden last source := by
  induction source generalizing hidden <;>
    simp_all [labels, initialField, List.mem_append, List.mem_cons]

theorem initial_optional_outside (source : Layer Row Index) (hidden : List Nat) (first last : Nat)
    (firstHidden : first ∉ hidden) (lastHidden : last ∉ hidden)
    (firstOutside : first ∉ labels source) (lastOutside : last ∉ labels source) :
    initialOptional hidden first source = initialOptional hidden last source := by
  induction source generalizing hidden <;>
    simp_all [labels, initialOptional, List.mem_append, List.mem_cons]

def support (hidden : List Nat) (source target : Ty) : List Nat :=
  hidden ++ (labels source ++ labels target)

theorem at_label_outside (source target : Ty) (first last : Nat)
    (sourceFirst : first ∉ labels source) (sourceLast : last ∉ labels source)
    (targetFirst : first ∉ labels target) (targetLast : last ∉ labels target) :
    AtLabel source target first ↔ AtLabel source target last := by
  have firstSource := initial_field_outside source [] first last (by simp) (by simp) sourceFirst sourceLast
  have firstTarget := initial_field_outside target [] first last (by simp) (by simp) targetFirst targetLast
  have optionalSource := initial_optional_outside source [] first last (by simp) (by simp) sourceFirst sourceLast
  have optionalTarget := initial_optional_outside target [] first last (by simp) (by simp) targetFirst targetLast
  have sourceField := CommonNominalOuterLabels.fieldType_outside source [] first last
    (by simp) (by simp) sourceFirst sourceLast
  have targetField := CommonNominalOuterLabels.fieldType_outside target [] first last
    (by simp) (by simp) targetFirst targetLast
  have sourceOptional := CommonNominalOuterLabels.optionalType_outside source [] first last
    (by simp) (by simp) sourceFirst sourceLast
  have targetOptional := CommonNominalOuterLabels.optionalType_outside target [] first last
    (by simp) (by simp) targetFirst targetLast
  simp only [AtLabel, firstSource, firstTarget, optionalSource, optionalTarget,
    sourceField, targetField, sourceOptional, targetOptional]

/-- All constructor depths, all negative ranks and all new observations are
covered by this actual finite list of original labels plus one fresh label. -/
theorem tail_finite_exact (hidden : List Nat) (source target : Ty) :
    RecordTailLe hidden source target ↔
      ∀ label ∈ representatives (support hidden source target), label ∉ hidden → AtLabel source target label := by
  rw [CommonNominalRecordTailProfiles.tail_profiles_exact]
  apply CommonNominalOuterLabels.forall_iff_representatives
  intro first last firstOutside lastOutside
  simp only [support, List.mem_append, not_or] at firstOutside lastOutside
  simpa only [firstOutside.1, lastOutside.1, not_false_eq_true, true_implies] using
    at_label_outside source target first last firstOutside.2.1 lastOutside.2.1
      firstOutside.2.2 lastOutside.2.2

end Yulang.CommonNominalFiniteRecordTail
