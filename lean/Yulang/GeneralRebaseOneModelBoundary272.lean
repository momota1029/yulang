import Yulang.GeneralRebaseTreeHybrid272

namespace Yulang.GeneralRebaseOneModelBoundary272
open CommonNominalFullCarrier
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalVersionedCycles232 (Equal)
open GeneralNominalOriginTerms (Same)
open GeneralRebaseFiniteTree272 (Tree scalar)
open GeneralRebaseTreeConstructors272 (scalar_canonical)
open GeneralRebaseTreeInterpreter272 (Certified)
open GeneralRebaseFiniteTreeCompare272 (modelLookup local_sound reject)
open GeneralDictionaryOutputDepth252 (initial model initial_model)
open GeneralDictionaryOutputDepthInstall252 (smallModel small_initial)

def seed : Nat → Option Tree
 | 0 | 3 => some (scalar .int)
 | _ => none

theorem checked : Certified smallModel seed := by
 intro n t hit
 unfold seed at hit
 split at hit
 · cases Option.some.inj hit
   exact ⟨scalar_canonical _,subtype_refl _,subtype_refl _⟩
 · cases Option.some.inj hit
   exact ⟨scalar_canonical _,subtype_refl _,subtype_refl _⟩
 · contradiction

theorem computed_local : modelLookup seed (.source 3) (.source 0) = some true := by decide +kernel

theorem remains_partial : reject seed (.source 3) (.source 0) = none := by decide +kernel

theorem equal_in_small : Same smallModel (.source 3) (.source 0) := by
 have bit := local_sound smallModel seed checked (.source 3) (.source 0)
 rw [computed_local] at bit
 exact bit

theorem not_equal_in_other : ¬ Same model (.source 3) (.source 0) := by
 intro same
 have equal := same.2.2 _ _ (.source _) (.source _)
 have contradiction := GeneralDictionaryInspectionHeads215.tag_subtype
   (GeneralDictionaryInspectionHeads215.tagged_nominal 0 _)
   (GeneralDictionaryInspectionHeads215.tagged_scalar .int) equal.1
 cases contradiction

theorem actual_boundary :
 GeneralNominalVersionedJournal232.Models initial smallModel ∧
 GeneralNominalVersionedJournal232.Models initial model ∧
 Same smallModel (.source 3) (.source 0) ∧ ¬ Equal initial (.source 3) (.source 0) :=
 ⟨small_initial,initial_model,equal_in_small,fun all => not_equal_in_other (all model initial_model)⟩

end Yulang.GeneralRebaseOneModelBoundary272
