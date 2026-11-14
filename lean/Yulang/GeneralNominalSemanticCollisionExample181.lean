import Yulang.GeneralNominalSemanticCompatibility181
import Yulang.GeneralNominalCenteredExtensionExact180
import Yulang.GeneralDictionaryCenteredNominalPointExample178
import Yulang.CommonNominalFullConstructors

/-! Regression: two distinct but equivalent chosen representatives share one
fresh center. Semantic extension succeeds where exact-value assignment cannot.
This finite-family fixture does not assert an inspected Candidate for the pair. -/
namespace Yulang.GeneralNominalSemanticCollisionExample181
open GeneralNominalCenters GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalRawFrame179 (fullSources)
open GeneralDictionaryCenteredNominalPointExample178 (start inhabited)
open GeneralDictionaryNominalPairExample178 (assignment upper_value)

def arguments (_ : Fin 2) : NominalArgument := ⟨⟨(3,3),100⟩,.source 3⟩
def values (i : Fin 2) : Ty := if i.val = 0 then .top else .union .top .top

theorem top_union : Equivalent (.top : Ty) (.union .top .top) :=
  ⟨((common_union_is_join .top .top (.union .top .top)).mp (subtype_refl _)).1,
    (common_union_is_join .top .top .top).mpr ⟨subtype_refl _,subtype_refl _⟩⟩

theorem representative (i : Fin 2) : Equivalent (.top : Ty) (values i) := by
  unfold values
  split
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact top_union

theorem source_member : 3 ∈ fullSources start := by decide +kernel
theorem center_fresh : 100 ∉ fullSources start := by decide +kernel

theorem semantic_extension :
    ∃ extended, GeneralNominalCenteredSteps.Models start extended ∧
      (∀ name ∈ fullSources start, extended name = assignment false name) ∧
      ∀ i, (arguments i).Holds extended := by
  apply GeneralNominalSemanticCompatibility181.compatible_extension
    start arguments (assignment false) (inhabited false) values
  · intro i
    exact ⟨source_member,source_member,source_member⟩
  · intro i
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen
    cases seen
    exact representative i
  · intro i
    exact representative i
  · intro i j _
    exact ⟨subtype_trans (representative i).2 (representative j).1,
      subtype_trans (representative j).2 (representative i).1⟩
  · intro _ member
    exact False.elim (center_fresh member)

theorem exact_assignment_impossible :
    ¬ ∃ extended : GeneralNominalCommonBridge.Assignment,
      ∀ i, (extended (arguments i).argument.center).1 = values i := by
  apply GeneralNominalCenteredExtensionExact180.collision_obstruction arguments values 0 1 rfl
  intro h
  cases h

end Yulang.GeneralNominalSemanticCollisionExample181
