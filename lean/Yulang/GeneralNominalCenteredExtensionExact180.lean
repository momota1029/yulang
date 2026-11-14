import Yulang.GeneralNominalCenteredJournalExtension179

/-! Exact compatibility conditions for a finite, old-footprint-preserving
extension. This is a finite extension characterization, not general evidence
production from selected candidates. -/
namespace Yulang.GeneralNominalCenteredExtensionExact180
open GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenteredModelExtension
open GeneralNominalRawFrame179 (fullSources)

 theorem extension_iff (state : GeneralNominalCenteredSteps.State roles)
    (arguments : Fin count → NominalArgument) (previous : Assignment)
    (valid : GeneralNominalCenteredSteps.Models state previous) (values : Fin count → Ty)
    (linked : ∀ index, (arguments index).argument.endpoints.1 ∈ fullSources state ∧
      (arguments index).argument.endpoints.2 ∈ fullSources state ∧
      originSource (arguments index).origin ∈ fullSources state) :
    (∃ extended, GeneralNominalCenteredSteps.Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      (∀ index, (extended (arguments index).argument.center).1 = values index) ∧
      ∀ index, (arguments index).Holds extended) ↔
    (∀ index, GeneralNominalCaptureMerges.Fits previous
      (arguments index).argument.endpoints (values index)) ∧
    (∀ index, (∃ actual, Observes previous (arguments index).origin actual) ∧
      ∀ actual, Observes previous (arguments index).origin actual → Equivalent actual (values index)) ∧
    (∀ first last, (arguments first).argument.center = (arguments last).argument.center →
      values first = values last) ∧
    (∀ index, (arguments index).argument.center ∈ fullSources state →
      values index = (previous (arguments index).argument.center).1) := by
  constructor
  · rintro ⟨extended,_,kept,center,holds⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro index
      have bounds := (holds index).1
      change Subtype (extended (arguments index).argument.endpoints.1).1
          (extended (arguments index).argument.center).1 ∧
        Subtype (extended (arguments index).argument.center).1
          (extended (arguments index).argument.endpoints.2).1 at bounds
      rw [kept _ (linked index).1,kept _ (linked index).2.1,center index] at bounds
      exact bounds
    · intro index
      obtain ⟨⟨actual,seen⟩,_,same⟩ := (holds index).2
      refine ⟨⟨actual,observes_same seen (kept _ (linked index).2.2)⟩,?_⟩
      intro value observed
      have result := same value (extended (arguments index).argument.center).1
        (observes_same observed (kept _ (linked index).2.2).symm) (.source _)
      simpa only [center index] using result
    · intro first last equal
      rw [← center first,← center last,equal]
    · intro index member
      rw [← center index,kept _ member]
  · rintro ⟨bounds,readback,coherent,preserved⟩
    exact GeneralNominalCenteredJournalExtension179.nominal_extension state arguments previous
      valid values linked bounds readback coherent preserved

 theorem overlap_obstruction (state : GeneralNominalCenteredSteps.State roles)
    (arguments : Fin count → NominalArgument) (previous : Assignment) (values : Fin count → Ty)
    (index : Fin count) (member : (arguments index).argument.center ∈ fullSources state)
    (different : values index ≠ (previous (arguments index).argument.center).1) :
    ¬ ∃ extended : Assignment,
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      (∀ index, (extended (arguments index).argument.center).1 = values index) := by
  rintro ⟨extended,kept,center⟩
  apply different
  rw [← center index,kept _ member]

 theorem collision_obstruction (arguments : Fin count → NominalArgument) (values : Fin count → Ty)
    (first last : Fin count)
    (same : (arguments first).argument.center = (arguments last).argument.center)
    (different : values first ≠ values last) :
    ¬ ∃ extended : Assignment,
      ∀ index, (extended (arguments index).argument.center).1 = values index := by
  rintro ⟨extended,center⟩
  apply different
  rw [← center first,← center last,same]

end Yulang.GeneralNominalCenteredExtensionExact180
