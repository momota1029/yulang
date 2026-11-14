import Yulang.GeneralNominalCenteredExtensionExact180

/-! Source-origin specialization: readback values come from the preserved old
assignment. Equal fresh names may be shared when their source values agree. -/
namespace Yulang.GeneralNominalSourceExtension180
open GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRawFrame179 (fullSources)

def argument (endpoints : GeneralSourceState.Interval) (center source : Nat) : NominalArgument :=
  ⟨⟨endpoints,center⟩,.source source⟩

theorem source_extension (state : GeneralNominalCenteredSteps.State roles)
    (previous : Assignment) (valid : GeneralNominalCenteredSteps.Models state previous)
    (endpoints : Fin count → GeneralSourceState.Interval)
    (centers sources : Fin count → Nat)
    (linked : ∀ i, (endpoints i).1 ∈ fullSources state ∧
      (endpoints i).2 ∈ fullSources state ∧ sources i ∈ fullSources state)
    (bounds : ∀ i, GeneralNominalCaptureMerges.Fits previous (endpoints i) (previous (sources i)).1)
    (coherent : ∀ i j, centers i = centers j → (previous (sources i)).1 = (previous (sources j)).1)
    (preserved : ∀ i, centers i ∈ fullSources state → (previous (sources i)).1 = (previous (centers i)).1) :
    ∃ extended, GeneralNominalCenteredSteps.Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      (∀ i, (extended (centers i)).1 = (previous (sources i)).1) ∧
      ∀ i, (argument (endpoints i) (centers i) (sources i)).Holds extended := by
  apply GeneralNominalCenteredJournalExtension179.nominal_extension state
    (fun i => argument (endpoints i) (centers i) (sources i)) previous valid
    (fun i => (previous (sources i)).1) linked bounds
  · intro i
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen
    cases seen
    exact ⟨subtype_refl _,subtype_refl _⟩
  · exact coherent
  · exact preserved

theorem fresh_source_extension (state : GeneralNominalCenteredSteps.State roles)
    (previous : Assignment) (valid : GeneralNominalCenteredSteps.Models state previous)
    (endpoints : Fin count → GeneralSourceState.Interval)
    (centers sources : Fin count → Nat)
    (linked : ∀ i, (endpoints i).1 ∈ fullSources state ∧
      (endpoints i).2 ∈ fullSources state ∧ sources i ∈ fullSources state)
    (bounds : ∀ i, GeneralNominalCaptureMerges.Fits previous (endpoints i) (previous (sources i)).1)
    (coherent : ∀ i j, centers i = centers j → (previous (sources i)).1 = (previous (sources j)).1)
    (fresh : ∀ i, centers i ∉ fullSources state) :
    ∃ extended, GeneralNominalCenteredSteps.Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      (∀ i, (extended (centers i)).1 = (previous (sources i)).1) ∧
      ∀ i, (argument (endpoints i) (centers i) (sources i)).Holds extended :=
  source_extension state previous valid endpoints centers sources linked bounds coherent
    (fun i member => False.elim (fresh i member))

end Yulang.GeneralNominalSourceExtension180
