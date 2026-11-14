import Yulang.GeneralNominalRawFrame179

/-! Constructive finite extension over an arbitrary existing centered journal.
The local compatibility hypotheses concern actual finite origins, bounds and
name overlap. No final plan validity or common-model premise is supplied. -/
namespace Yulang.GeneralNominalCenteredJournalExtension179
open GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenteredModelExtension
open GeneralNominalRawFrame179 (fullSources)

 theorem nominal_extension (state : GeneralNominalCenteredSteps.State roles)
    (arguments : Fin count → NominalArgument) (previous : Assignment)
    (valid : GeneralNominalCenteredSteps.Models state previous) (values : Fin count → Ty)
    (linked : ∀ index, (arguments index).argument.endpoints.1 ∈ fullSources state ∧
      (arguments index).argument.endpoints.2 ∈ fullSources state ∧
      originSource (arguments index).origin ∈ fullSources state)
    (bounds : ∀ index, GeneralNominalCaptureMerges.Fits previous
      (arguments index).argument.endpoints (values index))
    (readback : ∀ index, (∃ actual, Observes previous (arguments index).origin actual) ∧
      ∀ actual, Observes previous (arguments index).origin actual → Equivalent actual (values index))
    (coherent : ∀ first last, (arguments first).argument.center = (arguments last).argument.center →
      values first = values last)
    (preserved : ∀ index, (arguments index).argument.center ∈ fullSources state →
      values index = (previous (arguments index).argument.center).1) :
    ∃ extended, GeneralNominalCenteredSteps.Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      (∀ index, (extended (arguments index).argument.center).1 = values index) ∧
      ∀ index, (arguments index).Holds extended := by
  let names := fun index => (arguments index).argument.center
  let extended := assign previous names values
  have kept (name : Nat) (member : name ∈ fullSources state) : extended name = previous name := by
    apply assign_preserves
    intro index equal
    simpa only [names,equal] using preserved index (show names index ∈ fullSources state from equal ▸ member)
  have centerValue (index : Fin count) : (extended (arguments index).argument.center).1 = values index :=
    assign_value previous names values coherent index
  refine ⟨extended,GeneralNominalRawFrame179.centered_models_frame state
    (fun name member => (kept name member).symm) valid,kept,centerValue,?_⟩
  intro index
  constructor
  · change Subtype (extended (arguments index).argument.endpoints.1).1
        (extended (arguments index).argument.center).1 ∧
      Subtype (extended (arguments index).argument.center).1 (extended (arguments index).argument.endpoints.2).1
    rw [kept _ (linked index).1,kept _ (linked index).2.1,centerValue index]
    exact bounds index
  · obtain ⟨actual,seen⟩ := (readback index).1
    refine ⟨⟨actual,observes_same seen (kept _ (linked index).2.2).symm⟩,⟨_,.source _⟩,?_⟩
    intro actual center seen named
    cases named
    rw [centerValue index]
    exact (readback index).2 actual (observes_same seen (kept _ (linked index).2.2))

end Yulang.GeneralNominalCenteredJournalExtension179
