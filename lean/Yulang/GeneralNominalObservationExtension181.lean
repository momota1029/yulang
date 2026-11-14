import Yulang.GeneralNominalSemanticCompatibility181

/-! A representative-free criterion for finite nominal extension. The criterion
uses actual origin observations, endpoint bounds and center collisions only. -/
namespace Yulang.GeneralNominalObservationExtension181
open GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenteredModelExtension
open GeneralNominalRawFrame179 (fullSources)

private theorem equivalent_trans (one : Equivalent a b) (two : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans one.1 two.1, subtype_trans two.2 one.2⟩

theorem extension_iff (state : GeneralNominalCenteredSteps.State roles)
    (arguments : Fin count → NominalArgument) (previous : Assignment)
    (valid : GeneralNominalCenteredSteps.Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧
      originSource (arguments i).origin ∈ fullSources state) :
    (∃ extended, GeneralNominalCenteredSteps.Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      ∀ i, (arguments i).Holds extended) ↔
    (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
    (∀ i actual, Observes previous (arguments i).origin actual →
      GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
    (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
      Observes previous (arguments i).origin first → Observes previous (arguments j).origin last →
      Equivalent first last) ∧
    (∀ i actual, (arguments i).argument.center ∈ fullSources state →
      Observes previous (arguments i).origin actual →
      Equivalent actual (previous (arguments i).argument.center).1) := by
  constructor
  · rintro ⟨extended,_,kept,holds⟩
    have readback i actual (seen : Observes previous (arguments i).origin actual) :
        Equivalent actual (extended (arguments i).argument.center).1 :=
      (holds i).2.2.2 actual (extended (arguments i).argument.center).1
        (observes_same seen (kept _ (linked i).2.2).symm) (.source _)
    refine ⟨?_,?_,?_,?_⟩
    · intro i
      obtain ⟨actual,seen⟩ := (holds i).2.1
      exact ⟨actual,observes_same seen (kept _ (linked i).2.2)⟩
    · intro i actual seen
      have h := (holds i).1
      change Subtype (extended (arguments i).argument.endpoints.1).1
          (extended (arguments i).argument.center).1 ∧
        Subtype (extended (arguments i).argument.center).1 (extended (arguments i).argument.endpoints.2).1 at h
      rw [kept _ (linked i).1,kept _ (linked i).2.1] at h
      exact ⟨subtype_trans h.1 (readback i actual seen).2,
        subtype_trans (readback i actual seen).1 h.2⟩
    · intro i j first last same one two
      have firstEq := readback i first one
      rw [same] at firstEq
      exact equivalent_trans firstEq ⟨(readback j last two).2,(readback j last two).1⟩
    · intro i actual member seen
      have h := readback i actual seen
      rwa [kept _ member] at h
  · rintro ⟨inhabited,bounds,coherent,overlap⟩
    classical
    let values := fun i => Classical.choose (inhabited i)
    have seen i : Observes previous (arguments i).origin (values i) := Classical.choose_spec (inhabited i)
    apply GeneralNominalSemanticCompatibility181.compatible_extension state arguments previous valid values linked
    · intro i
      exact ⟨inhabited i,fun actual observed => coherent i i actual (values i) rfl observed (seen i)⟩
    · exact fun i => bounds i (values i) (seen i)
    · exact fun i j same => coherent i j (values i) (values j) same (seen i) (seen j)
    · exact fun i member => overlap i (values i) member (seen i)

end Yulang.GeneralNominalObservationExtension181
