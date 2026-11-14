import Yulang.GeneralNominalCenteredJournalExtension179

/-! Semantic compatibility for finite families of arbitrary nominal origins.
The old raw footprint remains fixed. Collisions need equivalent observations,
not identical chosen representatives. This does not construct general evidence. -/
namespace Yulang.GeneralNominalSemanticCompatibility181
open GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenteredModelExtension
open GeneralNominalRawFrame179 (fullSources)

private theorem equivalent_trans (one : Equivalent a b) (two : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans one.1 two.1, subtype_trans two.2 one.2⟩

noncomputable def chooseModel (state : GeneralNominalCenteredSteps.State roles)
    (previous : Assignment) (centers : Fin count → Nat) (values : Fin count → Ty) : Assignment := by
  classical
  exact fun name => if name ∈ fullSources state then previous name else
    if found : ∃ i, centers i = name then
      (values (Classical.choose found),(previous name).2) else previous name

theorem chooseModel_kept (state : GeneralNominalCenteredSteps.State roles)
    (previous : Assignment) (centers : Fin count → Nat) (values : Fin count → Ty)
    (member : name ∈ fullSources state) :
    chooseModel state previous centers values name = previous name := by
  classical
  simp only [chooseModel,ite_eq_left member]

theorem chooseModel_readback (state : GeneralNominalCenteredSteps.State roles)
    (previous : Assignment) (centers : Fin count → Nat) (values : Fin count → Ty)
    (coherent : ∀ i j, centers i = centers j → Equivalent (values i) (values j))
    (overlap : ∀ i, centers i ∈ fullSources state → Equivalent (values i) (previous (centers i)).1)
    (i : Fin count) :
    Equivalent (values i) (chooseModel state previous centers values (centers i)).1 := by
  classical
  unfold chooseModel
  split
  · rename_i member
    exact overlap i member
  · rw [dite_eq_left ⟨i,rfl⟩]
    exact coherent i _ (Classical.choose_spec (show ∃ j, centers j = centers i from ⟨i,rfl⟩)).symm

theorem compatible_extension (state : GeneralNominalCenteredSteps.State roles)
    (arguments : Fin count → NominalArgument) (previous : Assignment)
    (valid : GeneralNominalCenteredSteps.Models state previous) (values : Fin count → Ty)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧
      originSource (arguments i).origin ∈ fullSources state)
    (observed : ∀ i, (∃ actual, Observes previous (arguments i).origin actual) ∧
      ∀ actual, Observes previous (arguments i).origin actual → Equivalent actual (values i))
    (bounds : ∀ i, GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints (values i))
    (coherent : ∀ i j, (arguments i).argument.center = (arguments j).argument.center →
      Equivalent (values i) (values j))
    (overlap : ∀ i, (arguments i).argument.center ∈ fullSources state →
      Equivalent (values i) (previous (arguments i).argument.center).1) :
    ∃ extended, GeneralNominalCenteredSteps.Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      ∀ i, (arguments i).Holds extended := by
  let centers := fun i => (arguments i).argument.center
  let extended := chooseModel state previous centers values
  have kept (name) (member : name ∈ fullSources state) : extended name = previous name :=
    chooseModel_kept state previous centers values member
  have readback i : Equivalent (values i) (extended (arguments i).argument.center).1 :=
    chooseModel_readback state previous centers values coherent overlap i
  refine ⟨extended,GeneralNominalRawFrame179.centered_models_frame state
    (fun name member => (kept name member).symm) valid,kept,?_⟩
  intro i
  constructor
  · change Subtype (extended (arguments i).argument.endpoints.1).1
        (extended (arguments i).argument.center).1 ∧
      Subtype (extended (arguments i).argument.center).1 (extended (arguments i).argument.endpoints.2).1
    rw [kept _ (linked i).1,kept _ (linked i).2.1]
    exact ⟨subtype_trans (bounds i).1 (readback i).1,
      subtype_trans (readback i).2 (bounds i).2⟩
  · obtain ⟨actual,seen⟩ := (observed i).1
    refine ⟨⟨actual,observes_same seen (kept _ (linked i).2.2).symm⟩,⟨_,.source _⟩,?_⟩
    intro actual center seen named
    cases named
    exact equivalent_trans ((observed i).2 actual (observes_same seen (kept _ (linked i).2.2)))
      (readback i)

theorem compatible_iff (state : GeneralNominalCenteredSteps.State roles)
    (arguments : Fin count → NominalArgument) (previous : Assignment)
    (valid : GeneralNominalCenteredSteps.Models state previous) (values : Fin count → Ty)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧
      originSource (arguments i).origin ∈ fullSources state)
    (observed : ∀ i, (∃ actual, Observes previous (arguments i).origin actual) ∧
      ∀ actual, Observes previous (arguments i).origin actual → Equivalent actual (values i)) :
    (∃ extended, GeneralNominalCenteredSteps.Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      ∀ i, (arguments i).Holds extended) ↔
    (∀ i, GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints (values i)) ∧
    (∀ i j, (arguments i).argument.center = (arguments j).argument.center →
      Equivalent (values i) (values j)) ∧
    (∀ i, (arguments i).argument.center ∈ fullSources state →
      Equivalent (values i) (previous (arguments i).argument.center).1) := by
  constructor
  · rintro ⟨extended,_,kept,holds⟩
    have readback i : Equivalent (values i) (extended (arguments i).argument.center).1 := by
      obtain ⟨actual,seen⟩ := (observed i).1
      have one := (observed i).2 actual seen
      have two := (holds i).2.2.2 actual (extended (arguments i).argument.center).1
        (observes_same seen (kept _ (linked i).2.2).symm) (.source _)
      exact equivalent_trans ⟨one.2,one.1⟩ two
    refine ⟨?_,?_,?_⟩
    · intro i
      have h := (holds i).1
      change Subtype (extended (arguments i).argument.endpoints.1).1
          (extended (arguments i).argument.center).1 ∧
        Subtype (extended (arguments i).argument.center).1 (extended (arguments i).argument.endpoints.2).1 at h
      rw [kept _ (linked i).1,kept _ (linked i).2.1] at h
      exact ⟨subtype_trans h.1 (readback i).2,subtype_trans (readback i).1 h.2⟩
    · intro i j equal
      have one := readback i
      rw [equal] at one
      exact equivalent_trans one ⟨(readback j).2,(readback j).1⟩
    · intro i member
      have h := readback i
      rwa [kept _ member] at h
  · rintro ⟨bounds,coherent,overlap⟩
    exact compatible_extension state arguments previous valid values linked observed bounds coherent overlap

end Yulang.GeneralNominalSemanticCompatibility181
