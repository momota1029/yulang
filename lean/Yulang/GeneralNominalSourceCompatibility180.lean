import Yulang.GeneralNominalSourceExtension180

/-! Semantic compatibility of source readbacks. Shared names need equivalent,
not syntactically equal, source values. Old footprint names are never changed. -/
namespace Yulang.GeneralNominalSourceCompatibility180
open GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRawFrame179 (fullSources)
open GeneralNominalSourceExtension180 (argument)

private theorem equivalent_trans (one : Equivalent a b) (two : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans one.1 two.1, subtype_trans two.2 one.2⟩

noncomputable def chooseModel (state : GeneralNominalCenteredSteps.State roles)
    (previous : Assignment) (centers sources : Fin count → Nat) : Assignment := by
  classical
  exact fun name => if name ∈ fullSources state then previous name else
    if found : ∃ i, centers i = name then
      ((previous (sources (Classical.choose found))).1,(previous name).2) else previous name

theorem chooseModel_kept (state : GeneralNominalCenteredSteps.State roles)
    (previous : Assignment) (centers sources : Fin count → Nat)
    (member : name ∈ fullSources state) :
    chooseModel state previous centers sources name = previous name := by
  classical
  simp only [chooseModel,ite_eq_left member]

theorem chooseModel_readback (state : GeneralNominalCenteredSteps.State roles)
    (previous : Assignment) (centers sources : Fin count → Nat)
    (coherent : ∀ i j, centers i = centers j →
      Equivalent (previous (sources i)).1 (previous (sources j)).1)
    (overlap : ∀ i, centers i ∈ fullSources state →
      Equivalent (previous (sources i)).1 (previous (centers i)).1) (i : Fin count) :
    Equivalent (previous (sources i)).1 (chooseModel state previous centers sources (centers i)).1 := by
  classical
  unfold chooseModel
  split
  · rename_i member
    exact overlap i member
  · rw [dite_eq_left ⟨i,rfl⟩]
    exact coherent i _ (Classical.choose_spec (show ∃ j, centers j = centers i from ⟨i,rfl⟩)).symm

theorem compatible_extension (state : GeneralNominalCenteredSteps.State roles)
    (previous : Assignment) (valid : GeneralNominalCenteredSteps.Models state previous)
    (endpoints : Fin count → GeneralSourceState.Interval) (centers sources : Fin count → Nat)
    (linked : ∀ i, (endpoints i).1 ∈ fullSources state ∧
      (endpoints i).2 ∈ fullSources state ∧ sources i ∈ fullSources state)
    (bounds : ∀ i, GeneralNominalCaptureMerges.Fits previous (endpoints i) (previous (sources i)).1)
    (coherent : ∀ i j, centers i = centers j →
      Equivalent (previous (sources i)).1 (previous (sources j)).1)
    (overlap : ∀ i, centers i ∈ fullSources state →
      Equivalent (previous (sources i)).1 (previous (centers i)).1) :
    ∃ extended, GeneralNominalCenteredSteps.Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      ∀ i, (argument (endpoints i) (centers i) (sources i)).Holds extended := by
  let extended := chooseModel state previous centers sources
  have kept (name) (member : name ∈ fullSources state) : extended name = previous name :=
    chooseModel_kept state previous centers sources member
  have readback i : Equivalent (previous (sources i)).1 (extended (centers i)).1 :=
    chooseModel_readback state previous centers sources coherent overlap i
  refine ⟨extended,GeneralNominalRawFrame179.centered_models_frame state
    (fun name member => (kept name member).symm) valid,kept,?_⟩
  intro i
  constructor
  · change Subtype (extended (endpoints i).1).1 (extended (centers i)).1 ∧
      Subtype (extended (centers i)).1 (extended (endpoints i).2).1
    rw [kept _ (linked i).1,kept _ (linked i).2.1]
    exact ⟨subtype_trans (bounds i).1 (readback i).1,
      subtype_trans (readback i).2 (bounds i).2⟩
  · change GeneralNominalOriginTerms.Same extended (.source (sources i)) (.source (centers i))
    refine ⟨⟨_,.source _⟩,⟨_,.source _⟩,?_⟩
    intro a b one two
    cases one
    cases two
    rw [kept _ (linked i).2.2]
    exact readback i

theorem compatible_iff (state : GeneralNominalCenteredSteps.State roles)
    (previous : Assignment) (valid : GeneralNominalCenteredSteps.Models state previous)
    (endpoints : Fin count → GeneralSourceState.Interval) (centers sources : Fin count → Nat)
    (linked : ∀ i, (endpoints i).1 ∈ fullSources state ∧
      (endpoints i).2 ∈ fullSources state ∧ sources i ∈ fullSources state) :
    (∃ extended, GeneralNominalCenteredSteps.Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      ∀ i, (argument (endpoints i) (centers i) (sources i)).Holds extended) ↔
    (∀ i, GeneralNominalCaptureMerges.Fits previous (endpoints i) (previous (sources i)).1) ∧
    (∀ i j, centers i = centers j →
      Equivalent (previous (sources i)).1 (previous (sources j)).1) ∧
    (∀ i, centers i ∈ fullSources state →
      Equivalent (previous (sources i)).1 (previous (centers i)).1) := by
  constructor
  · rintro ⟨extended,_,kept,holds⟩
    have readback i : Equivalent (previous (sources i)).1 (extended (centers i)).1 := by
      have h := (holds i).2.2.2 _ _ (.source _) (.source _)
      change Equivalent (extended (sources i)).1 (extended (centers i)).1 at h
      rwa [kept _ (linked i).2.2] at h
    refine ⟨?_,?_,?_⟩
    · intro i
      have h := (holds i).1
      change Subtype (extended (endpoints i).1).1 (extended (centers i)).1 ∧
        Subtype (extended (centers i)).1 (extended (endpoints i).2).1 at h
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
    exact compatible_extension state previous valid endpoints centers sources linked bounds coherent overlap

end Yulang.GeneralNominalSourceCompatibility180
