import Yulang.GeneralNominalFramedExtension181

/-! Finite nominal extension relative to any proved model frame.
The predicate may include both a core journal and historical/live effects.
The finite observation criterion is unchanged; no general evidence is asserted. -/
namespace Yulang.GeneralNominalPredicateExtension182
open GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenteredModelExtension
open GeneralNominalCenteredFrame179 (Agree)

open GeneralNominalFramedExtension181 (chooseModel chooseModel_kept chooseModel_readback)

private theorem equivalent_trans (one : Equivalent a b) (two : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans one.1 two.1, subtype_trans two.2 one.2⟩

theorem compatible_extension (P : Assignment → Prop) (support : List Nat)
    (frame : ∀ first last, Agree support first last →
      P first → P last)
    (arguments : Fin count → NominalArgument) (previous : Assignment)
    (valid : P previous) (values : Fin count → Ty)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ support ∧
      (arguments i).argument.endpoints.2 ∈ support ∧
      originSource (arguments i).origin ∈ support)
    (observed : ∀ i, (∃ actual, Observes previous (arguments i).origin actual) ∧
      ∀ actual, Observes previous (arguments i).origin actual → Equivalent actual (values i))
    (bounds : ∀ i, GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints (values i))
    (coherent : ∀ i j, (arguments i).argument.center = (arguments j).argument.center →
      Equivalent (values i) (values j))
    (overlap : ∀ i, (arguments i).argument.center ∈ support →
      Equivalent (values i) (previous (arguments i).argument.center).1) :
    ∃ extended, P extended ∧
      (∀ name ∈ support, extended name = previous name) ∧
      ∀ i, (arguments i).Holds extended := by
  let centers := fun i => (arguments i).argument.center
  let extended := chooseModel support previous centers values
  have kept (name) (member : name ∈ support) : extended name = previous name :=
    chooseModel_kept support previous centers values member
  have readback i : Equivalent (values i) (extended (arguments i).argument.center).1 :=
    chooseModel_readback support previous centers values coherent overlap i
  refine ⟨extended,frame previous extended
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

theorem extension_iff (P : Assignment → Prop) (support : List Nat)
    (frame : ∀ first last, Agree support first last →
      P first → P last)
    (arguments : Fin count → NominalArgument) (previous : Assignment)
    (valid : P previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ support ∧
      (arguments i).argument.endpoints.2 ∈ support ∧
      originSource (arguments i).origin ∈ support) :
    (∃ extended, P extended ∧
      (∀ name ∈ support, extended name = previous name) ∧
      ∀ i, (arguments i).Holds extended) ↔
    (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
    (∀ i actual, Observes previous (arguments i).origin actual →
      GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
    (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
      Observes previous (arguments i).origin first → Observes previous (arguments j).origin last →
      Equivalent first last) ∧
    (∀ i actual, (arguments i).argument.center ∈ support →
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
    apply compatible_extension P support frame arguments previous valid values linked
    · intro i
      exact ⟨inhabited i,fun actual observed => coherent i i actual (values i) rfl observed (seen i)⟩
    · exact fun i => bounds i (values i) (seen i)
    · exact fun i j same => coherent i j (values i) (values j) same (seen i) (seen j)
    · exact fun i member => overlap i (values i) member (seen i)

end Yulang.GeneralNominalPredicateExtension182
