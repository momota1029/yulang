import Yulang.GeneralRebaseDepthPayload285

set_option maxRecDepth 22000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralRebaseDepthMinimal285
open GeneralDictionaryOutputDepth252 (S F P model)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseDepthGroundModels285 (InitialTypeCheck FinalTypeCheck final_check no_row_requirement)
open GeneralRebaseDepthPublic285 (project inflate)
open CommonNominalFullCarrier (Ty Equivalent)

abbrev badType (n : Nat) : Ty := if n ≤ 1 then F else S

def damage (n : Nat) : Assignment := fun i =>
  (if i = n then badType n else (model i).1,(model i).2)

theorem literal_agreement (n i : Nat) (different : i ≠ n) :
    (damage n i).1 = (model i).1 := by simp [damage,different]

theorem scalar_ne_foo : ¬ Equivalent S F := by
  intro held
  exact nomatch (GeneralDictionaryInspectionHeads215.tag_subtype
    (GeneralDictionaryInspectionHeads215.tagged_scalar .int)
    (GeneralDictionaryInspectionHeads215.tagged_nominal 0 [.inl S]) held.1)

theorem scalar_ne_output : ¬ Equivalent S P := by
  intro held
  exact nomatch (GeneralDictionaryInspectionHeads215.tag_subtype
    (GeneralDictionaryInspectionHeads215.tagged_scalar .int)
    (GeneralDictionaryInspectionHeads215.tagged_nominal 0 [.inl
      (CommonNominalFullCarrier.nominal 0 [.inl F])]) held.1)

theorem breaks_source (n : Nat) (small : n ≤ 2) : ¬ InitialTypeCheck (damage n) := by
  intro checked
  have bounds : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases bounds with rfl|rfl|rfl
  · exact scalar_ne_foo ⟨checked.1.2,checked.1.1⟩
  · exact scalar_ne_foo ⟨checked.2.1.2,checked.2.1.1⟩
  · exact scalar_ne_foo checked.2.2

theorem breaks_raw (n : Nat) (small : n ≤ 3) : ¬ Models installed (damage n) := by
  intro holds
  obtain ⟨source,output⟩ := (final_check _).mp holds
  by_cases input : n ≤ 2
  · exact breaks_source n input source
  · have eq : n = 3 := by omega
    subst n
    exact scalar_ne_output output

def Frames (Q : Assignment → Prop) (support : List Nat) : Prop :=
  ∀ a b, (∀ i ∈ support, (a i).1 = (b i).1) → (Q a ↔ Q b)

theorem minimal_raw (support : List Nat) :
    Frames (Models installed) support ↔ ∀ n ≤ 3, n ∈ support := by
  constructor
  · intro framed n small
    apply Classical.byContradiction
    intro omitted
    have agrees : ∀ i ∈ support, (model i).1 = (damage n i).1 :=
      fun i seen => (literal_agreement n i (fun cross => omitted (cross ▸ seen))).symm
    exact breaks_raw n small ((framed model (damage n) agrees).mp installed_model)
  · intro covers a b agrees
    exact no_row_requirement a b (fun n h => agrees n (covers n h))

def Canonical (a : Assignment) : Prop :=
    Models installed (inflate (project a) (fun n => (a n).2))

theorem minimal_canonical (support : List Nat) :
    Frames Canonical support ↔ ∀ n ≤ 2, n ∈ support := by
  constructor
  · intro framed n small
    apply Classical.byContradiction
    intro omitted
    have agrees : ∀ i ∈ support, (model i).1 = (damage n i).1 :=
      fun i seen => (literal_agreement n i (fun cross => omitted (cross ▸ seen))).symm
    have canonModel : Canonical model :=
      (GeneralRebaseDepthGroundModels285.canonical_check model).mpr ((final_check model).mp installed_model).1
    exact breaks_source n small ((GeneralRebaseDepthGroundModels285.canonical_check _).mp
      ((framed model (damage n) agrees).mp canonModel))
  · intro covers a b agrees
    show Canonical a ↔ Canonical b
    unfold Canonical
    rw [GeneralRebaseDepthGroundModels285.canonical_check,GeneralRebaseDepthGroundModels285.canonical_check]
    simp only [InitialTypeCheck,agrees 0 (covers 0 (by decide)),agrees 1 (covers 1 (by decide)),
      agrees 2 (covers 2 (by decide))]

end Yulang.GeneralRebaseDepthMinimal285
