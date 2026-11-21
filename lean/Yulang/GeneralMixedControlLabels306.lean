import Yulang.GeneralMixedControlRank306

namespace Yulang.GeneralMixedControlLabels306
open GeneralMixedControlMask306
open GeneralMixedControlLiveness306
open GeneralMixedControlBisim306 (is_equal_of_bits Observe)
open GeneralDictionaryOutputDepth252 (root registry roles)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseDepthPathRank285 (ActualPath)

def LabelBisim (R : Mask → Mask → Prop) : Prop :=
  ∀ x y q, R x y →
    (∀ x', fire q x x' = true → ∃ y', fire q y y' = true ∧ R x' y') ∧
    (∀ y', fire q y y' = true → ∃ x', fire q x x' = true ∧ R x' y')

theorem any_label_bisim_is_equality {R : Mask → Mask → Prop} (bisim : LabelBisim R)
    (x y : Mask) (same : R x y) : x = y := by
  apply is_equal_of_bits
  intro q
  have enabled : get x q = false ↔ get y q = false := by
    constructor
    · intro missing
      obtain ⟨later,step,_⟩ := (bisim x y q same).1 full ((full_triggers x q).mpr missing)
      exact ((fire_exact q y later).mp step).2.1
    · intro missing
      obtain ⟨next,step,_⟩ := (bisim x y q same).2 full ((full_triggers y q).mpr missing)
      exact ((fire_exact q x next).mp step).2.1
  cases hx : get x q <;> cases hy : get y q <;> simp [hx,hy] at enabled ⊢

theorem rank_not_label_exact :
    rank onlyZero = rank onlyOne ∧
    fire 0 onlyZero full = false ∧ fire 0 onlyOne full = true ∧
    fire 1 onlyZero full = true ∧ fire 1 onlyOne full = false := by decide

theorem labelled_agreement_exact {s t : State roles} {ns nt : Nat}
    (p : ActualPath installed s ns) (q : ActualPath installed t nt) :
    (∀ i : Fin 2, (∃ u, Observe i s u) ↔ (∃ u, Observe i t u)) ↔ project s = project t := by
  constructor
  · intro same
    apply is_equal_of_bits
    intro i
    have both := (label_enabled (GeneralMixedControlAtoms306.reach_facts p) i).symm.trans
      ((same i).trans (label_enabled (GeneralMixedControlAtoms306.reach_facts q) i))
    cases hs : get (project s) i <;> cases ht : get (project t) i <;> simp [hs,ht] at both ⊢
  · intro same i
    rw [label_enabled (GeneralMixedControlAtoms306.reach_facts p),
      label_enabled (GeneralMixedControlAtoms306.reach_facts q),same]

end Yulang.GeneralMixedControlLabels306
