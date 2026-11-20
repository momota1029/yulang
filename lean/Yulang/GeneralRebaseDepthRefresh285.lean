import Yulang.GeneralRebaseDepthView285
import Yulang.GeneralNominalOutputGrowth
import Yulang.GeneralDictionaryGroundCopy218Refresh

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralRebaseDepthRefresh285
open GeneralDictionaryOutputDepth252 (model P F S)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralNominalOutputGrowth (tower tower_equivalent)
open GeneralNominalSupport (Head)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (FitsAll Descriptor Parameter)
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_nominal tagged_test tagged_scalar)
open CommonNominalFullCarrier (Subtype Equivalent subtype_trans Ty)
open GeneralNominalVersionedMixedObservations233 (Refresh cache_sound)
open GeneralNominalRecursiveInspection (Test)

theorem scalar_not_middle : ¬ Subtype (tower 0) (tower 2) := by
  intro le
  exact nomatch (tag_subtype (tagged_scalar .int) (tagged_nominal 0 [.inl (tower 1)]) le)

theorem first_not_middle : ¬ Subtype (tower 1) (tower 2) := by
  intro le
  have same := ((CommonNominalFullCarrier.nominal_regular_invariant_exact ..).mp le).2.2 0
    (.inl (tower 0)) (.inl (tower 1)) rfl rfl
  exact (by decide : (0 : Nat) ≠ 1) ((tower_equivalent 0 1).mp same)

theorem third_not_middle : ¬ Subtype (tower 3) (tower 2) := by
  intro le
  have same := ((CommonNominalFullCarrier.nominal_regular_invariant_exact ..).mp le).2.2 0
    (.inl (tower 2)) (.inl (tower 1)) rfl rfl
  exact (by decide : (2 : Nat) ≠ 1) ((tower_equivalent 2 1).mp same)

theorem no_lower_slot (n : Nat) : ¬ Subtype (model n).1 (tower 2) := by
  cases n with
  | zero => exact scalar_not_middle
  | succ n =>
    cases n with
    | zero => exact scalar_not_middle
    | succ n =>
      cases n with
      | zero => exact first_not_middle
      | succ n =>
        cases n with
        | zero => exact third_not_middle
        | succ n => exact first_not_middle

theorem nominal_unrepresentable (snap : GeneralNominalState.State)
    (slot : Fin snap.base.slots) (d : Descriptor snap.base.slots)
    (atSlot : (model (snap.base.source slot)).1 = P)
    (denotes : GeneralNominalState.Denotes snap.base model slot d) : False := by
  obtain ⟨vs,fits,equiv⟩ := denotes
  rw [atSlot] at equiv
  have inv := (CommonNominalFullCarrier.nominal_regular_invariant_exact 0 d.declaration.name
    [.inl (tower 2)] vs).mp equiv.1
  have len : vs.length = 1 := inv.2.1.symm
  cases vs with
  | nil => cases len
  | cons value values =>
    have tail_nil : values = [] := List.length_eq_zero_iff.mp (by simpa only [List.length_cons, Nat.succ.injEq] using len)
    subst values
    have d_len : d.arguments.length = 1 :=
      (GeneralNominalLinearMaterializationFacts.fitsAll_length _ _ _ _ fits).symm.trans len
    cases args : d.arguments with
    | nil => rw [args] at d_len; cases d_len
    | cons param params =>
      have zero : d.arguments[0]? = some param := args ▸ rfl
      obtain ⟨v,found,fitsHead⟩ :=
        GeneralNominalIntervalLaws.fitsAll_at _ _ _ _ fits 0 param zero
      have same := inv.2.2 0 (.inl (tower 2)) v rfl found
      cases v with
      | inr row => exact same
      | inl ty =>
        cases param with
        | row bounds => exact fitsHead
        | type bounds => exact no_lower_slot _ (subtype_trans fitsHead.1 same.2)

theorem no_certified_deep_head_of_model
    (state : GeneralNominalVersionedJournal232.State roles)
    (valid : GeneralNominalVersionedJournal232.Models state model)
    (snap : GeneralNominalState.State)
    (cert : GeneralNominalVersionedMixedObservations233.CacheSound state snap)
    {identity : Nat} (atId : (model identity).1 = P) :
    ¬ GeneralNominalState.Known snap identity := by
  intro known
  obtain ⟨test,observ,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have held := cache_sound cert (GeneralNominalSupport.head_recorded head) valid
  have tested := GeneralDictionaryGroundCopy218Refresh.head_holds head held
  have tag := tagged_test test tested
  rw [atId] at tag
  have requirement := tag_subtype tag (tagged_nominal 0 [.inl (tower 2)])
    (CommonNominalFullCarrier.subtype_refl _)
  cases head with
  | scalar slot base found => cases requirement
  | structural slot kind children found =>
    cases shape : snap.view.shapes kind <;>
      simp [shape,GeneralNominalFiniteHeadInversion.head] at requirement
  | nominal slot desc found => exact nominal_unrepresentable snap slot desc atId held

theorem no_refresh_at_output (target : GeneralNominalCandidates.Context)
    (cert : Refresh installed target) :
    ¬ GeneralNominalState.Known target.state 3 :=
  no_certified_deep_head_of_model installed installed_model target.state cert.cache rfl

end Yulang.GeneralRebaseDepthRefresh285
