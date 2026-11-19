import Yulang.GeneralRebaseVersionMicro278

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseVersionPrivate278
open GeneralDictionaryVersionLoopSource237 (roles model declaration F S)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralDictionaryVersionLoopBook239 (allocations reservations atoms plan packet)
open GeneralDictionaryVersionLoopNames238 (lower upper upper_above)
open GeneralDictionaryVersionLoopFamilyNovel239 (bad)
open GeneralDictionaryVersionLoopPacket237 (actual actual_value)
open GeneralRebaseVersionMicro278 (installed refreshed)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem installed_exact (n : Nat) (m : Assignment) :
    Models (installed n) m ↔ Models (state n) m ∧ Holds (plan n) m := by
  constructor
  · intro valid
    exact ⟨GeneralNominalVersionedMixedKernel234.step_models
      (GeneralRebaseVersionMicro278.install_step n) valid,valid.2.1 _ List.mem_cons_self⟩
  · rintro ⟨valid,packetValid⟩
    exact (GeneralNominalVersionedInstall232.install_models rfl).mpr
      (GeneralDictionaryVersionLoopInstall239.common_general (stages n).shape m valid packetValid)

theorem refreshed_exact (n : Nat) (m : Assignment) :
    Models (refreshed n) m ↔ Models (installed n) m :=
  GeneralNominalVersionedMixedObservations233.refresh_models
    (GeneralDictionaryVersionLoopFamilyRefresh238.certificate allocations reservations atoms (installed n) n
      (stages n).shape.source rfl
      (GeneralDictionaryVersionLoopInstall239.installed_recorded (stages n).shape (stages n).recorded))

theorem reobserved_exact (n : Nat) (m : Assignment) :
    Models (state (n+1)) m ↔ Models (refreshed n) m :=
  GeneralNominalVersionedMixedObservations233.reobserve_models
    (GeneralDictionaryVersionLoopFamilyReobserve238.certificate allocations reservations atoms (installed n) n
      (stages n).shape.source
      (GeneralDictionaryVersionLoopInstall239.installed_recorded (stages n).shape (stages n).recorded))

theorem bad_not_packet (n : Nat) : ¬ Holds (plan n) (bad n) := by
  intro held
  have fits := GeneralNominalVersionedPlans231.shared_center held.2.1 (name := 0)
    (Or.inl (by change 0 ∈ declaration.inputNames; decide +kernel))
  rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryVersionLoopFamilyFull238.binder_exact] at fits
  change GeneralNominalCaptureMerges.Fits (bad n)
    ((GeneralNominalVersionedAllocation231.capture _ _ _ _ (packet n).bindings).inputs 0) (bad n actual).1 at fits
  rw [GeneralDictionaryVersionLoopFamilyPacket238.bindings_exact] at fits
  change Subtype (bad n (lower (n+1))).1 (bad n actual).1 ∧
    Subtype (bad n actual).1 (bad n (upper n)).1 at fits
  have ne : actual ≠ upper n := Ne.symm
    (GeneralNominalAggregateVersion231.not_legacy_slot 3 0 0 1 0 _ 0 0 8 0)
  have center : (bad n actual).1 = F := by simp only [bad,ne,ite_false,actual_value]
  have bound : (bad n (upper n)).1 = .bottom := by simp only [bad,ite_true]
  rw [center,bound] at fits
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.nominal 0 1)
    ⟨[.inl S],rfl,(by
      intro depth
      apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
      intro rank env observation accepted
      exact CommonNominalFullDemand.probeAt_bottom rank observation),fits.2⟩

theorem bad_agrees (n : Nat) : GeneralVersionBoundaryCompletion259.Agree (bad n) model := by
  constructor
  · intro id small
    have outside : id ≠ upper n := by
      have high := upper_above n
      omega
    simp only [bad,outside,ite_false]
  · intro id
    unfold bad
    split <;> rfl

theorem raw_strict (n : Nat) :
    Models (state n) (bad n) ∧ ¬ Models (installed n) (bad n) ∧
    GeneralVersionBoundaryCompletion259.Agree (bad n) model :=
  ⟨(stages n).future n (Nat.le_refl _),
    fun next => bad_not_packet n ((installed_exact n _).mp next).2,bad_agrees n⟩

theorem later_bad (n : Nat) : ¬ Models (state (n+1)) (bad n) :=
  fun valid => (raw_strict n).2.1 ((refreshed_exact n _).mp ((reobserved_exact n _).mp valid))

end Yulang.GeneralRebaseVersionPrivate278
