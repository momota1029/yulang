import Yulang.GeneralRebaseRowLeafMark288
import Yulang.GeneralRebaseLeafLedger288

/-! Materialization into the old ledger, only as static state data. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralRebaseRowLedger288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (plan child sole_child)
open GeneralRebaseRowParentFrame287 (after effect after_model)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseRowLeafWitness288 (leaf source_exact)
open GeneralRebaseRowLeafSlice288 (prior finalFacts same_models)
open GeneralRebaseRowSemanticMark287 (marked target refines all_models_support known_output)
open GeneralRebaseLeafLedger288 (record)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedSupport233 (Trusted PacketSettled Discharged)
open GeneralNominalVersionedMixedObservations233 (CacheSound Refresh)
open GeneralNominalCommonBridge (Assignment)

noncomputable abbrev supplemented : State roles := record (after true) GeneralRebaseRowWholeChild287.plan

theorem layouts :
    supplemented.core = (after true).core ∧ supplemented.effects = (after true).effects ∧
      supplemented.plans = [GeneralRebaseRowWholeChild287.plan,plan true] := ⟨rfl,rfl,rfl⟩

theorem models_eq (m : Assignment) : Models supplemented m ↔ Models (after true) m :=
  GeneralRebaseLeafLedger288.record_models leaf m

theorem old_child : Discharged supplemented (child true) :=
  GeneralRebaseLeafLedger288.recorded_child leaf

theorem old_parent : PacketSettled supplemented (plan true) :=
  GeneralRebaseLeafLedger288.singleton_settlement leaf (List.mem_singleton_self _) (sole_child true)

theorem old_trusted_output : Trusted supplemented (finalFacts true) :=
  GeneralRebaseLeafLedger288.old_trust_in_static_ledger
    ((GeneralRebaseRowLeafSlice288.extension_iff true).mpr rfl) leaf (sole_child true)

theorem old_cache : CacheSound supplemented (marked true) := by
  apply GeneralNominalVersionedMixedObservations233.versioned_cache
  intro obs recorded
  refine ⟨finalFacts true,old_trusted_output,?_⟩
  intro m slice
  exact GeneralCanonicalObservations.recorded_sound _ m
    (all_models_support true m ((same_models true m).mp slice)) recorded

noncomputable def old_refresh : Refresh supplemented (target true) where
  refines := refines true
  interpretation := rfl
  support := fun _ h => h
  constraints := fun m valid =>
    let raw := all_models_support true m ((models_eq m).mp valid)
    ⟨raw.1,raw.2.2⟩
  cache := old_cache

theorem terminal_current_cache (choice : Bool) : CacheSound (after choice) (current choice).state := by
  apply GeneralNominalVersionedMixedObservations233.versioned_cache
  intro obs seen
  refine ⟨[],.source,?_⟩
  intro m valid
  exact GeneralCanonicalObservations.recorded_sound _ m
    ((GeneralRebaseRowTrustedBoundary287.raw_after choice m).mpr ((source_exact choice m).mp valid)) seen

theorem unknown_output (choice : Bool) : ¬ GeneralNominalState.Known (current choice).state 2 :=
  GeneralRebaseRowTrustedBoundary287.forbidden_known choice _ (terminal_current_cache choice) 2 (by decide)

end Yulang.GeneralRebaseRowLedger288
