import Yulang.GeneralVersionRowsPacket259
import Yulang.GeneralDictionaryVersionLoopIteration239
namespace Yulang.GeneralVersionRowsStages259
open GeneralVersionRowsRaw259 (withRows)
open GeneralDictionaryVersionLoopBook239 (plan atoms allocations reservations context)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralNominalVersionedJournal232 (Models)
variable (rows : Nat → Common.Row)

theorem atoms_valid (n : Nat) : PresenceNormalForm.All CommonNominalFullCarrier.model (withRows rows) (atoms n) := by
 induction n with
 | zero => intro _ member; cases member
 | succ n ih =>
   have full := GeneralVersionRowsPacket259.packet_holds rows n (allocations n) (reservations n) (atoms n) ih
   have replay := (GeneralNominalVersionedInstallation231.replay_holds_iff (plan n) (withRows rows)).mpr full
   exact replay.1.2.2

theorem packet_holds (n : Nat) : GeneralNominalVersionedPlans231.Holds (plan n) (withRows rows) :=
 GeneralVersionRowsPacket259.packet_holds rows n _ _ _ (atoms_valid rows n)

theorem initial_raw : GeneralNominalState.Models GeneralDictionaryVersionLoopSource237.snapshot (withRows rows) := by
 have raw := GeneralVersionRowsRaw259.raw_models rows 0 (allocations 0) (reservations 0) (atoms 0) (atoms_valid rows 0)
 change GeneralNominalState.Models (context 0).state (withRows rows) at raw
 rw [GeneralDictionaryVersionLoopBook239.context_zero] at raw
 exact raw

theorem all_stages (n : Nat) : Models (state n) (withRows rows) := by
 induction n with
 | zero =>
   apply (GeneralNominalVersionedJournal232.initial_models ..).mpr
   exact ⟨initial_raw rows,fun _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩
 | succ n ih =>
   exact GeneralDictionaryVersionLoopRound239.models_general (stages n).shape (stages n).recorded
     (withRows rows) ih (packet_holds rows n)
end Yulang.GeneralVersionRowsStages259
