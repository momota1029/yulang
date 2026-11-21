import Yulang.GeneralVersionedHistoricalTransport312

set_option backward.isDefEq.respectTransparency false
/-! Executable lookup for the exact historical-ID premise. The current entry's
term need not be compared by the checker; the seed/slot invariants prove it. -/
namespace Yulang.GeneralVersionedProtectedLookup312
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered entries)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralVersionedProtectedPeer312 (Raw semanticPool completed)
open GeneralNominalVersionedPlans231 (HeadModels)
open GeneralNominalSaturationState (Packet)

def verify (pool : List Nat) (state : State roles) (p : Packet roles) : Bool :=
  (packetEntries p).all fun entry =>
    if pool.contains entry.1 then (entries state).any (fun prior => prior.1 == entry.1) else true

theorem verify_iff (pool : List Nat) (state : State roles) (p : Packet roles) :
    verify pool state p = true ↔ IdCovered pool state p := by
  unfold verify IdCovered
  rw [List.all_eq_true]
  constructor
  · intro passed entry member inside
    have hit := passed entry member
    have yes : pool.contains entry.1 = true := List.contains_iff_mem.mpr inside
    simp only [yes,ite_true,List.any_eq_true,beq_iff_eq] at hit
    obtain ⟨prior,found,target⟩ := hit
    obtain ⟨plan,recorded,entryMember⟩ := List.mem_flatMap.mp found
    exact ⟨plan,recorded,prior,entryMember,target⟩
  · intro covered entry member
    by_cases inside : entry.1 ∈ pool
    · obtain ⟨plan,recorded,prior,entryMember,target⟩ := covered entry member inside
      have yes : pool.contains entry.1 = true := List.contains_iff_mem.mpr inside
      simp only [yes,ite_true,List.any_eq_true,beq_iff_eq]
      exact ⟨prior,List.mem_flatMap.mpr ⟨plan,recorded,entryMember⟩,target⟩
    · have no : pool.contains entry.1 = false := by simpa using inside
      simp only [no,Bool.false_eq_true,ite_false]

theorem checked_head {state : State roles} {p : Packet roles}
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (current : p.context = state.core.erased.current.context)
    (valid : Models state m) (raw : Raw p m) (checked : verify (semanticPool p) state p = true) :
    HeadModels p (completed p m) :=
  GeneralVersionedProtectedPeer312.complete_on_trace path current valid raw ((verify_iff ..).mp checked)

end Yulang.GeneralVersionedProtectedLookup312
