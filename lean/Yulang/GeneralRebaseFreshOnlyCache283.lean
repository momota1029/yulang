import Yulang.GeneralRebaseCacheCounterexamples283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseFreshOnlyCache283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralRebaseInstallCache283 (Valid add forward interpret coherent)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseSortedCache283 (push push_exact)
open GeneralRebaseFreshDelta283 (onlyNew NoBackReads)
open GeneralRebaseIncrementalHistory283 (changes)
open GeneralNominalAcyclicEquations237 (Coherent)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)

def quick (old : List (Entry Nat)) (effect : Effect roles) : List (Entry Nat) :=
  push (onlyNew (old.map Prod.fst) (packetEntries effect.plan.packet)) []

def evaluate (old : List (Entry Nat)) (effect : Effect roles) (memo : Assignment) : Assignment :=
  GeneralPresenceOrderedBlock247.solve model (quick old effect) memo

variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}
  {reg : Registry} {focus : Occurrence roles} {old : List (Entry Nat)}

theorem new_packet_members (valid : Valid old state) (record : Recorded state) (snap : effect.snapshot = state.core)
    (entry : Entry Nat) :
    entry ∈ onlyNew (old.map Prod.fst) (packetEntries effect.plan.packet) ↔
      entry ∈ onlyNew (old.map Prod.fst) (add old effect) := by
  have next := GeneralRebaseInstallCache283.add_valid valid record snap
  have content : entry ∈ add old effect ↔ entry ∈ packetEntries effect.plan.packet ∨ entry ∈ old :=
    (next.content entry).trans ((GeneralRebaseProspectiveDelta283.ext_history record snap entry).trans
      (or_congr Iff.rfl (valid.content entry).symm))
  simp only [onlyNew,List.mem_filter,List.contains_eq_mem,Bool.not_eq_true',decide_eq_false_iff_not,content]
  constructor
  · exact fun h => ⟨Or.inl h.1,h.2⟩
  · exact fun h => ⟨h.1.resolve_right (fun seen => h.2 (List.mem_map.mpr ⟨entry,seen,rfl⟩)),h.2⟩

theorem quick_exact (valid : Valid old state) (record : Recorded state) (snap : effect.snapshot = state.core)
    (unread : NoBackReads (old.map Prod.fst) (add old effect)) :
    quick old effect = changes old (add old effect) := by
  have validNext := GeneralRebaseInstallCache283.add_valid valid record snap
  have noConflict := coherent validNext (GeneralRebaseProspective282.recorded_install record snap)
  have h : Coherent (onlyNew (old.map Prod.fst) (packetEntries effect.plan.packet) ++ []) := by
    simp only [List.append_nil]
    intro a one b two same
    exact noConflict a (List.mem_filter.mp ((new_packet_members valid record snap a).mp one)).1
      b (List.mem_filter.mp ((new_packet_members valid record snap b).mp two)).1 same
  obtain ⟨sorted,content⟩ := push_exact _ _ List.Pairwise.nil h
  rw [GeneralRebaseFreshDelta283.exact_changes old (add old effect) unread]
  apply GeneralRebaseCanonicalCache283.sorted_unique _ _ sorted
    (List.Pairwise.sublist List.filter_sublist validNext.increasing)
  intro row
  exact (show row ∈ quick old effect ↔ _ from content row).trans
    ((show (row ∈ _ ∨ row ∈ ([] : List (Entry Nat))) ↔ row ∈ _ from by simp only [List.not_mem_nil,or_false]).trans
      (new_packet_members valid record snap row))

theorem reads (valid : Valid old state) (seen : Reachable reg focus state) (snap : effect.snapshot = state.core)
    (unread : NoBackReads (old.map Prod.fst) (add old effect)) (base : Assignment) :
    evaluate old effect (interpret old base) = GeneralRebaseHistoryOrder282.decode (install state effect) base := by
  have record := GeneralNominalVersionedMixedSeedLedger237.reachable seen
  unfold evaluate
  rw [quick_exact valid record snap unread]
  exact GeneralRebaseInstallCache283.lookup valid record snap base

end Yulang.GeneralRebaseFreshOnlyCache283
