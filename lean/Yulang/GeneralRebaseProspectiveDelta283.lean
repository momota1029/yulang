import Yulang.GeneralRebaseIncrementalHistory283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseProspectiveDelta283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedInstall232 (install InstallationModels install_models)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded entries)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralRebaseProspective282 (recorded_install members acceptance_before)
open GeneralRebaseHistoryOrder282 (history decode ordered)
open GeneralNominalAcyclicEquations237 (Coherent Descending)
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseIncrementalHistory283 (changes update)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {state : State roles} {effect : Effect roles}

theorem entries_append (s : State roles) (e : Effect roles) :
    entries (install s e) = packetEntries e.plan.packet ++ entries s := rfl

theorem ext_history (old : Recorded state) (snap : effect.snapshot = state.core)
    (row : Entry Nat) : row ∈ history (install state effect) ↔
      row ∈ packetEntries effect.plan.packet ∨ row ∈ history state := by
  rw [members (recorded_install old snap),entries_append,List.mem_append,members old]

theorem coherent_history (s : State roles) (recorded : Recorded s) : Coherent (history s) :=
  fun a first b last eq => GeneralNominalVersionedMixedSeedLedger237.same_entry recorded
    ((members recorded a).mp first) ((members recorded b).mp last) eq

theorem descending_history (s : State roles) (recorded : Recorded s) : Descending (history s) :=
  fun r member => GeneralNominalVersionedHistoryEquations237.descending s r ((members recorded r).mp member)

def replay (state : State roles) (effect : Effect roles) (cache : Assignment) :=
  update (history state) (history (install state effect)) cache

theorem replay_exact (old : Recorded state) (snap : effect.snapshot = state.core) (base : Assignment) :
    replay state effect (decode state base) = decode (install state effect) base := by
  apply GeneralRebaseIncrementalHistory283.exact_update
     (fun {row} h => (ext_history old snap row).mpr (Or.inr h))
     (coherent_history _ (recorded_install old snap))
     (descending_history _ (recorded_install old snap))
     (ordered state).2.2 (ordered (install state effect)).2.2

theorem reachable_exact (reach : Reachable registry root state) (snap : effect.snapshot = state.core)
    (base : Assignment) : replay state effect (decode state base) = decode (install state effect) base :=
  replay_exact (GeneralNominalVersionedMixedSeedLedger237.reachable reach) snap base

theorem old_eq_cache (reach : Reachable registry root state) (snap : effect.snapshot = state.core)
    (base : Assignment) :
    Models (install state effect) (replay state effect (decode state base)) ↔
    GeneralRebaseProspective282.Compiled (install state effect) base := by
  rw [reachable_exact reach snap,GeneralRebaseProspective282.decoded
    (GeneralRebaseProspective282.empty_install
      (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reach))]

theorem guard (reach : Reachable registry root state) (snap : effect.snapshot = state.core) :
    (∃ base, Models (install state effect) (replay state effect (decode state base))) ↔
    ∃ a, InstallationModels state effect a := by
  exact (exists_congr (old_eq_cache reach snap)).trans (acceptance_before reach snap)

theorem supports_historical_evidence (reach : Reachable registry root state)
    (snap : effect.snapshot = state.core) (base : Assignment) (r : Registry)
    (focus : Occurrence roles) (data : GeneralDictionaryReadback.Payload) :
    GeneralNominalRebaseEvidenceView243.Evidence r (install state effect).core
      (GeneralPresenceOrderedSubstitution247.mapping (history (install state effect))) base focus data ↔
      GeneralNominalVersionedEvidence231.Evidence r (install state effect).core
        (replay state effect (decode state base)) focus data := by
  rw [reachable_exact reach snap, GeneralNominalRebaseEvidenceView243.evidence_exact,
    GeneralNominalOrderedRaw248.read_mapping]
  rfl

end Yulang.GeneralRebaseProspectiveDelta283
