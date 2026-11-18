import Yulang.GeneralNominalOrderedJournalExpansion249
import Yulang.GeneralNominalOrderedSupport248
import Yulang.GeneralPresenceOrderedPrepared247
import Yulang.GeneralNominalVersionedHistoryNormalization238
/-! Executable preparation of the actual versioned historical ledger. Existing
full journal models supply the old block; no extra old-equation premise is
needed on this source domain. Fresh successor production remains separate. -/
namespace Yulang.GeneralNominalVersionedPreparedHistory249
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSeedLedger237 (entries Recorded)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedPrepared247 GeneralPresenceOrderedSort247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247
open CommonNominalFullCarrier

theorem ranked (state : State roles) : Ranked (fun n => n) (entries state) := by
 intro entry member dependency _ read
 exact GeneralNominalVersionedHistoryEquations237.descending state entry member dependency.1
   (GeneralNominalOrderedSupport248.typed_reads_subset entry.2 read)

theorem prepares (state : State roles) :
 ∃ sorted, prepare (entries state) = some sorted ∧ SafeOrder sorted :=
 prepare_complete (fun n => n) (entries state) (ranked state)

theorem historical_block (state : State roles) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models state assignment) : All model assignment (block (entries state)) := by
 intro atom member
 obtain ⟨entry,present,member⟩ := List.mem_flatMap.mp member
 exact GeneralNominalVersionedHistoryNormalization238.historical_equations valid entry present atom member

theorem sorted_block (state : State roles) (recorded : Recorded state) (sorted : List (Entry Nat))
 (success : prepare (entries state) = some sorted) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models state assignment) : All model assignment (block sorted) :=
 (prepared_models model assignment (entries state) sorted
   (GeneralNominalVersionedHistoryEquations237.coherent recorded) success).mpr
   (historical_block state assignment valid)

theorem source_sorted_block (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (sorted : List (Entry Nat)) (success : prepare (entries state) = some sorted) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models state assignment) : All model assignment (block sorted) :=
 sorted_block state (GeneralNominalVersionedMixedSeedLedger237.reachable reachable) sorted success assignment valid

theorem source_public_models_iff (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (sorted fresh : List (Entry Nat)) (success : prepare (entries state) = some sorted)
 (freshSafe : SafeOrder fresh)
 (protectedJournal : GeneralNominalOrderedJournalExpansion249.Protected state sorted fresh)
 (consumers : List (Atom Nat))
 (protectedConsumers : GeneralPresenceOrderedExpansion249.Protected sorted fresh consumers)
 (shared : Nat → Prop)
 (oldPrivate : ∀ name, shared name → ∀ entry ∈ sorted, entry.1 ≠ name)
 (freshPrivate : ∀ name, shared name → ∀ entry ∈ fresh, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, GeneralNominalVersionedJournal232.Models state assignment ∧
   All model assignment consumers ∧ Agrees model shared assignment boundary) ↔
 (∃ assignment, (GeneralNominalRebaseJournalView243.compile state (mapping sorted)).Models assignment ∧
   All model assignment (rewrite sorted consumers ++ block fresh) ∧ Agrees model shared assignment boundary) := by
 have result := GeneralNominalOrderedJournalExpansion249.public_models_iff state
   (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reachable) sorted fresh
   (prepared_safe (entries state) sorted success) freshSafe protectedJournal consumers protectedConsumers
   shared oldPrivate freshPrivate boundary
 constructor
 · rintro ⟨assignment,valid,ordinary,agree⟩
   exact result.mp ⟨assignment,valid,(all_append model assignment _ _).mpr
     ⟨ordinary,source_sorted_block state reachable sorted success assignment valid⟩,agree⟩
 · intro valid
   obtain ⟨assignment,journal,ordinary,agree⟩ := result.mpr valid
   exact ⟨assignment,journal,((all_append model assignment _ _).mp ordinary).1,agree⟩
end Yulang.GeneralNominalVersionedPreparedHistory249
