import Yulang.GeneralNominalVersionedPreparedHistory249
import Yulang.GeneralNominalMaterializedSequenceModels249
/-! Actual reachable source snapshots initializeFrame finite owner frames without
adding new historical constraints. Future source-step simulation is separate. -/
namespace Yulang.GeneralNominalSourceOwnerFrame249
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSeedLedger237 (entries)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedPrepared247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedRebase247
open GeneralNominalMaterializedDomain249
open GeneralNominalMaterializedOwnerFrame249 (Frame Formed)
open GeneralNominalMaterializedSequence249 (run)
open GeneralNominalMaterializedSequenceModels249 (PublicModels)
open CommonNominalFullCarrier

noncomputable def sourceFrame (state : State roles) (sorted : List (Entry Nat)) (consumers : List (Atom Nat)) : Frame :=
 ⟨GeneralNominalRebaseJournalView243.compile state CompTerm.var,consumers,sorted⟩

theorem identity_read (assignment : Assignment) :
 GeneralNominalRebaseRawView243.read CompTerm.var assignment = assignment := rfl

theorem source_formed (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (sorted : List (Entry Nat)) (success : prepare (entries state) = some sorted) (consumers : List (Atom Nat)) :
 Formed (sourceFrame state sorted consumers) :=
 ⟨Materialized.source state (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reachable) CompTerm.var,
 prepared_safe (entries state) sorted success⟩

theorem source_models_iff (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (sorted : List (Entry Nat)) (success : prepare (entries state) = some sorted)
 (consumers : List (Atom Nat)) (assignment : Assignment) :
 GeneralNominalMaterializedOwnerFrame249.Models (sourceFrame state sorted consumers) assignment ↔
 GeneralNominalVersionedJournal232.Models state assignment ∧ All model assignment consumers := by
 change (GeneralNominalRebaseJournalView243.compile state CompTerm.var).Models assignment ∧
   All model assignment (consumers ++ block sorted) ↔ _
 rw [GeneralNominalRebaseJournalView243.compile_exact state
   (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reachable),identity_read]
 constructor
 · rintro ⟨valid,ordinary⟩
   exact ⟨valid,((all_append model assignment _ _).mp ordinary).1⟩
 · rintro ⟨valid,ordinary⟩
   exact ⟨valid,(all_append model assignment _ _).mpr
     ⟨ordinary,GeneralNominalVersionedPreparedHistory249.source_sorted_block state reachable sorted success assignment valid⟩⟩

theorem source_run_models_iff (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (sorted : List (Entry Nat)) (success : prepare (entries state) = some sorted)
 (consumers : List (Atom Nat)) (blocks : List (List (Entry Nat)))
 (safe : ∀ block ∈ blocks, SafeOrder block)
 (within : ∀ block ∈ blocks, TargetsWithin block sorted)
 (shared : Nat → Prop) (privateNames : ∀ name, shared name → ∀ entry ∈ sorted, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, GeneralNominalVersionedJournal232.Models state assignment ∧
   All model assignment consumers ∧ Agrees model shared assignment boundary) ↔
 PublicModels (run (sourceFrame state sorted consumers) blocks) shared boundary := by
 have result := GeneralNominalMaterializedSequenceModels249.run_models_iff
   (sourceFrame state sorted consumers) (source_formed state reachable sorted success consumers)
   blocks safe within shared privateNames boundary
 constructor
 · rintro ⟨assignment,valid,ordinary,agree⟩
   exact result.mp ⟨assignment,(source_models_iff state reachable sorted success consumers assignment).mpr ⟨valid,ordinary⟩,agree⟩
 · intro valid
   obtain ⟨assignment,valid,agree⟩ := result.mpr valid
   obtain ⟨journal,ordinary⟩ := (source_models_iff state reachable sorted success consumers assignment).mp valid
   exact ⟨assignment,journal,ordinary,agree⟩
noncomputable def initializeFrame (state : State roles) (consumers : List (Atom Nat)) : Option Frame :=
 (prepare (entries state)).map (fun sorted => sourceFrame state sorted consumers)

theorem initialize_success (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (consumers : List (Atom Nat)) :
 ∃ frame, initializeFrame state consumers = some frame ∧ Formed frame ∧
   ∀ assignment, GeneralNominalMaterializedOwnerFrame249.Models frame assignment ↔
     GeneralNominalVersionedJournal232.Models state assignment ∧ All model assignment consumers := by
 obtain ⟨sorted,success,_⟩ := GeneralNominalVersionedPreparedHistory249.prepares state
 refine ⟨sourceFrame state sorted consumers,?_,source_formed state reachable sorted success consumers,?_⟩
 · simp only [initializeFrame,success,Option.map_some]
 · exact source_models_iff state reachable sorted success consumers

theorem mixed_of_point (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state) :
 B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state := by
 obtain ⟨initial,source,path⟩ := reachable
 exact ⟨initial,source,GeneralNominalPointErasure240.steps_old path⟩

theorem point_initialize_success (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state)
 (consumers : List (Atom Nat)) :
 ∃ frame, initializeFrame state consumers = some frame ∧ Formed frame ∧
   ∀ assignment, GeneralNominalMaterializedOwnerFrame249.Models frame assignment ↔
     GeneralNominalVersionedJournal232.Models state assignment ∧ All model assignment consumers :=
 initialize_success state (mixed_of_point state reachable) consumers
end Yulang.GeneralNominalSourceOwnerFrame249
