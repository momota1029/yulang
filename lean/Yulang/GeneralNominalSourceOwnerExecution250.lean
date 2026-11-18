import Yulang.GeneralNominalOwnerExecution250
import Yulang.GeneralNominalSourceOwnerFrame249
/-! Reachable mixed source snapshots feed the finite checked owner executor
without adding an old-block assumption to source Models. Command generation,
stable-key packet production, source Step simulation and Acc remain separate. -/
namespace Yulang.GeneralNominalSourceOwnerExecution250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalSourceOwnerFrame249 (sourceFrame)
open GeneralNominalOwnerOpening250 (choose openFrame)
open GeneralNominalOwnerExecution250 (program seedAssignment result)
open GeneralNominalInstallCoverage250 (OwnerCommand)
open GeneralNominalFiniteInstallTrace250 (Permitted)
open GeneralNominalMaterializedSequenceModels249 (PublicModels)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedPrepared247
open GeneralPresenceOrderedRebase247
open CommonNominalFullCarrier

theorem source_public_execution_iff (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry sourceRoot state)
 (sorted : List (Entry Nat))
 (success : prepare (GeneralNominalVersionedMixedSeedLedger237.entries state) = some sorted)
 (consumers : List (Atom Nat)) (root declaration : Nat) (names shared : List Nat) (source : List OwnerCommand)
 (oldPrivate : ∀ name ∈ shared, ∀ entry ∈ sorted, entry.1 ≠ name) (boundary : Assignment) :
 let frame := sourceFrame state sorted consumers
 let handle := choose frame root declaration names shared
 (∃ assignment, GeneralNominalVersionedJournal232.Models state assignment ∧ All model assignment consumers ∧
   Permitted (openFrame frame handle) (program handle source) (seedAssignment handle assignment) ∧
   Agrees model (fun name => name ∈ shared) assignment boundary) ↔
 PublicModels (result frame handle source) (fun name => name ∈ shared) boundary := by
 dsimp only
 have equivalent := GeneralNominalOwnerExecution250.public_execution_iff (sourceFrame state sorted consumers)
   (prepared_safe _ _ success) root declaration names shared source oldPrivate boundary
 simpa only [GeneralNominalSourceOwnerFrame249.source_models_iff state reachable sorted success,and_assoc] using equivalent

theorem source_checked_success (state : State roles) (sorted : List (Entry Nat))
 (success : prepare (GeneralNominalVersionedMixedSeedLedger237.entries state) = some sorted)
 (consumers : List (Atom Nat)) (root declaration : Nat) (names shared : List Nat) (source : List OwnerCommand) :
 let frame := sourceFrame state sorted consumers
 let handle := choose frame root declaration names shared
 GeneralNominalCheckedInstall250.run (openFrame frame handle) (program handle source) = some (result frame handle source) :=
 GeneralNominalOwnerExecution250.checked_success _ (prepared_safe _ _ success) root declaration names shared source
end Yulang.GeneralNominalSourceOwnerExecution250
