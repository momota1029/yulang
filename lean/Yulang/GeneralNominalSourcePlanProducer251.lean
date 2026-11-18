import Yulang.GeneralNominalPlanProducer251
import Yulang.GeneralNominalSourceOwnerFrame249
namespace Yulang.GeneralNominalSourcePlanProducer251
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCenters (Plan)
open GeneralNominalMaterializedOwnerFrame249 (Frame Formed Models)
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration PresenceNormalForm
open CommonNominalFullCarrier

theorem initialize_and_install (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (consumers : List (Atom Nat)) (plan : Plan roles) (protectedNames : List Nat) :
 ∃ frame : Frame, GeneralNominalSourceOwnerFrame249.initializeFrame state consumers = some frame ∧
 Formed frame ∧
 GeneralNominalCheckedInstall250.step (GeneralNominalPlanProducer251.opened plan frame protectedNames)
   (GeneralNominalPlanProducer251.command plan frame protectedNames) =
   some (GeneralNominalPlanProducer251.result plan frame protectedNames) ∧
 ∀ assignment : Assignment, GeneralNominalVersionedJournal232.Models state assignment →
 All model assignment consumers →
 (Models (GeneralNominalPlanProducer251.result plan frame protectedNames)
   (GeneralNominalPlanProducer251.finalAssignment plan frame protectedNames assignment) ↔
 GeneralNominalRolePacket251.Holds plan (GeneralNominalPlanProducer251.env plan frame protectedNames)
   (GeneralNominalPlanProducer251.reference plan frame protectedNames assignment)
   (GeneralNominalPlanProducer251.finalAssignment plan frame protectedNames assignment)) := by
 obtain ⟨frame,initialized,formed,exactModels⟩ :=
   GeneralNominalSourceOwnerFrame249.initialize_success state reachable consumers
 refine ⟨frame,initialized,formed,GeneralNominalPlanProducer251.checked_success plan frame formed.2 protectedNames,?_⟩
 intro assignment source ordinary
 exact GeneralNominalPlanProducer251.install_exact plan frame formed.2 protectedNames assignment
   ((exactModels assignment).mpr ⟨source,ordinary⟩)
end Yulang.GeneralNominalSourcePlanProducer251
