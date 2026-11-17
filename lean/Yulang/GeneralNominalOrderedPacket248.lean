import Yulang.GeneralNominalOrderedOrigin248
import Yulang.GeneralNominalRebasePacketView243
import Yulang.GeneralNominalVersionedPacketCongruence238

/-! Ordered readback for the actual projection report and complete compiled
packet. Existing concrete assignment congruence supplies stability, rather than
an additional assumed packet law. This does not enumerate current/history/cache
occurrences or construct a source transition or ordering producer. -/
namespace Yulang.GeneralNominalOrderedPacket248
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceModelCongruence245 GeneralPresenceOrderedRecovery247
open GeneralPresenceCommonLaws245 GeneralNominalOrderedOrigin248
open GeneralNominalCenters (Plan)

theorem assignment_same (compatible : Compatible model first last) :
 GeneralNominalAssignmentCongruence238.Same first last := compatible

theorem projection_exact (entries : List (Entry Nat)) (assignment : Assignment)
 (state : GeneralNominalState.State) (report : GeneralNominalRecursiveInspection.Report state) :
 (GeneralNominalRebaseProjectionView243.compile state (mapping entries) report).Models assignment ↔
 GeneralNominalRecursiveInspection.ProjectionModels state report (solve model entries assignment) := by
 rw [GeneralNominalRebaseProjectionView243.compile_exact,read_mapping]

theorem packet_exact (entries : List (Entry Nat)) (assignment : Assignment)
 (plan : Plan roles) :
 (GeneralNominalRebasePacketView243.compile plan (mapping entries)).Holds assignment ↔
 GeneralNominalVersionedPlans231.Holds plan (solve model entries assignment) := by
 rw [GeneralNominalRebasePacketView243.compile_exact,read_mapping]

theorem projection_recovered (entries : List (Entry Nat)) (assignment : Assignment)
 (valid : All model assignment (block entries))
 (state : GeneralNominalState.State) (report : GeneralNominalRecursiveInspection.Report state) :
 (GeneralNominalRebaseProjectionView243.compile state (mapping entries) report).Models assignment ↔
 GeneralNominalRecursiveInspection.ProjectionModels state report assignment := by
 rw [projection_exact]
 exact GeneralNominalProjectionCongruence238.projection_iff
   (assignment_same (solve_compatible model common_laws entries assignment valid)) state report

theorem packet_recovered (entries : List (Entry Nat)) (assignment : Assignment)
 (valid : All model assignment (block entries)) (plan : Plan roles) :
 (GeneralNominalRebasePacketView243.compile plan (mapping entries)).Holds assignment ↔
 GeneralNominalVersionedPlans231.Holds plan assignment := by
 rw [packet_exact]
 exact GeneralNominalVersionedPacketCongruence238.holds_iff
   (assignment_same (solve_compatible model common_laws entries assignment valid)) plan

theorem projection_rebase (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old))
 (state : GeneralNominalState.State) (report : GeneralNominalRecursiveInspection.Report state) :
 (GeneralNominalRebaseProjectionView243.compile state (mapping old) report).Models
   (solve model fresh assignment) ↔
 GeneralNominalRecursiveInspection.ProjectionModels state report assignment := by
 rw [projection_exact,solve_absorbs model old fresh safe within]
 exact GeneralNominalProjectionCongruence238.projection_iff
   (assignment_same (solve_compatible model common_laws old assignment valid)) state report

theorem packet_rebase (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) (plan : Plan roles) :
 (GeneralNominalRebasePacketView243.compile plan (mapping old)).Holds
   (solve model fresh assignment) ↔ GeneralNominalVersionedPlans231.Holds plan assignment := by
 rw [packet_exact,solve_absorbs model old fresh safe within]
 exact GeneralNominalVersionedPacketCongruence238.holds_iff
   (assignment_same (solve_compatible model common_laws old assignment valid)) plan

/- A finite family uses one and the same assignment and fresh extension for
all packets. It does not assert that an actual journal has been enumerated. -/
theorem packets_rebase (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) (plans : List (Plan roles)) :
 (∀ plan ∈ plans, (GeneralNominalRebasePacketView243.compile plan (mapping old)).Holds
   (solve model fresh assignment)) ↔
 (∀ plan ∈ plans, GeneralNominalVersionedPlans231.Holds plan assignment) := by
 exact forall_congr' fun plan => forall_congr' fun _ =>
   packet_rebase old fresh safe within assignment valid plan
end Yulang.GeneralNominalOrderedPacket248
