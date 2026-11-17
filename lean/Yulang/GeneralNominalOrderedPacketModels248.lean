import Yulang.GeneralNominalOrderedPacket248
import Yulang.GeneralPresenceOrderedRebase247

/-! One common witness for actual packets, ordinary consumers, ordered block
constraints, and public coordinates. A supplied finite list is not a proof
that every actual journal/current/history/cache occurrence was enumerated. -/
namespace Yulang.GeneralNominalOrderedPacketModels248
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceCommonLaws245 GeneralNominalOrderedPacket248
open GeneralPresenceOrderedRebase247
open GeneralNominalCenters (Plan)

theorem models_forward (old fresh : List (Entry Nat))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh) (within : TargetsWithin fresh old)
 (consumers : List (Atom Nat)) (plans : List (Plan roles)) (assignment : Assignment)
 (valid : All model assignment (consumers ++ block old))
 (packets : ∀ plan ∈ plans, GeneralNominalVersionedPlans231.Holds plan assignment) :
 All model (solve model fresh assignment) (rewrite old consumers ++ block fresh) ∧
 (∀ plan ∈ plans, (GeneralNominalRebasePacketView243.compile plan (mapping old)).Holds
   (solve model fresh assignment)) := by
 refine ⟨GeneralPresenceOrderedRebase247.models_forward model common_laws old fresh
   oldSafe freshSafe within consumers assignment valid,?_⟩
 exact (packets_rebase old fresh oldSafe within assignment
   ((all_append model assignment _ _).mp valid).2 plans).mpr packets

theorem models_backward (old fresh : List (Entry Nat)) (oldSafe : SafeOrder old)
 (consumers : List (Atom Nat)) (plans : List (Plan roles)) (assignment : Assignment)
 (valid : All model assignment (rewrite old consumers ++ block fresh))
 (packets : ∀ plan ∈ plans,
   (GeneralNominalRebasePacketView243.compile plan (mapping old)).Holds assignment) :
 All model (solve model old assignment) (consumers ++ block old) ∧
 (∀ plan ∈ plans, GeneralNominalVersionedPlans231.Holds plan (solve model old assignment)) := by
 refine ⟨GeneralPresenceOrderedRebase247.models_backward model common_laws old fresh
   oldSafe consumers assignment valid,?_⟩
 intro plan member
 exact (packet_exact old assignment plan).mp (packets plan member)

theorem public_models_iff (old fresh : List (Entry Nat))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh) (within : TargetsWithin fresh old)
 (consumers : List (Atom Nat)) (plans : List (Plan roles)) (sharedNames : Nat → Prop)
 (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, All model assignment (consumers ++ block old) ∧
   (∀ plan ∈ plans, GeneralNominalVersionedPlans231.Holds plan assignment) ∧
   Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, All model assignment (rewrite old consumers ++ block fresh) ∧
   (∀ plan ∈ plans, (GeneralNominalRebasePacketView243.compile plan (mapping old)).Holds assignment) ∧
   Agrees model sharedNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,valid,packets,agree⟩
   obtain ⟨newValid,newPackets⟩ := models_forward old fresh oldSafe freshSafe within consumers plans assignment valid packets
   refine ⟨solve model fresh assignment,newValid,newPackets,?_⟩
   intro name shared
   rw [solve_outside model fresh assignment name]
   · exact agree name shared
   · intro entry member
     obtain ⟨original,present,equal⟩ := within entry member
     rw [← equal]
     exact privateTargets name shared original present
 · rintro ⟨assignment,valid,packets,agree⟩
   obtain ⟨oldValid,oldPackets⟩ := models_backward old fresh oldSafe consumers plans assignment valid packets
   refine ⟨solve model old assignment,oldValid,oldPackets,?_⟩
   intro name shared
   rw [solve_outside model old assignment name (privateTargets name shared)]
   exact agree name shared
end Yulang.GeneralNominalOrderedPacketModels248
