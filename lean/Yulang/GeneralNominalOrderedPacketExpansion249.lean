import Yulang.GeneralNominalPacketSupport249
import Yulang.GeneralPresenceOrderedExpansion249

/-! Expanded-target rebase of complete actual compiled packets. A finite list
of Plans shares one witness with consumers/block/public coordinates. Complete
operational journal enumeration is not asserted. -/
namespace Yulang.GeneralNominalOrderedPacketExpansion249
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247
open GeneralPresenceCommonLaws245
open GeneralNominalCenters (Plan)

def Protected (plan : Plan roles) (old fresh : List (Entry Nat)) : Prop :=
 ∀ name ∈ GeneralNominalPacketSupport249.support
   (GeneralNominalRebasePacketView243.compile plan (mapping old)),
   ∀ entry ∈ fresh, entry.1 ≠ name

theorem packet_preserved (packet : GeneralNominalRebasePacketView243.Packet)
 (fresh : List (Entry Nat)) (assignment : Assignment)
 (protectedReads : ∀ name ∈ GeneralNominalPacketSupport249.support packet,
   ∀ entry ∈ fresh, entry.1 ≠ name) :
 packet.Holds (solve model fresh assignment) ↔ packet.Holds assignment := by
 apply GeneralNominalPacketSupport249.packet_iff packet _ assignment (solve_rows model fresh assignment)
 intro name member
 exact congrArg Prod.fst (solve_outside model fresh assignment name (protectedReads name member))

theorem packet_forward (plan : Plan roles) (old fresh : List (Entry Nat))
 (protectedReads : Protected plan old fresh) (assignment : Assignment)
 (valid : All model assignment (block old)) :
 (GeneralNominalRebasePacketView243.compile plan (mapping old)).Holds (solve model fresh assignment) ↔
 GeneralNominalVersionedPlans231.Holds plan assignment := by
 rw [packet_preserved _ fresh assignment protectedReads]
 exact GeneralNominalOrderedPacket248.packet_recovered old assignment valid plan

theorem public_models_iff (old fresh : List (Entry Nat))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh)
 (consumers : List (Atom Nat)) (protectedConsumers : GeneralPresenceOrderedExpansion249.Protected old fresh consumers)
 (plans : List (Plan roles)) (protectedPackets : ∀ plan ∈ plans, Protected plan old fresh)
 (sharedNames : Nat → Prop)
 (oldPrivate : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (freshPrivate : ∀ name, sharedNames name → ∀ entry ∈ fresh, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, All model assignment (consumers ++ block old) ∧
   (∀ plan ∈ plans, GeneralNominalVersionedPlans231.Holds plan assignment) ∧
   Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, All model assignment (rewrite old consumers ++ block fresh) ∧
   (∀ plan ∈ plans, (GeneralNominalRebasePacketView243.compile plan (mapping old)).Holds assignment) ∧
   Agrees model sharedNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,valid,packets,agree⟩
   refine ⟨solve model fresh assignment,
     GeneralPresenceOrderedExpansion249.models_forward model common_laws old fresh freshSafe
       consumers protectedConsumers assignment valid,?_,?_⟩
   · intro plan member
     exact (packet_forward plan old fresh (protectedPackets plan member) assignment
       ((all_append model assignment _ _).mp valid).2).mpr (packets plan member)
   · intro name shared
     rw [solve_outside model fresh assignment name (freshPrivate name shared)]
     exact agree name shared
 · rintro ⟨assignment,valid,packets,agree⟩
   refine ⟨solve model old assignment,
     GeneralPresenceOrderedRebase247.models_backward model common_laws old fresh oldSafe consumers assignment valid,?_,?_⟩
   · intro plan member
     exact (GeneralNominalOrderedPacket248.packet_exact old assignment plan).mp (packets plan member)
   · intro name shared
     rw [solve_outside model old assignment name (oldPrivate name shared)]
     exact agree name shared
end Yulang.GeneralNominalOrderedPacketExpansion249
