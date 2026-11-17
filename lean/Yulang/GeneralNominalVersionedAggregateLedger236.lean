import Yulang.GeneralNominalVersionedAggregateEntries236
set_option backward.isDefEq.respectTransparency false
/-! Identical aggregate IDs across historical packets denote identical terms.
Protected-entry coverage is a finite syntactic lookup in actual recorded plans. -/
namespace Yulang.GeneralNominalVersionedAggregateLedger236
open GeneralNominalVersionedAggregateRealization236 (entries member_iff)
open GeneralNominalFiniteEquationRealization236 (Entry)
open GeneralNominalVersionedJournal232
open GeneralNominalCenters

theorem same_target
 (one : first ∈ entries seed r d a names)
 (two : last ∈ entries seed r' d' b otherNames) (same : first.1 = last.1) : first.2 = last.2 := by
 obtain ⟨name,_,_,one⟩ := (member_iff ..).mp one
 obtain ⟨other,_,_,two⟩ := (member_iff ..).mp two
 rcases one with rfl | rfl <;> rcases two with rfl | rfl
 all_goals have fields := GeneralNominalVersionedAggregateReuse236.slot_fields same
 · exact congrArg GeneralNominalAllocation.lower fields.2.2.2.2
 · cases fields.2.2.1
 · cases fields.2.2.1
 · exact congrArg GeneralNominalAllocation.upper fields.2.2.2.2

def packetEntries (packet : GeneralNominalSaturationState.Packet roles) : List Entry :=
 entries packet.context.state.seed packet.site.occurrence.identity packet.declaration.id
   packet.bindings packet.declaration.inputNames

def ProtectedCovered (pool : List Nat) (state : State roles)
 (packet : GeneralNominalSaturationState.Packet roles) : Prop :=
 ∀ entry ∈ packetEntries packet, entry.1 ∈ pool →
 ∃ prior ∈ state.plans, prior.packet.context.state.seed = packet.context.state.seed ∧
   ∃ old ∈ packetEntries prior.packet, old.1 = entry.1

theorem protected_equations (covered : ProtectedCovered pool state packet) (valid : Models state model) :
 ∀ entry ∈ packetEntries packet, entry.1 ∈ pool →
 PresenceNormalForm.All CommonNominalFullCarrier.model model (GeneralNominalAllocation.equations entry.1 entry.2) := by
 intro entry member inside
 obtain ⟨prior,present,seed,old,oldMember,target⟩ := covered entry member inside
 have held := (GeneralNominalVersionedAggregateEntries236.holds_iff prior.packet.context.state prior.packet.registry
   prior.packet.site.occurrence.identity prior.packet.declaration prior.packet.bindings model).mp
   (GeneralNominalVersionedAggregateReuse236.recorded_merges valid present) old oldMember
 have member' := oldMember
 unfold packetEntries at member'
 rw [seed] at member'
 have term := same_target member' member target
 rw [target,term] at held
 exact held
end Yulang.GeneralNominalVersionedAggregateLedger236
