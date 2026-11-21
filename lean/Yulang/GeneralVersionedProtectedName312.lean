import Yulang.GeneralVersionedSemanticPeer312
import Yulang.GeneralNominalVersionedAggregateReuse236

set_option backward.isDefEq.respectTransparency false
/-! The residual protected-entry contract is exactly same owner, declaration
and per-name occurrence version. Whole-report equality is unnecessary, and
the same stored name certifies either polarity that is actually protected. -/
namespace Yulang.GeneralVersionedProtectedName312
open GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalVersionedAggregateRealization236 (member_iff)
open GeneralNominalAggregateVersion231 (slot)
open GeneralNominalAllocation (occurrences)
open GeneralNominalSaturationState (Packet)
variable {roles : Roles.RoleDecls} {s : State roles} {p : Packet roles}

abbrev atSlot (p : Packet roles) (mode name : Nat) : Nat :=
  slot p.context.state.seed p.site.occurrence.identity p.declaration.id mode name p.bindings

def Named (pool : List Nat) (s : State roles) (p : Packet roles) : Prop :=
  ∀ name ∈ p.declaration.inputNames, (occurrences p.bindings name).length ≠ 1 →
    (atSlot p 0 name ∈ pool ∨ atSlot p 1 name ∈ pool) →
    ∃ past ∈ s.plans, name ∈ past.packet.declaration.inputNames ∧
      past.packet.context.state.seed = p.context.state.seed ∧
      past.packet.site.occurrence.identity = p.site.occurrence.identity ∧
      past.packet.declaration.id = p.declaration.id ∧
      occurrences past.packet.bindings name = occurrences p.bindings name

theorem same_slot {past : Packet roles} {name mode}
    (seed : past.context.state.seed = p.context.state.seed)
    (owner : past.site.occurrence.identity = p.site.occurrence.identity)
    (key : past.declaration.id = p.declaration.id)
    (version : occurrences past.bindings name = occurrences p.bindings name) :
    atSlot past mode name = atSlot p mode name := by
  have code := GeneralNominalAggregateVersion231.version_eq_iff.mpr version
  unfold atSlot slot GeneralNominalAggregateVersion231.key
  rw [seed,owner,key,code]

theorem all_ids (named : Named pool s p) : IdCovered pool s p := by
  intro entry found inside
  obtain ⟨name,member,count,lower | upper⟩ := (member_iff ..).mp found
  · have targetEq : entry.1 = atSlot p 0 name := congrArg Prod.fst lower
    have inPool : atSlot p 0 name ∈ pool := by
      rw [← targetEq]
      exact inside
    obtain ⟨prior,stored,used,seed,owner,key,version⟩ := named name member count (.inl inPool)
    have multiplicity : (occurrences prior.packet.bindings name).length ≠ 1 := version ▸ count
    refine ⟨prior,stored,(atSlot prior.packet 0 name,GeneralNominalAllocation.lower (occurrences prior.packet.bindings name)),?_,?_⟩
    · exact (member_iff ..).mpr ⟨name,used,multiplicity,.inl rfl⟩
    · exact (same_slot seed owner key version).trans ((congrArg Prod.fst lower).symm)
  · have targetEq : entry.1 = atSlot p 1 name := congrArg Prod.fst upper
    have inPool : atSlot p 1 name ∈ pool := by
      rw [← targetEq]
      exact inside
    obtain ⟨prior,stored,used,seed,owner,key,version⟩ := named name member count (.inr inPool)
    have multiplicity : (occurrences prior.packet.bindings name).length ≠ 1 := version ▸ count
    refine ⟨prior,stored,(atSlot prior.packet 1 name,GeneralNominalAllocation.upper (occurrences prior.packet.bindings name)),?_,?_⟩
    · exact (member_iff ..).mpr ⟨name,used,multiplicity,.inr rfl⟩
    · exact (same_slot seed owner key version).trans ((congrArg Prod.fst upper).symm)

theorem owner_from_id
    (sameSeed : ∀ past ∈ s.plans, past.packet.context.state.seed = p.context.state.seed)
    (covered : IdCovered pool s p) : Named pool s p := by
  intro name named count active
  have get : ∀ mode : Nat, (mode = 0 ∨ mode = 1) → atSlot p mode name ∈ pool →
      ∃ past ∈ s.plans, name ∈ past.packet.declaration.inputNames ∧
        past.packet.context.state.seed = p.context.state.seed ∧
        past.packet.site.occurrence.identity = p.site.occurrence.identity ∧
        past.packet.declaration.id = p.declaration.id ∧
        occurrences past.packet.bindings name = occurrences p.bindings name := by
    intro mode polarity active
    let entry : GeneralNominalFiniteEquationRealization236.Entry :=
      (atSlot p mode name,if mode = 0 then GeneralNominalAllocation.lower (occurrences p.bindings name)
        else GeneralNominalAllocation.upper (occurrences p.bindings name))
    have found : entry ∈ packetEntries p := by
      apply (member_iff ..).mpr
      refine ⟨name,named,count,?_⟩
      rcases polarity with rfl|rfl
      · exact .inl rfl
      · exact .inr rfl
    obtain ⟨prior,stored,old,oldFound,target⟩ := covered entry found active
    have seed := sameSeed prior stored
    obtain ⟨earlier,used,_,lower | upper⟩ := (member_iff ..).mp oldFound
    · have equal : atSlot prior.packet 0 earlier = atSlot p mode name :=
        (congrArg Prod.fst lower).symm.trans target
      unfold atSlot at equal
      rw [seed] at equal
      obtain ⟨x,k,_,n,v⟩ := GeneralNominalVersionedAggregateReuse236.slot_fields equal
      subst earlier
      exact ⟨prior,stored,used,seed,x,k,v⟩
    · have equal : atSlot prior.packet 1 earlier = atSlot p mode name :=
        (congrArg Prod.fst upper).symm.trans target
      unfold atSlot at equal
      rw [seed] at equal
      obtain ⟨x,k,_,n,v⟩ := GeneralNominalVersionedAggregateReuse236.slot_fields equal
      subst earlier
      exact ⟨prior,stored,used,seed,x,k,v⟩
  exact active.elim (get 0 (.inl rfl)) (get 1 (.inr rfl))

theorem on_trace
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (current : p.context = s.core.erased.current.context) :
    IdCovered pool s p ↔ Named pool s p := by
  refine ⟨owner_from_id ?_,all_ids⟩
  intro prior stored
  rw [current]
  exact GeneralNominalVersionedMixedSeedLedger237.reachable path prior stored

end Yulang.GeneralVersionedProtectedName312
