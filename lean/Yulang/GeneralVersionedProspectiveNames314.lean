import Yulang.GeneralVersionedNewOwnerHead314

set_option backward.isDefEq.respectTransparency false
/-! Mixed-history footprints distinguish a currently prospective owner's
semantic reads from its independently writable where columns. -/
namespace Yulang.GeneralVersionedProspectiveNames314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedOwnerEnvelope314 (Envelope current)
open GeneralVersionedTraceDomain313 (context seed)
open GeneralNominalVersionedFrame231 (binder capture)
open GeneralNominalAllocation (occurrences)
open GeneralNominalIdentities (Origin source source_identity)
open GeneralVersionedUnseenBinder313 (Unseen)

def ReadTag (kind : Nat) : Prop := kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 8

def LocalTag (p : Plan roles) (allowed : Nat → Prop) (n : Nat) : Prop :=
  ∃ k : Origin, allowed k.2.2.1 ∧ source p.packet.context.state.seed k = n

def Read (s : State roles) (p : Plan roles) (n : Nat) : Prop :=
  Envelope s n ∨ LocalTag p ReadTag n
def Actual (s : State roles) (p : Plan roles) (n : Nat) : Prop :=
  Envelope s n ∨ ∃ k : Origin, (k.2.2.1 = 2 ∨ k.2.2.1 = 8) ∧
    k.2.2.2.2 = 0 ∧ source p.packet.context.state.seed k = n

theorem weaken {s : State roles} {p : Plan roles} (a : Actual s p n) : Read s p n := by
  rcases a with same|⟨k,tag,_,hit⟩
  · exact .inl same
  · exact .inr ⟨k,.inr (.inr tag),hit⟩

theorem raw_read {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    (aligned : p.packet.context = context s)
    (member : n ∈ GeneralNominalState.sources p.packet.context.state) : Envelope s n := by
  rw [aligned] at member
  exact current actual member

theorem endpoint_reads {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (aligned : p.packet.context = context s) (name : Nat) :
    Read s p ((capture p.packet).inputs name).1 ∧ Read s p ((capture p.packet).inputs name).2 := by
  have singleton (bounds : GeneralSourceState.Interval) (seen : occurrences p.packet.bindings name = [bounds]) :
      Read s p bounds.1 ∧ Read s p bounds.2 := by
    have within : bounds ∈ occurrences p.packet.bindings name := seen ▸ List.mem_singleton_self _
    have eps := GeneralNominalAllocationSupport.occurrences_endpoints
      (GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet))
      name bounds within
    exact ⟨.inl (raw_read actual aligned eps.1),.inl (raw_read actual aligned eps.2)⟩
  have alloc :
      Read s p (GeneralNominalAggregateVersion231.slot p.packet.context.state.seed p.packet.site.occurrence.identity
        p.packet.declaration.id 0 name p.packet.bindings) ∧
      Read s p (GeneralNominalAggregateVersion231.slot p.packet.context.state.seed p.packet.site.occurrence.identity
        p.packet.declaration.id 1 name p.packet.bindings) :=
    ⟨.inr ⟨_,.inl rfl,rfl⟩,.inr ⟨_,.inr (.inl rfl),rfl⟩⟩
  unfold capture GeneralNominalVersionedFrame231.frame GeneralNominalVersionedAllocation231.capture
  cases found : occurrences p.packet.bindings name with
  | nil => simpa only [found] using alloc
  | cons first rest =>
    cases rest with
    | nil => simpa only [found] using singleton first found
    | cons b tail => simpa only [found] using alloc

theorem actual_binder {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (aligned : p.packet.context = context s) (name : Nat) :
    Actual s p (binder p name) := by
  have privateSlot : Actual s p (fresh p.packet.context.state.seed p.packet.site.occurrence.identity
      p.packet.declaration.id 8 name 0) := .inr ⟨_,.inr rfl,rfl,rfl⟩
  have different := GeneralNominalAggregateVersion231.distinct_purpose p.packet.context.state.seed
    p.packet.site.occurrence.identity p.packet.declaration.id 0 1 name p.packet.bindings p.packet.bindings (by decide)
  unfold binder
  split
  · exact .inr ⟨_,.inl rfl,rfl,rfl⟩
  · unfold capture GeneralNominalVersionedFrame231.frame GeneralNominalVersionedAllocation231.capture
    cases found : occurrences p.packet.bindings name with
    | nil => simpa only [found,different,ite_false] using privateSlot
    | cons first rest =>
      cases rest with
      | nil =>
        simp only [found]
        split
        · have listed : first ∈ occurrences p.packet.bindings name := found ▸ List.mem_singleton_self _
          exact .inl (raw_read actual aligned
            (GeneralNominalAllocationSupport.occurrences_endpoints
              (GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet))
              name first listed).1)
        · exact privateSlot
      | cons b tail => simpa only [found,different,ite_false] using privateSlot

theorem rhs_reads {s : State roles} {p : Plan roles} (actual : Reachable registry root s)
    (aligned : p.packet.context = context s) (mode : GeneralNominalMaterialization.Mode) (name : Nat) :
    Read s p (GeneralNominalVersionedExpressionFrame236.variableSource p mode name) := by
  unfold GeneralNominalVersionedExpressionFrame236.variableSource
  split
  · exact weaken (actual_binder actual aligned name)
  · cases mode
    · exact (endpoint_reads actual aligned name).1
    · exact (endpoint_reads actual aligned name).2
    · exact weaken (actual_binder actual aligned name)

theorem excludes {s : State roles} {p : Plan roles} (aligned : p.packet.context = context s) (unseen : Unseen s p)
    {kind : Nat} (forbidden : ¬ ReadTag kind) (a b : Nat) :
    ¬ Read s p (fresh p.packet.context.state.seed p.packet.site.occurrence.identity p.packet.declaration.id kind a b) := by
  let k := GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id kind a b
  intro read
  rcases read with existing|⟨other,point,eq⟩
  · change Envelope s (source p.packet.context.state.seed k) at existing
    rw [aligned] at existing
    exact GeneralVersionedOwnerEnvelope314.never (key := k) unseen existing
  · have same : other = k := (source_identity _ _ _).mp eq
    subst other
    exact forbidden point

end Yulang.GeneralVersionedProspectiveNames314
