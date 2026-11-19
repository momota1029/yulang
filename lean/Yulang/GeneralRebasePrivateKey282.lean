import Yulang.GeneralRebasePacketFootprint281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePrivateKey282
open GeneralNominalIdentities (Origin source source_identity)
open GeneralNominalAllocation (origin occurrences)
open GeneralRebaseAggregateTags281 (Tag fixedOrigin)
open GeneralNominalSaturationState (Packet)
open GeneralNominalCenters (Plan fresh)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralNominalState (sources)

def port (seed owner decl : Nat) (t : Tag) := source seed (fixedOrigin owner decl t)

def Excludes (p : Packet roles) (owner decl : Nat) (tag : Tag) : Prop :=
  port p.context.state.seed owner decl tag ∉ sources p.context.state

theorem different_purpose (t : Tag) (big : 2 ≤ purpose) :
    port seed owner decl t ≠ source seed (origin root other purpose name phase) := by
  intro same
  have key := (source_identity _ _ _).mp same
  have test : (if t.upper then (1 : Nat) else 0) = purpose := congrArg (fun k : Origin => k.2.2.1) key
  cases h : t.upper <;> simp [h] at test <;> omega

theorem versioned_distinct (p : Packet roles) (owner decl : Nat) (t : Tag) (purpose name : Nat) :
    port p.context.state.seed owner decl t ≠
      GeneralNominalAggregateVersion231.slot p.context.state.seed p.site.occurrence.identity
        p.declaration.id purpose name p.bindings := by
  unfold port fixedOrigin
  exact Ne.symm (GeneralNominalAggregateVersion231.not_legacy_slot _ _ _ _ _ _ _ _ _ _)

theorem endpoint_support (p : Packet roles) (observed : [bounds] = occurrences p.bindings name) :
    bounds.1 ∈ sources p.context.state ∧ bounds.2 ∈ sources p.context.state := by
  have cover := GeneralNominalAllocationSupport.report_endpoints p.context.state (GeneralNominalPacketSupport.report p)
  exact GeneralNominalAllocationSupport.occurrences_endpoints cover name bounds
    (observed ▸ List.mem_singleton_self _)

theorem capture_private {p : Packet roles} {owner decl : Nat} {t : Tag}
    (excluded : Excludes p owner decl t) (name : Nat) :
    port p.context.state.seed owner decl t ≠ ((capture p).inputs name).1 ∧
    port p.context.state.seed owner decl t ≠ ((capture p).inputs name).2 := by
  change _ ≠ ((GeneralNominalVersionedAllocation231.capture _ _ _ _ _).inputs name).1 ∧
    _ ≠ ((GeneralNominalVersionedAllocation231.capture _ _ _ _ _).inputs name).2
  cases listed : occurrences p.bindings name with
  | nil =>
    simpa only [GeneralNominalVersionedAllocation231.capture,listed] using
      And.intro (versioned_distinct p owner decl t 0 name) (versioned_distinct p owner decl t 1 name)
  | cons bounds rest =>
    cases rest with
    | nil =>
      have both := endpoint_support p listed.symm
      simp only [GeneralNominalVersionedAllocation231.capture,listed]
      exact ⟨fun h => excluded (h.symm ▸ both.1),fun h => excluded (h.symm ▸ both.2)⟩
    | cons other tail =>
      simpa only [GeneralNominalVersionedAllocation231.capture,listed] using
        And.intro (versioned_distinct p owner decl t 0 name) (versioned_distinct p owner decl t 1 name)

theorem binder_private {p : Plan roles} {owner decl : Nat} {t : Tag}
    (excluded : Excludes p.packet owner decl t) (name : Nat) :
    port p.packet.context.state.seed owner decl t ≠ binder p name := by
  unfold binder
  split
  · exact different_purpose t (by decide : 2 ≤ 2)
  · split
    · exact (capture_private excluded name).1
    · exact different_purpose t (by decide : 2 ≤ 8)

end Yulang.GeneralRebasePrivateKey282
