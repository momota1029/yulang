import Yulang.GeneralRebasePrivateRequests282

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
namespace Yulang.GeneralRebasePrivatePacket282
open GeneralNominalCenters (Plan Site)
open GeneralRebasePrivateKey282 (port Excludes capture_private binder_private)
open GeneralRebasePrivateHead282 (replay_private)
open GeneralRebasePrivateSchema282 (SiteSafe site_private head_private)
open GeneralRebasePrivateChild282 (child_site child_output)
open GeneralRebasePrivateRequests282 (OutputSafe child_schema_private emitted_schema_private)
open GeneralRebaseAggregateTags281 (Tag)
open GeneralNominalVersionedPacketFrame236 (headSources privateSources captureSources childSources sources)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralNominalState (State)
open GeneralNominalCommonBridge (Assignment)

theorem semantic_subset (s : State) :
    GeneralNominalSemanticRawFrame236.sources s ⊆ GeneralNominalState.sources s := by
  intro n member
  unfold GeneralNominalSemanticRawFrame236.sources GeneralNominalSemanticRawFrame236.erased at member
  simp only [GeneralNominalState.sources,List.append_nil,List.mem_append,or_assoc] at member ⊢
  rcases member with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

theorem private_sources_equal (q : Plan roles) :
    GeneralNominalState.sources (GeneralNominalVersionedPlans231.privateState q.packet) =
      GeneralNominalState.sources (replayPlan q).packet.context.state := by
  simp only [GeneralNominalState.sources,GeneralNominalVersionedPlans231.privateState,
    GeneralNominalVersionedAllocation231.propagate,GeneralNominalState.extend,
    GeneralNominalVersionedInstallation231.replayPlan,GeneralNominalVersionedTransport231.extendedPlan,
    GeneralNominalVersionedTransport231.extendedPacket,GeneralDictionaryOrdinaryTransport.extend,GeneralNominalVersionedInstallation231.atoms,
    GeneralNominalVersionedInstallation231.reserved,List.append_nil,List.append_assoc]

theorem head_sources_private (q : Plan roles) (visible : q.packet.declaration ∈ q.packet.registry.declarations)
    (absent : Excludes q.packet owner decl tag) :
    port q.packet.context.state.seed owner decl tag ∉ headSources q.packet := by
  intro found
  rcases List.mem_append.mp found with pri|report
  · have member := semantic_subset _ pri
    rw [private_sources_equal q] at member
    exact replay_private visible absent member
  · exact absent (semantic_subset _ (GeneralNominalSemanticRawFrame236.report_sources_subset _ _ _ report))

structure Safe (q : Plan roles) (owner decl : Nat) (tag : Tag) : Prop where
  visible : q.packet.declaration ∈ q.packet.registry.declarations
  excludes : Excludes q.packet owner decl tag
  input : SiteSafe q.input (port q.packet.context.state.seed owner decl tag)
  outputs : OutputSafe q (port q.packet.context.state.seed owner decl tag)

theorem captures_private {q : Plan roles} (absent : Excludes q.packet owner decl tag) :
    port q.packet.context.state.seed owner decl tag ∉ captureSources q := by
  intro found
  obtain ⟨name,_,used⟩ := List.mem_flatMap.mp found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with lo|hi|center
  · exact (capture_private absent name).1 lo
  · exact (capture_private absent name).2 hi
  · exact binder_private absent name center

theorem children_private {q : Plan roles} (absent : Excludes q.packet owner decl tag) :
    port q.packet.context.state.seed owner decl tag ∉ childSources q := by
  intro found
  obtain ⟨clause,_,used⟩ := List.mem_flatMap.mp found
  rcases List.mem_append.mp used with site|schema
  · exact site_private (child_site absent clause.val _) site
  · exact child_schema_private absent clause.val _ schema

theorem sources_private {q : Plan roles} (safe : Safe q owner decl tag) :
    port q.packet.context.state.seed owner decl tag ∉ sources q := by
  intro member
  rcases List.mem_append.mp member with member|child
  · rcases List.mem_append.mp member with member|emitted
    · rcases List.mem_append.mp member with member|head
      · rcases List.mem_append.mp member with member|captures
        · rcases List.mem_append.mp member with pri|input
          · exact head_sources_private q safe.visible safe.excludes pri
          · exact site_private safe.input input
        · exact captures_private safe.excludes captures
      · exact head_private q safe.excludes safe.input head
    · exact emitted_schema_private safe.excludes safe.outputs emitted
  · exact children_private safe.excludes child

end Yulang.GeneralRebasePrivatePacket282
