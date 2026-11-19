import Yulang.GeneralRebasePrivateKey282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePrivateHead282
open GeneralRebasePrivateKey282 (port Excludes capture_private binder_private)
open GeneralRebaseAggregateTags281 (Tag)
open GeneralNominalCenters (Plan)
open GeneralNominalState (sources)
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedInstallation231 (replayPlan reserved replay_private_models)
open GeneralNominalVersionedPlans231 (privateState HeadModels)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedExpressionFrame236 (variableSource equationSources schemaSources)
open GeneralNominalVersionedFrame231 (binder capture)

theorem replay_private {q : Plan roles} (visible : q.packet.declaration ∈ q.packet.registry.declarations)
    (absent : Excludes q.packet owner decl tag) :
    port q.packet.context.state.seed owner decl tag ∉
      sources (replayPlan q).packet.context.state := by
  intro seen
  rcases List.mem_append.mp (GeneralRebaseOwnedSupport277.replay_support q visible seen) with old | reserved
  · exact absent old
  · exact GeneralRebaseFixedOrigin281.not_reserved q.packet owner decl tag reserved

theorem head_transport (q : Plan roles) {x y : Assignment}
    (visible : q.packet.declaration ∈ q.packet.registry.declarations)
    (same : Agree (sources q.packet.context.state ++ reserved q.packet) x y) :
    HeadModels q.packet x ↔ HeadModels q.packet y := by
  unfold HeadModels
  rw [← replay_private_models,← replay_private_models]
  have replay : Agree (sources (replayPlan q).packet.context.state) x y :=
    fun n seen => same n (GeneralRebaseOwnedSupport277.replay_support q visible seen)
  apply and_congr
  · exact ⟨GeneralNominalCenteredModelExtension.source_models_same _ replay,
      GeneralNominalCenteredModelExtension.source_models_same _ (fun n h => (replay n h).symm)⟩
  · apply GeneralNominalSemanticRawFrame236.projection_iff
    intro n used
    exact same n (List.mem_append_left _ (by
      have found := GeneralNominalSemanticRawFrame236.report_sources_subset _ _ _ used
      unfold GeneralNominalSemanticRawFrame236.sources GeneralNominalSemanticRawFrame236.erased at found
      simp only [sources,List.append_nil,List.mem_append,or_assoc] at found ⊢
      rcases found with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))))

theorem protected_head (q : Plan roles) (visible : q.packet.declaration ∈ q.packet.registry.declarations)
    (absent : Excludes q.packet owner decl tag) (x y : Assignment)
    (same : ∀ n, n ≠ port q.packet.context.state.seed owner decl tag → x n = y n) :
    HeadModels q.packet x ↔ HeadModels q.packet y :=
  head_transport q visible (fun n used => same n (fun h => by
    subst n
    exact (List.mem_append.mp used).elim absent (GeneralRebaseFixedOrigin281.not_reserved _ _ _ _)))

theorem variable_private {q : Plan roles} (absent : Excludes q.packet owner decl tag)
    (mode : GeneralNominalMaterialization.Mode) (name : Nat) :
    port q.packet.context.state.seed owner decl tag ≠ variableSource q mode name := by
  unfold variableSource
  split
  · exact binder_private absent name
  · cases mode
    · exact (capture_private absent name).1
    · exact (capture_private absent name).2
    · exact binder_private absent name

theorem output_private (q : Plan roles) (tag : Tag) (name : Nat) :
    port q.packet.context.state.seed owner decl tag ≠ (capture q.packet).outputs name :=
  GeneralRebasePrivateKey282.different_purpose tag (by decide : 2 ≤ 2)

theorem schema_private {q : Plan roles} (absent : Excludes q.packet owner decl tag)
    (schema : GeneralNominalCenteredHeadMatSchemas.Schema)
    (targets : ∀ eq ∈ schema.equations, port q.packet.context.state.seed owner decl tag ≠ eq.target) :
    port q.packet.context.state.seed owner decl tag ∉ schemaSources q schema := by
  intro used
  obtain ⟨e,listed,member⟩ := List.mem_flatMap.mp used
  rcases List.mem_cons.mp member with target|variables
  · exact targets e listed target
  · obtain ⟨key,_,equal⟩ := List.mem_map.mp variables
    exact variable_private absent key.1 key.2 equal.symm

end Yulang.GeneralRebasePrivateHead282
