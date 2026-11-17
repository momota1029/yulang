import Yulang.GeneralDictionaryMixedGround218PointPacket235
import Yulang.GeneralDictionaryMixedGround218Fresh235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218PointFrame235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (declaration declaration_checked model)
open GeneralDictionaryMixedGround218Point235
open GeneralDictionaryMixedGround218PointPacket235
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

theorem source_owned (member : identity ∈ GeneralNominalState.sources packet.context.state) :
    identity < 8 ∨ ∃ key ∈ packet.context.state.allocated, GeneralNominalIdentities.source 7 key = identity := by
  simp only [GeneralNominalState.sources,List.mem_append] at member
  rcases member with ((type | row) | reserved) | ordinary
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp type
    change Fin 8 at slot
    change slot.val = identity at equal
    exact Or.inl (by have bound := slot.isLt; omega)
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp row
    change Fin 8 at slot
    change slot.val = identity at equal
    exact Or.inl (by have bound := slot.isLt; omega)
  · change identity ∈ GeneralNominalVersionedInstallation231.reserved GeneralDictionaryMixedGround218Leaf235.parentPacket at reserved
    obtain ⟨key,member,equal⟩ := List.mem_map.mp reserved
    exact Or.inr ⟨key,List.mem_append_right _ member,equal⟩
  · change identity ∈ GeneralDictionaryMixedGround218Leaf235.ctx.state.ordinary.flatMap GeneralNominalState.atomSources at ordinary
    rw [GeneralDictionaryMixedGround218Fresh235.ordinary_exact] at ordinary
    change identity ∈ [2,3,2,3,6,6,6,6,2,3,2,3] at ordinary
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ordinary
    exact Or.inl (by omega)

theorem fresh (bindings) : GeneralNominalVersionedAllocation231.Fresh packet.context.state registry root.identity bindings := by
  intro key _ collision
  change GeneralNominalIdentities.source 7 key ∈ _ at collision
  rcases source_owned collision with small | ⟨old,owned,equal⟩
  · have above := GeneralNominalIdentities.source_above_seed 7 key
    exact False.elim (by omega)
  · have same := (GeneralNominalIdentities.source_identity 7 old key).mp equal
    exact same ▸ owned

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry packet.context root declaration := by
  refine ⟨source.metadata,?_,[(6,6)],rfl,fresh _,?_,model,GeneralNominalVersionedPlans231.head_models packet_holds⟩
  · constructor
    · intro i; constructor <;>
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨6,rfl⟩)))
    · intro output member; cases member
  · rw [GeneralDictionaryGroundCopy218SaturatedParent.report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry point.core root 0 plan := by
  refine ⟨rfl,context_eq,rfl,rfl,?_,?_,List.mem_cons_self,rfl,rfl,?_⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_self
  · rw [←context_eq]; exact prepared
end Yulang.GeneralDictionaryMixedGround218PointFrame235
