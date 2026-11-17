import Yulang.GeneralDictionaryLooseIterationBookSupport240
import Yulang.GeneralNominalVersionedPacketFrame236
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseIterationPacketSupport240
open GeneralDictionaryLooseIterationBook240
open GeneralDictionaryLooseFamilyNames240
open GeneralDictionaryLooseIterationBookSupport240
open GeneralDictionaryLooseFamilyBase240
open GeneralNominalSemanticRawFrame236 (sources)
open GeneralNominalState (atomSources)

theorem raw_fresh (stage index : Nat) (later : stage ≤ index) :
 upper index ∉ sources (context stage).state := by
 intro member
 change upper index ∈ (List.ofFn (source stage) ++ List.ofFn (source stage) ++ [] ++
   (atoms stage).flatMap atomSources) at member
 simp only [List.append_nil,List.mem_append,List.mem_ofFn] at member
 rcases member with ((⟨slot,same⟩ | ⟨slot,same⟩) | member)
 · by_cases small : slot.val < 5
   · rw [source_small slot small] at same
     have large := upper_above index
     omega
   · rw [source_large slot (by omega)] at same
     exact upper_not_lower (slot.val-4) index same.symm
 · by_cases small : slot.val < 5
   · rw [source_small slot small] at same
     have large := upper_above index
     omega
   · rw [source_large slot (by omega)] at same
     exact upper_not_lower (slot.val-4) index same.symm
 · exact fresh_upper stage index later member
theorem private_sources (stage : Nat) :
 sources (GeneralNominalVersionedPlans231.privateState (packet stage)) ⊆
 sources (context stage).state ++
 (GeneralNominalVersionedInstallation231.atoms (packet stage)).flatMap atomSources := by
 unfold sources GeneralNominalSemanticRawFrame236.erased GeneralNominalState.sources
 unfold GeneralNominalVersionedPlans231.privateState GeneralNominalVersionedAllocation231.propagate
 simp only [GeneralNominalState.extend]
 intro name member
 simp only [List.mem_append,List.flatMap_append,List.not_mem_nil,or_false,
   GeneralNominalVersionedInstallation231.atoms] at member ⊢
 simpa only [or_assoc] using member

theorem private_fresh (stage index : Nat) (later : stage < index) :
 upper index ∉ sources (GeneralNominalVersionedPlans231.privateState (packet stage)) := by
 intro member
 rcases List.mem_append.mp (private_sources stage member) with old | added
 · exact raw_fresh stage index (by omega) old
 · have found := GeneralDictionaryLooseIterationAtomSupport240.atom_sources stage _ _ _ added
   simp only [List.mem_cons,List.not_mem_nil,or_false] at found
   rcases found with same | same | same | same | same
   · have large := upper_above index; omega
   · have large := upper_above index; omega
   · exact upper_not_lower stage index same
   · exact upper_not_lower (stage+1) index same
   · have equal := upper_injective same; omega
theorem head_fresh (stage index : Nat) (later : stage < index) :
 upper index ∉ GeneralNominalVersionedPacketFrame236.headSources (packet stage) := by
 intro member
 rcases List.mem_append.mp member with privatePart | reportPart
 · exact private_fresh stage index later privatePart
 · exact raw_fresh stage index (by omega)
     (GeneralNominalSemanticRawFrame236.report_sources_subset _ _ _ reportPart)

theorem capture_sources (stage : Nat) :
 GeneralNominalVersionedPacketFrame236.captureSources (plan stage) =
 [lower (stage+1),upper stage,GeneralDictionaryLooseLoopPacket240.actual,
  lower (stage+1),upper stage,GeneralDictionaryLooseLoopPacket240.actual] := by
 unfold GeneralNominalVersionedPacketFrame236.captureSources
 change [0,0].flatMap _ = _
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
 rw [GeneralNominalVersionedFrame231.binder_eq,
   GeneralDictionaryLooseFamilyFull240.binder_exact]
 unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
 rw [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
 rfl
theorem actual_fresh (index : Nat) : upper index ≠ GeneralDictionaryLooseLoopPacket240.actual :=
 GeneralNominalAggregateVersion231.not_legacy_slot 4 0 0 1 0 _ 0 0 8 0

theorem packet_fresh (stage index : Nat) (later : stage < index) :
 upper index ∉ GeneralNominalVersionedPacketFrame236.sources (plan stage) := by
 intro member
 unfold GeneralNominalVersionedPacketFrame236.sources at member
 simp only [List.mem_append] at member
 rcases member with ((((head | input) | captures) | schema) | emitted) | children
 · exact head_fresh stage index later head
 · change upper index ∈ [3,3,3] at input
   simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at input
   have large := upper_above index
   omega
 · rw [capture_sources] at captures
   simp only [List.mem_cons,List.not_mem_nil,or_false] at captures
   have lowerNe := upper_not_lower (stage+1) index
   have actualNe := actual_fresh index
   have upperNe : upper index ≠ upper stage := by intro eq; have := upper_injective eq; omega
   omega
 · rw [GeneralDictionaryLooseFamilyFull240.head_schema] at schema
   unfold GeneralNominalVersionedHeadFrame236.schemaSources at schema
   simp only [List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,
     GeneralNominalVersionedHeadFrame236.variableSources,ite_true] at schema
   rw [GeneralNominalVersionedFrame231.binder_eq,
     GeneralDictionaryLooseFamilyFull240.binder_exact] at schema
   change upper index ∈ [3,3,GeneralDictionaryLooseLoopPacket240.actual,3,GeneralDictionaryLooseLoopPacket240.actual] at schema
   simp only [List.mem_cons,List.not_mem_nil,or_false] at schema
   have large := upper_above index
   have actualNe := actual_fresh index
   omega
 · rw [GeneralDictionaryLooseFamilyFull240.emitted_empty] at emitted
   cases emitted
 · change upper index ∈ [] at children
   cases children
end Yulang.GeneralDictionaryLooseIterationPacketSupport240
