import Yulang.GeneralNominalOrderedClassClosed249
import Yulang.GeneralNominalJournalSupport249

/-! Actual compiled journal typed reads eliminate every old ordered target.
The statement concerns precisely the existing compile fields and does not
claim coverage of a redesigned successor state or finite transition work. -/
namespace Yulang.GeneralNominalOrderedJournalClosed249
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralNominalOrderedViewClosed249 GeneralNominalOrderedObservationClosed249
open GeneralNominalOrderedPacketClosed249 GeneralNominalOrderedClassClosed249
open GeneralNominalRebaseJournalView243
open GeneralNominalJournalSupport249
variable (old : List (Entry Nat)) (safe : SafeOrder old)
include safe

theorem effect_closed (state : GeneralNominalVersionedJournal232.State roles)
 (source : GeneralNominalVersionedJournal232.Effect roles) :
 Outside old (effectReads (effect state source (mapping old))) := by
 intro n member entry present
 obtain ⟨reads,member,read⟩ := List.mem_flatten.mp member
 simp only [effectComponents,effect,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl
 · exact compile_closed old safe _ n read entry present
 · exact projection_closed old safe _ _ n read entry present
 · exact class_closed old safe _ _ _ n read entry present
 · exact class_closed old safe _ _ _ n read entry present

theorem journal_closed (state : GeneralNominalVersionedJournal232.State roles) :
 Outside old (support (compile state (mapping old))) := by
 intro n member entry present
 obtain ⟨reads,member,read⟩ := List.mem_flatten.mp member
 simp only [components,compile,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl
 · exact compile_closed old safe _ n read entry present
 · exact compile_closed old safe _ n read entry present
 · obtain ⟨arguments,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact observed_closed old safe original n used entry present
 · obtain ⟨site,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact live_closed old safe original n used entry present
 · obtain ⟨packet,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact packet_closed old safe original n used entry present
 · obtain ⟨effect,member,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact effect_closed old safe state original n used entry present

theorem within_protected (fresh : List (Entry Nat)) (within : TargetsWithin fresh old)
 (state : GeneralNominalVersionedJournal232.State roles) :
 ∀ n ∈ support (compile state (mapping old)), ∀ entry ∈ fresh, entry.1 ≠ n := by
 intro n member entry present
 obtain ⟨original,found,equal⟩ := within entry present
 rw [← equal]
 exact journal_closed old safe state n member original found
end Yulang.GeneralNominalOrderedJournalClosed249
