import Yulang.GeneralNominalOrderedViewClosed249
import Yulang.GeneralNominalPacketSupport249

/-! Actual compiled live values, origin paths and projection reports eliminate
old typed targets. This is a support producer, not a source-step certificate. -/
namespace Yulang.GeneralNominalOrderedObservationClosed249
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralNominalOrderedViewClosed249
open GeneralPresenceUsedSupport245 (typedReads)

variable (old : List (Entry Nat)) (safe : SafeOrder old)
include safe

theorem origin_closed (origin : GeneralNominalRecursiveInspection.Origin) :
 Outside old (GeneralNominalOriginSupport249.support (GeneralNominalRebaseOriginView243.compile (mapping old) origin)) := by
 induction origin with
 | source name => exact GeneralPresenceOrderedSyntax247.mapping_closed old safe name
 | nominal parent name index ih => exact ih
 | structural parent shape index ih => exact ih

theorem bounds_closed (state : GeneralNominalState.State) (bounds : GeneralNominalInspection.Bounds state) :
 Outside old (GeneralNominalProjectionSupport249.boundsReads (GeneralNominalRebaseProjectionView243.bounds state (mapping old) bounds)) := by
 intro name member entry present
 rcases List.mem_append.mp member with member | member
 · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ name member entry present
 · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ name member entry present

theorem capture_closed (state : GeneralNominalState.State) (capture : GeneralNominalRecursiveInspection.Capture state) :
 Outside old (GeneralNominalProjectionSupport249.captureReads (GeneralNominalRebaseProjectionView243.capture state (mapping old) capture)) := by
 intro name member entry present
 rcases List.mem_append.mp member with bounds | origin
 · exact bounds_closed old safe state capture.bounds name bounds entry present
 · obtain ⟨ref,found,read⟩ := List.mem_flatMap.mp origin
   have found' : capture.origin.map (GeneralNominalRebaseOriginView243.compile (mapping old)) = some ref := by
     simpa only [Option.mem_toList,GeneralNominalRebaseProjectionView243.capture] using found
   obtain ⟨original,_,rfl⟩ := Option.map_eq_some_iff.mp found'
   exact origin_closed old safe original name read entry present

theorem projection_closed (state : GeneralNominalState.State) (report : GeneralNominalRecursiveInspection.Report state) :
 Outside old (GeneralNominalProjectionSupport249.support (GeneralNominalRebaseProjectionView243.compile state (mapping old) report)) := by
 intro name member entry present
 rcases List.mem_append.mp member with left | captures
 · rcases List.mem_append.mp left with anchors | tests
   · obtain ⟨anchor,member,read⟩ := List.mem_flatMap.mp anchors
     obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
     rcases List.mem_append.mp read with origin | bounds
     · exact origin_closed old safe original.1 name origin entry present
     · exact bounds_closed old safe state original.2 name bounds entry present
   · obtain ⟨test,member,read⟩ := List.mem_flatMap.mp tests
     obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
     exact origin_closed old safe original.1 name read entry present
 · obtain ⟨capture,member,read⟩ := List.mem_flatMap.mp captures
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact capture_closed old safe state original name read entry present

theorem argument_closed (lower upper center : Nat) :
 Outside old (GeneralNominalLiveSupport249.argumentReads
   ⟨(mapping old lower).ty,(mapping old upper).ty,(mapping old center).ty⟩) := by
 intro name member entry present
 rcases List.mem_append.mp member with left | centerRead
 · rcases List.mem_append.mp left with lowerRead | upperRead
   · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe lower name lowerRead entry present
   · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe upper name upperRead entry present
 · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe center name centerRead entry present

theorem live_closed (site : GeneralNominalCenters.Site roles) :
 Outside old (GeneralNominalLiveSupport249.support (GeneralNominalRebaseLiveView243.compile site (mapping old))) := by
 intro name member entry present
 rcases List.mem_append.mp member with arguments | outputs
 · obtain ⟨argument,member,read⟩ := List.mem_flatMap.mp arguments
   obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
   exact argument_closed old safe _ _ _ name read entry present
 · obtain ⟨output,member,read⟩ := List.mem_flatMap.mp outputs
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact GeneralPresenceOrderedSyntax247.mapping_closed old safe original.target name read entry present
end Yulang.GeneralNominalOrderedObservationClosed249
