import Yulang.GeneralNominalVersionedAggregateEntries236
import Yulang.GeneralNominalVersionedInstall232
import Yulang.GeneralNominalAllocationSupport
import Yulang.GeneralNominalVersionedAggregateRealization236
import Yulang.GeneralNominalVersionedMixedKernel234

set_option backward.isDefEq.respectTransparency false
/-! Origin of every new raw name and child output in an actual versioned
installation. Internal binder/center names are not raw domain allocations. -/
namespace Yulang.GeneralVersionedInstallDomain313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalState (sources atomSources typeSources extend)
open GeneralNominalSaturationState (Packet)
open GeneralNominalAllocationSupport (Endpoints report_endpoints cross_sources checks_sources
  equation_sources lower_sources upper_sources occurrences_endpoints extend_sources)
open GeneralNominalVersionedAllocation231 (reserved input_keys aggregate_reserved)
open GeneralNominalVersionedAggregateRealization236 (entries member_iff)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralNominalCommonBridge (Assignment)

abbrev reserve (p : Packet roles) : List Nat :=
  reserved p.context.state p.registry p.site.occurrence.identity p.bindings

def pool (p : Packet roles) : List Nat := sources p.context.state ++ reserve p

theorem extension_endpoints (p : Packet roles) : Endpoints p.bindings (pool p) := by
  intro pair member
  have support := report_endpoints p.context.state (GeneralNominalPacketSupport.report p) pair member
  exact ⟨List.mem_append_left _ support.1,List.mem_append_left _ support.2⟩

theorem merge_atom (p : Packet roles) (visible : p.declaration ∈ p.registry.declarations)
    (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ GeneralNominalVersionedAllocation231.merges p.context.state p.registry
      p.site.occurrence.identity p.declaration p.bindings) :
    atomSources atom ⊆ pool p := by
  rw [GeneralNominalVersionedAggregateEntries236.atoms_eq] at member
  obtain ⟨entry,present,atomMem⟩ := List.mem_flatMap.mp member
  obtain ⟨name,declared,_,lower | upper⟩ := (member_iff ..).mp present
  · rw [lower] at atomMem
    exact equation_sources _ _ (List.mem_append_right _ (aggregate_reserved visible declared).1)
      (lower_sources _ (occurrences_endpoints (extension_endpoints p) name)) atom atomMem
  · rw [upper] at atomMem
    exact equation_sources _ _ (List.mem_append_right _ (aggregate_reserved visible declared).2)
      (upper_sources _ (occurrences_endpoints (extension_endpoints p) name)) atom atomMem

theorem replay_sources (p : Plan roles) (visible : p.packet.declaration ∈ p.packet.registry.declarations) :
    sources (replayPlan p).packet.context.state ⊆ pool p.packet := by
  apply extend_sources p.packet.context.state (reserve p.packet)
    (GeneralNominalVersionedInstallation231.atoms p.packet) (fun _ h => List.mem_append_left _ h)
    (fun _ h => List.mem_append_right _ h)
  intro atom member
  rcases List.mem_append.mp member with before | last
  · rcases List.mem_append.mp before with cross | merge
    · exact cross_sources (extension_endpoints p.packet) atom cross
    · exact merge_atom p.packet visible atom merge
  · exact checks_sources _ _ (fun _ h => List.mem_append_left _ h) atom last

theorem declaration_owner (bindings : GeneralNominalAllocation.Bindings)
    (member : k ∈ GeneralNominalVersionedAllocation231.declarationKeys owner decl bindings) : k.1 = owner := by
  simp only [GeneralNominalVersionedAllocation231.declarationKeys,List.mem_append] at member
  rcases member with (ins|outs)|kids
  · obtain ⟨n,_,p⟩ := List.mem_flatMap.mp ins
    simp only [List.mem_cons,List.not_mem_nil,or_false] at p
    rcases p with rfl|rfl <;> rfl
  · obtain ⟨n,_,rfl⟩ := List.mem_map.mp outs
    rfl
  · obtain ⟨clause,_,within⟩ := List.mem_flatMap.mp kids
    simp only [List.mem_append,List.mem_cons] at within
    rcases within with (rfl|arguments)|outputs
    · rfl
    · obtain ⟨idx,_,atIndex⟩ := List.mem_flatMap.mp arguments
      simp only [List.mem_cons,List.not_mem_nil,or_false] at atIndex
      rcases atIndex with rfl|rfl <;> rfl
    · obtain ⟨eq,_,rfl⟩ := List.mem_map.mp outputs
      rfl

theorem reserve_owner (p : Packet roles) {k : GeneralNominalIdentities.Origin}
    (inside : GeneralNominalIdentities.source p.context.state.seed k ∈ reserve p) :
    k.1 = p.site.occurrence.identity := by
  obtain ⟨origin,original,equal⟩ := List.mem_map.mp inside
  have same := (GeneralNominalIdentities.source_identity p.context.state.seed origin k).mp equal
  subst origin
  obtain ⟨decl,_,inDecl⟩ := List.mem_flatMap.mp original
  exact declaration_owner _ inDecl

end Yulang.GeneralVersionedInstallDomain313
