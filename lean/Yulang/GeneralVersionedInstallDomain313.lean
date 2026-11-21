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


theorem output_key (visible : decl ∈ registry.declarations) (output : name ∈ decl.outputNames) :
    GeneralNominalAllocation.origin owner decl.id 2 name 0 ∈
      GeneralNominalVersionedAllocation231.keys registry owner b :=
  List.mem_flatMap.mpr ⟨decl,visible,List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨name,output,rfl⟩))⟩

theorem child_output_key (visible : decl ∈ registry.declarations)
    (required : clause ∈ decl.requirements) (output : equation ∈ clause.outputs) :
    GeneralNominalAllocation.origin owner decl.id 5 equation.id 0 ∈
      GeneralNominalVersionedAllocation231.keys registry owner b :=
  List.mem_flatMap.mpr ⟨decl,visible,List.mem_append_right _
    (List.mem_flatMap.mpr ⟨clause,required,List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.mpr ⟨equation,output,rfl⟩))⟩)⟩

theorem output_reserved (p : Plan roles) (visible : p.packet.declaration ∈ p.packet.registry.declarations)
    (site : Site roles) (emitted : site ∈ GeneralNominalVersionedChildren232.emitted p)
    (output : GeneralSourceState.Output) (requested : output ∈ site.occurrence.demand.outputs) :
    output.target ∈ reserve p.packet := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
  have required : clause.val ∈ p.packet.declaration.requirements :=
    (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  obtain ⟨equation,present,rfl⟩ := List.mem_map.mp requested
  change GeneralDeclarationDemands.outputTarget p.packet.declaration
    (GeneralNominalVersionedFrame231.capture p.packet)
    ((GeneralNominalVersionedFrame231.frame p.packet).allocation p.packet.declaration.id clause.val).outputs equation ∈ reserve p.packet
  unfold GeneralDeclarationDemands.outputTarget
  split
  · split
    · rename_i name eq declared
      exact GeneralNominalVersionedAllocation231.reserved_key (output_key visible declared)
    · exact GeneralNominalVersionedAllocation231.reserved_key (child_output_key visible required present)
  · exact GeneralNominalVersionedAllocation231.reserved_key (child_output_key visible required present)


theorem declaration_purpose {k : GeneralNominalIdentities.Origin}
    (member : k ∈ GeneralNominalVersionedAllocation231.declarationKeys owner decl b) : k.2.2.1 ≤ 6 := by
  simp only [GeneralNominalVersionedAllocation231.declarationKeys,List.mem_append] at member
  rcases member with (ins|outs)|kids
  · obtain ⟨n,_,pair⟩ := List.mem_flatMap.mp ins
    simp only [List.mem_cons,List.not_mem_nil,or_false] at pair
    rcases pair with rfl|rfl <;> simp [GeneralNominalAggregateVersion231.key,GeneralNominalAllocation.origin]
  · obtain ⟨n,_,rfl⟩ := List.mem_map.mp outs
    simp [GeneralNominalAllocation.origin]
  · obtain ⟨clause,_,within⟩ := List.mem_flatMap.mp kids
    simp only [List.mem_append,List.mem_cons] at within
    rcases within with (rfl|arguments)|outputs
    · simp [GeneralNominalAllocation.origin]
    · obtain ⟨idx,_,atIndex⟩ := List.mem_flatMap.mp arguments
      simp only [List.mem_cons,List.not_mem_nil,or_false] at atIndex
      rcases atIndex with rfl|rfl <;> simp [GeneralNominalAllocation.origin]
    · obtain ⟨eq,_,rfl⟩ := List.mem_map.mp outputs
      simp [GeneralNominalAllocation.origin]

theorem reserve_purpose (p : Packet roles) {k : GeneralNominalIdentities.Origin}
    (inside : GeneralNominalIdentities.source p.context.state.seed k ∈ reserve p) : k.2.2.1 ≤ 6 := by
  obtain ⟨origin,original,equal⟩ := List.mem_map.mp inside
  have same := (GeneralNominalIdentities.source_identity p.context.state.seed origin k).mp equal
  subst origin
  obtain ⟨decl,_,inDecl⟩ := List.mem_flatMap.mp original
  exact declaration_purpose inDecl

theorem head_sources (p : Packet roles) (visible : p.declaration ∈ p.registry.declarations) :
    (GeneralNominalVersionedInstallation231.atoms p).flatMap atomSources ⊆ pool p := by
  intro n h
  obtain ⟨atom,member,inside⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp member with before|last
  · rcases List.mem_append.mp before with cross|merge
    · exact cross_sources (extension_endpoints p) atom cross inside
    · exact merge_atom p visible atom merge inside
  · exact checks_sources _ _ (fun _ h => List.mem_append_left _ h) atom last inside

end Yulang.GeneralVersionedInstallDomain313
