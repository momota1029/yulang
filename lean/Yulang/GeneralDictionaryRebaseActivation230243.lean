import Yulang.GeneralNominalRebaseActivation243
import Yulang.GeneralDictionaryRebase230Private241
import Yulang.GeneralNominalRebaseEscapedMerges242
set_option backward.isDefEq.respectTransparency false
/-! Checked activation on the concrete 230 raw nominal snapshot, with its
private cells already reserved. This is a local singleton/repeated merge
regression, not a report-changing reachable kernel path. -/
namespace Yulang.GeneralDictionaryRebaseActivation230243
open GeneralDictionaryJournalRefinement228Source (snapshot root roles)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryOptionalInstall229 (model lo hi actual)
open GeneralDictionaryRebase230Private241
open GeneralNominalRebaseActivation243
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseDefinitions241 (entries)
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)

def singletonBindings : GeneralNominalAllocation.Bindings := [(0,2,2)]
abbrev newEntries := entries snapshot.seed root.identity declaration.id newBindings declaration.inputNames
abbrev site : Site roles := rootSite snapshot.seed root
def sites : List (Site roles) := [site]
def raw : GeneralNominalState.State :=
 { snapshot with reserved := [lo,hi],allocated := GeneralNominalAllocation.keys registry root.identity }

theorem already_reserved : lo ∈ raw.reserved ∧ hi ∈ raw.reserved := by simp [raw]

theorem old_entries_empty : entries snapshot.seed root.identity declaration.id singletonBindings declaration.inputNames = [] := rfl

theorem old_merges_empty : GeneralNominalAllocation.merges raw registry root.identity declaration singletonBindings = [] := rfl

theorem raw_reads : GeneralDictionaryDefaultRawSupport213.sources raw =
 GeneralDictionaryDefaultRawSupport213.sources snapshot := rfl

theorem site_sources : siteSources site = [0,0,0] := rfl

theorem read_pool (name : Nat) (member : name ∈ reads raw publicAtoms sites) : name ∈ pool := by
 rcases List.mem_append.mp member with earlier | live
 · rcases List.mem_append.mp earlier with source | atom
   · apply raw_support name
     exact GeneralDictionaryDefaultRawSupport213.subset snapshot source
   · obtain ⟨atom,present,source⟩ := List.mem_flatMap.mp atom
     exact public_support atom present name source
 · obtain ⟨site,present,source⟩ := List.mem_flatMap.mp live
   cases List.mem_singleton.mp present
   rw [site_sources] at source
   have zero : name = 0 := by simpa using source
   subst name
   simp [pool]

theorem checked : Checked newEntries raw publicAtoms sites := by
 intro entry member present
 exact GeneralNominalRebaseDefinitions241.entries_fresh snapshot.seed root.identity declaration.id
   newBindings declaration.inputNames isolated entry member (read_pool entry.1 present)

theorem external_entries : External newEntries :=
 GeneralNominalRebaseEscapedMerges242.external_entries _ _ _ _ _ isolated linked

theorem original_consumers : Consumers raw publicAtoms sites model := by
 refine ⟨GeneralDictionaryOptionalInstall229.source_model,old_public,?_⟩
 intro current member index
 cases List.mem_singleton.mp member
 change CommonNominalFullCarrier.Subtype (model 0).1 (model 0).1 ∧
   CommonNominalFullCarrier.Subtype (model 0).1 (model 0).1
 exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem activation : Preserves newEntries rebased model ∧ Definitions newEntries rebased ∧
 Consumers raw publicAtoms sites rebased ∧
 GeneralNominalRebaseLiveLabels241.CentersAgree sites rebased model :=
 activate newEntries (GeneralNominalRebaseDefinitions241.coherent snapshot.seed root.identity declaration.id newBindings declaration.inputNames) external_entries
   raw publicAtoms sites checked model original_consumers

theorem exact_projection (sourceModel : Assignment) : Consumers raw publicAtoms sites sourceModel ↔
 ∃ next, Preserves newEntries next sourceModel ∧ Definitions newEntries next ∧
 Consumers raw publicAtoms sites next ∧ GeneralNominalRebaseLiveLabels241.CentersAgree sites next sourceModel :=
 projection_iff newEntries (GeneralNominalRebaseDefinitions241.coherent snapshot.seed root.identity declaration.id newBindings declaration.inputNames) external_entries
   raw publicAtoms sites checked sourceModel

theorem actual_fits_retained : GeneralNominalRebaseProjection241.CapturedFits snapshot registry root.identity
 declaration newBindings (fun _ => actual) rebased := actual_fits
end Yulang.GeneralDictionaryRebaseActivation230243
