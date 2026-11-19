import Yulang.GeneralRebaseAllWidthSafety275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 8000000
namespace Yulang.GeneralRebaseAllWidthSelected275
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry sourceRegistry declaration declaration_checked checked)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralRebaseAllWidthRealized275 (successor)
open GeneralRebaseAllWidthPlan275 (packet plan children_empty located)
open GeneralRebaseAllWidthFrame275 (frame raw_sites edges_empty)
open GeneralRebaseAllWidthPacket275 (packet_holds)
open GeneralRebaseAllWidthStable275 (ready classes stable evidence)
open GeneralRebaseAllWidthSafety275 (retained_model safe known)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedCandidates231 (Survivor Unique)

theorem survivor : Survivor registry successor.core.erased.current.context root declaration.id [] :=
 ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,packet.bounds,
   located,frame.prepared,children_empty.symm⟩

theorem unique : Unique registry successor.core.erased.current.context root declaration.id [] := by
 refine ⟨survivor,?_⟩
 intro key kids other
 have copy := other
 obtain ⟨_,d,visible,_,identity,_⟩ := other
 cases List.mem_singleton.mp visible
 have same : key = declaration.id := identity.symm
 subst key
 exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

theorem equal_outputs (m : Assignment) (focus : GeneralSourceDictionaries.Occurrence roles) :
 GeneralNominalCenteredHeadOutputs.EqualOutputs successor.core focus m := by
 intro first one last two _
 obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp one
 rw [raw_sites] at present
 cases List.mem_singleton.mp present
 cases List.mem_singleton.mp within
 obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp two
 rw [raw_sites] at present
 cases List.mem_singleton.mp present
 cases List.mem_singleton.mp within
 exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry successor root
   (.selected declaration.id []) := by
 apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
 apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
 apply GeneralNominalVersionedDiagnosticLaws232.selected_of_model safe unique retained_model frame
   ready (packet_holds extended retained_model) (classes extended retained_model)
 exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict retained_model
   (fun focus _ => equal_outputs extended focus) (equal_outputs extended root)

theorem generated_only (generated : GeneralNominalSaturationState.Generated successor.core.erased.current root focus) :
 focus = root :=
 GeneralNominalVersionedMixedTerminalStable234.generated_only raw_sites edges_empty generated

theorem evidenceAt :
 B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry successor root := by
 intro assignment valid demand key children dictionaries reached _stable _childStable chosen given
 have same : demand = root := reached.elim id generated_only
 subst demand
 have same := B4TargetV8.local_functional chosen selected
 cases same
 cases given
 exact evidence assignment valid

theorem regression :
 B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root successor ∧
 Models successor extended ∧ GeneralNominalVersionedMixedKernel234.Stable registry successor root ∧
 GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry successor root (.selected declaration.id []) ∧
 B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry successor root :=
 ⟨GeneralRebaseAllWidthRealized275.reachable,retained_model,stable,selected,evidenceAt⟩

end Yulang.GeneralRebaseAllWidthSelected275
