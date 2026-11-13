import Yulang.GeneralDictionaryNestedRefinementReplay

/-! Complete current private/projection/schema branch validity for recorded
finished nominal-variable inspections under source-preserving refinement. -/
namespace Yulang.GeneralDictionaryNestedBranchTransport
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Bounds queries)
open GeneralNominalRecursiveCandidates
open GeneralDictionaryNestedRefinement GeneralDictionaryNestedRefinementReplay
open GeneralNominalRefinements GeneralNominalSaturationState

theorem projection_map {a b : GeneralNominalState.State} (r : Refines a b)
 (report : Report a) (model : GeneralNominalCommonBridge.Assignment) :
 ProjectionModels b (mapReport r.base.embed report) model ↔ ProjectionModels a report model := by
 simp only [ProjectionModels,mapReport,List.forall_mem_map,mapCapture,mapBounds,Fits,r.base.source]

theorem selfChecks_map {a b : GeneralNominalState.State} (r : Refines a b) (report : Report a) :
 selfChecks b (mapReport r.base.embed report) = selfChecks a report := by
 simp [selfChecks,mapReport,mapBounds,List.map_map,Function.comp_def,r.base.source]

theorem merges_seed (a b : GeneralNominalState.State) (seed : b.seed = a.seed)
 (registry : GeneralDeclarations.Registry) (root : Nat) (declaration : GeneralDeclarations.Declaration)
 (bindings : GeneralNominalAllocation.Bindings) :
 GeneralNominalAllocation.merges b registry root declaration bindings =
 GeneralNominalAllocation.merges a registry root declaration bindings := by
 unfold GeneralNominalAllocation.merges
 rw [GeneralDictionaryBindingSchemaReplay.capture_seed a b seed]

theorem private_refined (a b : Context) (r : Refines a.state b.state)
 (interpretation : b.interpretation = a.interpretation)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (declaration : GeneralDeclarations.Declaration) (bounds : List (Bounds a.state))
 (scope : NominalOnlyMany (queries a.state a.interpretation declaration))
 (done : Finished (report a declaration bounds))
 (model : GeneralNominalCommonBridge.Assignment)
 (current : GeneralNominalState.Models b.state model)
 (old : GeneralNominalState.Models (privateState registry a root declaration bounds) model) :
 GeneralNominalState.Models (privateState registry b root declaration (bounds.map (mapBounds r.base.embed))) model := by
 unfold privateState at old ⊢
 have oldParts := (GeneralNominalState.extend_models ..).mp old
 have oldProp := (GeneralNominalAllocation.propagate_models ..).mp oldParts.1
 rw [report_refined a b r interpretation declaration bounds scope done,bindings_map,selfChecks_map]
 apply (GeneralNominalState.extend_models ..).mpr
 refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨current,oldProp.2.1,?_⟩,oldParts.2⟩
 rw [merges_seed a.state b.state r.seed]
 exact oldProp.2.2

theorem recorded_branch (root : GeneralSourceDictionaries.Occurrence roles)
 (state : GeneralNominalSupport.Tracked roles) (packet : Packet roles)
 (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
 (recorded : packet ∈ state.current.packets)
 (refinement : Refines packet.context.state state.current.context.state)
 (interpretation : state.current.context.interpretation = packet.context.interpretation)
 (scope : NominalOnlyMany (queries packet.context.state packet.context.interpretation packet.declaration))
 (done : Finished (report packet.context packet.declaration packet.bounds))
 (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
 BranchModels packet.registry state.current.context packet.site.occurrence packet.declaration packet.checked
 (packet.bounds.map (mapBounds refinement.base.embed)) model := by
 have old := valid.2.1 packet recorded
 refine ⟨private_refined packet.context state.current.context refinement interpretation packet.registry
   packet.site.occurrence packet.declaration packet.bounds scope done model valid.1 old.1,?_,
   recorded_schema root state packet reachable recorded refinement interpretation scope done model valid⟩
 rw [report_refined packet.context state.current.context refinement interpretation packet.declaration packet.bounds scope done]
 exact (projection_map refinement _ model).mpr old.2.1
end Yulang.GeneralDictionaryNestedBranchTransport
