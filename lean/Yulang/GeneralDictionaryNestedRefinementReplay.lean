import Yulang.GeneralDictionaryNestedRefinement
import Yulang.GeneralDictionaryBindingSchemaReplay

/-! Named-schema replay after a source-preserving carrier refinement for
arbitrary finished finite nominal-variable query trees. -/
namespace Yulang.GeneralDictionaryNestedRefinementReplay
open GeneralNominalRecursiveInspection GeneralNominalInspection
open GeneralNominalRecursiveCandidates
open GeneralDictionaryNestedRefinement
open GeneralNominalRefinements
open GeneralNominalSaturationState

theorem queries_preserved (a b : Context) (r : Refines a.state b.state)
 (interpretation : b.interpretation = a.interpretation) (declaration : GeneralDeclarations.Declaration) :
 queries b.state b.interpretation declaration = queries a.state a.interpretation declaration := by
 unfold queries
 rw [r.constructors,interpretation]

theorem report_refined (a b : Context) (r : Refines a.state b.state)
 (interpretation : b.interpretation = a.interpretation) (declaration : GeneralDeclarations.Declaration)
 (bounds : List (Bounds a.state))
 (scope : NominalOnlyMany (queries a.state a.interpretation declaration))
 (done : Finished (report a declaration bounds)) :
 report b declaration (bounds.map (mapBounds r.base.embed)) = mapReport r.base.embed (report a declaration bounds) := by
 unfold report at *
 rw [queries_preserved a b r interpretation declaration]
 rw [inspectMany_refined a.state b.state r _ bounds (fun _ => none) 0 scope done]
 simp [mapReport,List.map_append]

theorem bindings_preserved (a b : Context) (r : Refines a.state b.state)
 (interpretation : b.interpretation = a.interpretation) (declaration : GeneralDeclarations.Declaration)
 (bounds : List (Bounds a.state))
 (scope : NominalOnlyMany (queries a.state a.interpretation declaration))
 (done : Finished (report a declaration bounds)) :
 bindings b.state (report b declaration (bounds.map (mapBounds r.base.embed))) =
 bindings a.state (report a declaration bounds) := by
 rw [report_refined a b r interpretation declaration bounds scope done,bindings_map]

theorem recorded_schema (root : GeneralSourceDictionaries.Occurrence roles)
 (state : GeneralNominalSupport.Tracked roles) (packet : Packet roles)
 (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
 (recorded : packet ∈ state.current.packets)
 (refinement : Refines packet.context.state state.current.context.state)
 (interpretation : state.current.context.interpretation = packet.context.interpretation)
 (scope : NominalOnlyMany (queries packet.context.state packet.context.interpretation packet.declaration))
 (done : Finished (report packet.context packet.declaration packet.bounds))
 (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
 let currentBounds := packet.bounds.map (mapBounds refinement.base.embed)
 GeneralNominalMaterialization.Models state.current.context.state packet.declaration
   (GeneralNominalAllocation.capture state.current.context.state packet.registry packet.site.occurrence.identity
     packet.declaration.id (bindings state.current.context.state
       (report state.current.context packet.declaration currentBounds)))
   (report state.current.context packet.declaration currentBounds)
   (generated packet.registry state.current.context packet.site.occurrence packet.declaration packet.checked currentBounds) model := by
 apply GeneralDictionaryBindingSchemaReplay.replay packet.registry root state reachable packet recorded
 · exact bindings_preserved packet.context state.current.context refinement interpretation packet.declaration packet.bounds scope done
 · intro entry member captured present same actual origin known
   rw [report_refined packet.context state.current.context refinement interpretation packet.declaration packet.bounds scope done] at present
   obtain ⟨old,oldMember,names,origins⟩ := origins_map _ _ _ present
   exact ⟨old,oldMember,names,origins.trans known⟩
 · exact valid

end Yulang.GeneralDictionaryNestedRefinementReplay
