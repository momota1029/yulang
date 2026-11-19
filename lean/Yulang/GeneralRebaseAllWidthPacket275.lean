import Yulang.GeneralRebaseAllWidthPlan275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 7600000
namespace Yulang.GeneralRebaseAllWidthPacket275

open GeneralRebaseAllWidthPlan275
open GeneralRebaseAllWidthCertificate275 (context)
open GeneralRebaseAllWidthRealized275 (successor model_exact)
open GeneralRebaseAllWidthRegistration275 (embed)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralDictionaryVersionedPointStage233 (allocated reserved ordinary)


def mapBounds {before after : GeneralNominalState.State}
 (mapping : Fin before.base.slots → Fin after.base.slots) (item : GeneralNominalInspection.Bounds before) :
 GeneralNominalInspection.Bounds after := (mapping item.1,mapping item.2)

def mapCapture {before after : GeneralNominalState.State}
 (mapping : Fin before.base.slots → Fin after.base.slots) (item : Capture before) : Capture after :=
 ⟨item.name,mapBounds mapping item.bounds,item.origin⟩

def mapReport {before after : GeneralNominalState.State}
 (mapping : Fin before.base.slots → Fin after.base.slots) (item : Report before) : Report after :=
 ⟨item.captures.map (mapCapture mapping),item.inspected.map (mapBounds mapping),
   item.checked.map (mapBounds mapping),item.blocked.map (mapBounds mapping),
   item.conflicts.map (mapBounds mapping),item.arity,
   item.anchors.map (fun pair => (pair.1,mapBounds mapping pair.2)),item.tests⟩

theorem mapped_checks {before after : GeneralNominalState.State}
 (refinement : GeneralNominalRefinements.Refines before after) (report : Report before) :
 selfChecks after (mapReport refinement.base.embed report) = selfChecks before report := by
 simp [selfChecks,mapReport,mapBounds,List.map_map,refinement.base.source]

theorem mapped_projection {before after : GeneralNominalState.State}
 (refinement : GeneralNominalRefinements.Refines before after) (report : Report before) (m : Assignment) :
 ProjectionModels after (mapReport refinement.base.embed report) m ↔ ProjectionModels before report m := by
 simp only [ProjectionModels,mapReport,List.forall_mem_map,mapCapture,Fits,mapBounds,refinement.base.source]

noncomputable def old_refines : GeneralNominalRefinements.Refines retained.packet.context.state context.state :=
 { GeneralRebaseAllWidthRefinement275.refines with
   ordinary := fun _ member => List.mem_append_left _ member
   reserved := fun _ member => List.mem_append_left _ member
   allocated := fun _ member => List.mem_append_left _ member }

theorem report_transport :
 GeneralNominalPacketSupport.report packet =
 mapReport old_refines.base.embed (GeneralNominalPacketSupport.report retained.packet) := by
 change GeneralNominalRecursiveCandidates.report context _ [((0 : Fin 8),(0 : Fin 8))] =
   mapReport old_refines.base.embed
     (GeneralNominalRecursiveCandidates.report (GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary)
       _ [(0,0)])
 rw [report_exact,GeneralDictionaryOptionalCurrent229.report_exact]
 rfl

theorem same_bindings : packet.bindings = retained.packet.bindings := by
 rw [bindings_exact,GeneralDictionaryVersionedPoint233.bindings_exact]

theorem ordinary_exact (m : Assignment) : Ordinary packet m ↔ Ordinary retained.packet m := by
 unfold Ordinary
 rw [same_bindings,report_transport,mapped_checks old_refines]
 rfl

theorem projection_exact (m : Assignment) :
 ProjectionModels packet.context.state (GeneralNominalPacketSupport.report packet) m ↔
 ProjectionModels retained.packet.context.state (GeneralNominalPacketSupport.report retained.packet) m := by
 rw [report_transport]
 exact mapped_projection old_refines _ m

theorem same_schema_models (m : Assignment) (schema : GeneralNominalMaterialization.Schema) :
 SchemaHolds plan schema m ↔ SchemaHolds retained schema m := by
 unfold SchemaHolds
 have capture : GeneralNominalVersionedFrame231.capture packet =
   GeneralNominalVersionedFrame231.capture retained.packet := unchanged_capture
 simp only [unchanged_binder,capture]

theorem inputs_exact (m : Assignment) : Inputs plan m ↔ Inputs retained m := by
 unfold Inputs
 rw [ordinary_exact,projection_exact,unchanged_head,same_schema_models,unchanged_schema]
 have variables := funext (fun mode => funext (unchanged_variables m mode))
 rw [variables]
 have capture : GeneralNominalVersionedFrame231.capture packet =
   GeneralNominalVersionedFrame231.capture retained.packet := unchanged_capture
 have needed (name) : GeneralNominalSharedCaptures.Needed packet name ↔
     GeneralNominalSharedCaptures.Needed retained.packet name := Iff.rfl
 simp only [capture,needed,unchanged_binder]
 constructor <;> rintro ⟨a,b,c,d,e,f,_⟩ <;> exact ⟨a,b,c,d,e,f,fun _ h => False.elim (List.not_mem_nil h)⟩

theorem outputs_exact (m : Assignment) : Outputs plan m ↔ Outputs retained m := by
 unfold Outputs
 rw [unchanged_schema,funext (fun mode => funext (unchanged_variables m mode))]

theorem packet_holds (m : Assignment) (valid : Models successor m) : Holds plan m := by
 have previous : Holds retained m := (model_exact m |>.mp valid).2.1 _ List.mem_cons_self
 exact ⟨valid.1.1,(inputs_exact m).mpr previous.2.1,(outputs_exact m).mpr previous.2.2⟩

end Yulang.GeneralRebaseAllWidthPacket275
