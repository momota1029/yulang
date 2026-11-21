import Yulang.GeneralWhereOriginJoint318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 19000000
namespace Yulang.GeneralWhereOriginInstall318
open GeneralNominalCenters (Plan)
open GeneralNominalCandidates (Context)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralWhereVersionInstall317 (Journal Models install InstallStep)
open GeneralWhereOriginTrace318 (Trace rawOf)
open GeneralWhereOriginDelta318 (Delta)
open GeneralWhereOriginJoint318 (VisibleReads ChildRows guard new_certificate)
open GeneralWhereOriginReady318 (HeadReady)
open GeneralWhereOriginAssemble318 (ActualRows)
open GeneralWhereOriginPartition318 (allClassified)
open GeneralWhereOriginSuccessor318 (SilentChildren with_parent)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralWhereVersionCompiler317 (children)
open GeneralNominalCenteredHeadWFSource (DeclarationCovered)
open GeneralNominalSaturationState (Generated)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)

/-- Exact residual raw obligation. Delta checks identities and layout,
not whether the proposed new raw observations denote the solved model. -/
def RawTicket (j : Journal rs) (p : Plan rs) (ctx : Context) : Prop :=
  ∀ m, Models j m → Holds p m → GeneralNominalState.Models ctx.state m

theorem generated_append (j : Journal rs) (p : Plan rs) (ctx : Context) {d}
    (now : d ∈ children p) : Generated (install j ctx p).mixed.core.erased.current p.packet.site.occurrence d := by
  apply Generated.child .root
  change (p.packet.site.occurrence,d) ∈ j.mixed.core.erased.current.edges ++ (children p).map _
  exact List.mem_append_right _ (List.mem_map.mpr ⟨d,now,rfl⟩)

/-- A proved bridge into one actual isolated install. It treats raw
soundness, authorized prior choice, and source interval reads as named
premises rather than manufacturing a post-journal model. -/
theorem executes {j : Journal rs} {p : Plan rs} {ctx : Context}
    (checked : (boundary rs).Checked r) (trace : Trace r j)
    (frame : Frame (Compiled r) j.mixed.core p.packet.site.occurrence p.packet.declaration.id p)
    (selected : Local r j.mixed p.packet.site.occurrence
      (.selected p.packet.declaration.id (GeneralNominalVersionedFrame231.children p.packet)))
    (compatible : GeneralNominalCycleSteps.ChoiceCompatible j.mixed.core.erased.current p.packet)
    (layout : Delta (rawOf j) ctx.state p)
    (interpretation : ctx.interpretation = j.mixed.core.erased.current.context.interpretation)
    (classified : allClassified j p (guard j p) = true)
    (cover : DeclarationCovered p.packet.registry.constructors p.packet.context.interpretation p.packet.declaration)
    (reads : VisibleReads p) (silent : SilentChildren p) (raw : RawTicket j p ctx)
    (m : Assignment) (valid : Models j m) (ready : HeadReady j p m)
    (actual : ActualRows p m) (childRows : ChildRows p m) :
    InstallStep r j (install j ctx p) ∧ Trace r (install j ctx p) ∧
    (∃ n, Models j n ∧ Models (install j ctx p) n ∧ Agree (journalSources j ++ guard j p) m n) ∧
    (∀ d ∈ children p, Generated (install j ctx p).mixed.core.erased.current p.packet.site.occurrence d) := by
  obtain ⟨n,prior,head,plan,agrees⟩ :=
    new_certificate checked trace frame classified cover reads m valid ready actual childRows
  have modeled := with_parent prior (raw n prior plan) plan head.effects silent
  have step : InstallStep r j (install j ctx p) :=
    .whereRow ctx p checked frame selected compatible layout.refinement interpretation ⟨n,prior,modeled⟩
  exact ⟨step,.placed ctx p trace step layout,⟨n,prior,modeled,agrees⟩,fun _ => generated_append j p ctx⟩

end Yulang.GeneralWhereOriginInstall318
