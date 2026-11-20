import Yulang.GeneralNominalReportRecompute305
import Yulang.GeneralNominalTotalLocation304
import Yulang.GeneralNominalCenteredHeadMatPlanData

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalReportContext305
open GeneralNominalInspection (Bounds queries)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (Context report arguments)
open GeneralNominalReportCoordinates305 (Coordinates)
open GeneralNominalReportRecompute305 (many_exact)
open GeneralNominalReportSourceTransport (moveBounds moveReport moveCapture)
open GeneralNominalReportErasure (erase interval)
open GeneralNominalRefinements (Refines)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalSaturationState (Packet)
open GeneralNominalCenters (Plan)

structure EquivalentContexts (old next : Context) where
  forward : Refines old.state next.state
  backward : Refines next.state old.state
  geometry : Coordinates old.state next.state
  interpretation : old.interpretation = next.interpretation

variable {old next : Context}

theorem same_embedding (eq : EquivalentContexts old next) :
    eq.geometry.slot = eq.forward.base.embed := by
  funext i
  exact next.state.base.source_injective ((eq.geometry.source_eq i).trans (eq.forward.base.source i).symm)

theorem model_iff (eq : EquivalentContexts old next) (m : Assignment) :
    GeneralNominalState.Models old.state m ↔ GeneralNominalState.Models next.state m :=
  ⟨GeneralNominalRefinements.models eq.backward m,GeneralNominalRefinements.models eq.forward m⟩

theorem arguments_exact (eq : EquivalentContexts old next) (root : Occurrence roles) :
    arguments next root = (arguments old root).map (List.map (moveBounds eq.geometry.slot)) := by
  rw [same_embedding eq]
  exact GeneralNominalTotalLocation304.arguments_total old next eq.forward eq.backward root

theorem report_exact (eq : EquivalentContexts old next) (d : GeneralDeclarations.Declaration)
    (span : List (Bounds old.state)) :
    report next d (span.map (moveBounds eq.geometry.slot)) =
      moveReport eq.geometry.slot (report old d span) := by
  have q : queries next.state next.interpretation d = queries old.state old.interpretation d := by
    unfold queries
    rw [eq.forward.constructors,← eq.interpretation]
  unfold report
  rw [q,many_exact eq.geometry]
  simp [moveReport,List.map_append]

theorem interval_move {before after : GeneralNominalState.State} (rel : Coordinates before after)
    (bounds : Bounds before) : interval after (moveBounds rel.slot bounds) = interval before bounds := by
  simp [interval,moveBounds,rel.source_eq]

theorem erase_move {before after : GeneralNominalState.State} (rel : Coordinates before after)
    (data : Report before) : erase after (moveReport rel.slot data) = erase before data := by
  simp [erase,moveReport,moveCapture,List.map_map,Function.comp_def,interval_move]

theorem erase_report (eq : EquivalentContexts old next) (d : GeneralDeclarations.Declaration)
    (span : List (Bounds old.state)) :
    erase next.state (report next d (span.map (moveBounds eq.geometry.slot))) =
      erase old.state (report old d span) := by
  rw [report_exact eq,erase_move eq.geometry]

def movePacket (p : Packet roles) (eq : EquivalentContexts p.context next) : Packet roles :=
  ⟨p.registry,next,p.site,p.declaration,p.checked,p.bounds.map (moveBounds eq.geometry.slot)⟩

def movePlan (p : Plan roles) (eq : EquivalentContexts p.packet.context next) : Plan roles :=
  ⟨movePacket p.packet eq,p.input,p.input_exact⟩

theorem same_plan (p : Plan roles) (eq : EquivalentContexts p.packet.context next) :
    Same p (movePlan p eq) :=
  ⟨rfl,rfl,rfl,eq.forward.seed.symm,eq.forward.constructors.symm,eq.interpretation,
    (erase_report eq p.packet.declaration p.packet.bounds).symm⟩

end Yulang.GeneralNominalReportContext305
