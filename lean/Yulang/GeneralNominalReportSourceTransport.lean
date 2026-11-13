import Yulang.GeneralNominalMaterialization

/-! Source-preserving relocation of a computed inspection report. These lemmas
transport semantic obligations, not the inspection algorithm itself. A client
must separately prove its fresh report equals the relocated report. -/
namespace Yulang.GeneralNominalReportSourceTransport
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Bounds)
open GeneralNominalCommonBridge (Assignment)
variable {before after : GeneralNominalState.State}

def moveBounds (slots : Fin before.base.slots → Fin after.base.slots)
    (bounds : Bounds before) : Bounds after := (slots bounds.1,slots bounds.2)

def moveCapture (slots : Fin before.base.slots → Fin after.base.slots)
    (capture : Capture before) : Capture after :=
  ⟨capture.name,moveBounds slots capture.bounds,capture.origin⟩

def moveReport (slots : Fin before.base.slots → Fin after.base.slots)
    (report : Report before) : Report after where
  captures := report.captures.map (moveCapture slots)
  inspected := report.inspected.map (moveBounds slots)
  checked := report.checked.map (moveBounds slots)
  blocked := report.blocked.map (moveBounds slots)
  conflicts := report.conflicts.map (moveBounds slots)
  arity := report.arity
  anchors := report.anchors.map fun anchor => (anchor.1,moveBounds slots anchor.2)
  tests := report.tests

 theorem bindings_preserved (slots : Fin before.base.slots → Fin after.base.slots)
    (sources : ∀ slot, after.base.source (slots slot) = before.base.source slot)
    (report : Report before) :
    bindings after (moveReport slots report) = bindings before report := by
  simp only [bindings,moveReport,List.map_map,Function.comp_def,moveCapture,moveBounds,sources]

 theorem selfChecks_preserved (slots : Fin before.base.slots → Fin after.base.slots)
    (sources : ∀ slot, after.base.source (slots slot) = before.base.source slot)
    (report : Report before) :
    selfChecks after (moveReport slots report) = selfChecks before report := by
  simp only [selfChecks,moveReport,List.map_map,Function.comp_def,moveBounds,sources]

 theorem finished_iff (slots : Fin before.base.slots → Fin after.base.slots)
    (report : Report before) : Finished (moveReport slots report) ↔ Finished report := by
  simp [Finished,moveReport]

 theorem projections_iff (slots : Fin before.base.slots → Fin after.base.slots)
    (sources : ∀ slot, after.base.source (slots slot) = before.base.source slot)
    (report : Report before) (model : Assignment) :
    ProjectionModels after (moveReport slots report) model ↔ ProjectionModels before report model := by
  simp only [ProjectionModels,moveReport,List.forall_mem_map,moveCapture,moveBounds,Fits,sources]

 theorem materialization_iff (slots : Fin before.base.slots → Fin after.base.slots)
    (report : Report before) (declaration : GeneralDeclarations.Declaration)
    (capture : GeneralDeclarationDemands.Capture) (schema : GeneralNominalMaterialization.Schema)
    (model : Assignment) :
    GeneralNominalMaterialization.Models after declaration capture (moveReport slots report) schema model ↔
    GeneralNominalMaterialization.Models before declaration capture report schema model := by
  simp [GeneralNominalMaterialization.Models,moveReport,moveCapture]
end Yulang.GeneralNominalReportSourceTransport
