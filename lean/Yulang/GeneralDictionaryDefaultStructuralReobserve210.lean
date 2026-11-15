import Yulang.GeneralNominalFinishedObservation197
import Yulang.GeneralNominalReobservationSteps
import Yulang.GeneralNominalReportErasure

set_option backward.isDefEq.respectTransparency false

/-! Successful nonnominal observations survive genuine descriptor revisions.
No semantic certificate or descriptor-preserving refinement is assumed. -/
namespace Yulang.GeneralDictionaryDefaultStructuralReobserve210
open GeneralNominalInspection (Query Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalInspectionTrace197
open GeneralNominalReobservationSteps
open GeneralNominalFinishedObservation197 (finished_visit finished_append)

inductive Syntax : Query → Prop where
  | variables : Syntax (.variables names)
  | scalar : Syntax (.scalar expected)
  | node (children : ∀ query ∈ patterns, Syntax query) : Syntax (.node expected patterns)

 def view (revision : Revision state) : GeneralNominalViewTransport196.View state.context.state :=
  ⟨state.context.state.view,revision.entries,revision.catalogue,revision.opaqueHeads⟩

mutual
 theorem traced (revision : Revision state) (shape : Syntax query)
    (finished : Finished (inspect state.context.state query bounds origin)) :
    Trace state.context.state (view revision) query bounds := by
  cases shape with
  | variables => exact .variables
  | scalar =>
    simp only [inspect,finished_visit] at finished
    cases nominal : state.context.state.nominals bounds.1 with
    | some descriptor => simp [nominal,Finished] at finished
    | none =>
      simp only [nominal] at finished
      cases head : state.context.state.view.heads bounds.1 <;> simp only [head] at finished
      all_goals try solve | cases finished.1 | cases finished.2.1
      next actual =>
        split at finished
        next same =>
          subst actual
          exact .scalar nominal ((revision.domain _).mpr nominal) head head
        next different => cases finished.2.1
  | @node patterns expected children =>
    simp only [inspect,finished_visit] at finished
    cases lower : state.context.state.view.heads bounds.1 <;> simp only [lower] at finished
    all_goals try solve | cases finished.1 | cases finished.2.1
    next lowerKind left =>
      cases upper : state.context.state.view.heads bounds.2 <;> simp only [upper] at finished
      all_goals try solve | cases finished.1 | cases finished.2.1
      next upperKind right =>
        split at finished
        next shapes =>
          exact .structural lower upper lower upper shapes.1 shapes.2 shapes.1 shapes.2 rfl rfl
            (tracedMany revision children finished)
        next missing => cases finished.1
 termination_by sizeOf query

 theorem tracedMany (revision : Revision state)
    (shape : ∀ query ∈ queries, Syntax query)
    (finished : Finished (inspectMany state.context.state queries bounds origins index)) :
    Traces state.context.state (view revision) queries bounds := by
  cases queries with
  | nil =>
    cases bounds with
    | nil => exact .nil
    | cons head tail => simp [inspectMany,Finished] at finished
  | cons query queries =>
    cases bounds with
    | nil => simp [inspectMany,Finished] at finished
    | cons head tail =>
      rw [inspectMany,finished_append] at finished
      exact .cons (traced revision (shape query (by simp)) finished.1)
        (tracedMany revision (fun q member => shape q (by simp [member])) finished.2)
 termination_by sizeOf queries
end

 theorem candidate_rechecked (revision : Revision state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries state.context.state
      state.context.interpretation declaration, Syntax query)
    (finished : Finished (inspectMany state.context.state
      (GeneralNominalInspection.queries state.context.state state.context.interpretation declaration)
      bounds (fun _ => none) 0)) :
    GeneralNominalViewTransport196.Rechecked state.context (view revision) declaration bounds :=
  rechecked_of_trace _ _ _ _ (tracedMany revision shape finished)

 theorem candidate_report (revision : Revision state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries state.context.state
      state.context.interpretation declaration, Syntax query)
    (finished : Finished (GeneralNominalRecursiveCandidates.report state.context declaration bounds)) :
    GeneralNominalReportErasure.erase revision.snapshot
      (GeneralNominalRecursiveCandidates.report ⟨revision.snapshot,state.context.interpretation⟩ declaration bounds) =
    GeneralNominalReportErasure.erase state.context.state
      (GeneralNominalRecursiveCandidates.report state.context declaration bounds) := by
  have done : Finished (inspectMany state.context.state
      (GeneralNominalInspection.queries state.context.state state.context.interpretation declaration)
      bounds (fun _ => none) 0) := finished
  have same := candidate_rechecked revision shape done
  change GeneralNominalRecursiveCandidates.report _ _ _ = _ at same
  change GeneralNominalReportErasure.erase _
    (GeneralNominalRecursiveCandidates.report
      (GeneralNominalViewTransport196.context state.context (view revision)) declaration bounds) = _
  rw [same]
  simp [GeneralNominalReportErasure.erase,GeneralNominalReportErasure.interval,
    GeneralNominalViewTransport196.report,GeneralNominalViewTransport196.capture,List.map_map,
    GeneralNominalViewTransport196.context,GeneralNominalViewTransport196.replace]

end Yulang.GeneralDictionaryDefaultStructuralReobserve210
