import Yulang.GeneralDictionaryMixedClosedStable234
import Yulang.GeneralNominalVersionedDiagnosticLaws232
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedClosedSelected234
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryMixedClosedStep234 (next)
open GeneralDictionaryMixedClosedStable234 (valid)
open GeneralDictionaryMixedClosedFrame234 (raw_sites centers)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralDictionaryOptionalCycles229
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalCenters GeneralNominalVersionedJournal232

abbrev slotForm (slot : Fin 8) : Form :=
  if slot.val < 5 then GeneralDictionaryOptionalStageSafety229.sourceForm slot.val else .width

theorem source_form (slot : Fin 8) :
    (extended (GeneralDictionaryMixedClosedBase234.source slot)).1 = (slotForm slot).value := by
  by_cases small : slot.val < 5
  · simpa only [GeneralDictionaryMixedClosedBase234.source,slotForm,small,ite_true] using
      GeneralDictionaryVersionedSecondSelected233.source_form ⟨slot.val,small⟩
  · have cases : slot = 5 ∨ slot = 6 ∨ slot = 7 := by have bound := slot.isLt; omega
    rcases cases with rfl | rfl | rfl
    · exact GeneralDictionaryVersionedBothModel233.fresh_value 1
    · exact GeneralDictionaryVersionedBothModel233.next_value 0
    · exact GeneralDictionaryVersionedBothModel233.next_value 1

theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic next origin :=
  GeneralNominalVersionedAcyclic232.acyclic valid GeneralDictionaryVersionedSecondSelected233.model_form origin

theorem frame : GeneralNominalVersionedEvidence231.Frame registry next.core root declaration.id
    GeneralDictionaryMixedClosedPlan234.plan :=
  GeneralDictionaryMixedClosedFrame234.frame (GeneralDictionaryMixedClosedEvidence234.packet valid)

theorem raw_edge_decreases {a b : Fin 8}
    (edge : GeneralNominalMixedRecurrence.Edge next.core.erased.current.context.state a b) :
    (slotForm b).rank <
      (slotForm a).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 ∨ 5 ≤ a.val then .structural 0 Fin.elim0 else .deferred .unresolved :
      GeneralNormalizedObservation.Head GeneralDictionaryMixedClosedBase234.viewShapes 8) = .structural kind children at recorded
    split at recorded
    · cases recorded; exact Fin.elim0 index
    · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound _ a b nominal extended valid.1.1
    have observation := embed_observation extended _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      change Equivalent (extended (GeneralDictionaryMixedClosedBase234.source a)).1 _ at equal
      rw [source_form a] at equal
      obtain ⟨child,smaller,meaning⟩ := nominal_child
        (slotForm a) equal found
      change Equivalent _ (extended (GeneralDictionaryMixedClosedBase234.source b)).1 at same
      rw [source_form b] at same
      have rankEq := equivalent_rank child
        (slotForm b)
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem no_raw_recurs (slot : Fin 8) :
    ¬ GeneralNominalCycleK2.RecursAt next.core.erased.current.context.state slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path next.core.erased.current.context.state a b →
      (slotForm b).rank ≤
      (slotForm a).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have smaller := raw_edge_decreases edge
  have larger := paths _ _ path
  omega

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady next root := by
  constructor
  · refine ⟨rootSite snapshot.seed root,?_,rfl⟩
    rw [centers]; exact List.mem_singleton_self _
  · intro first one _ last two _
    rw [centers] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry next root := by
  refine ⟨GeneralDictionaryMixedClosedFrame234.known,?_,?_,?_⟩
  · rintro (raw | (⟨index,cycle⟩ | ⟨site,_,_,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw; exact no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (raw | ⟨candidate,framed,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw; exact no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unready)
    · cases List.mem_singleton.mp visible; exact unprepared frame.prepared
    · exact unready administrative_ready


theorem equal_outputs (focus) : GeneralNominalCenteredHeadOutputs.EqualOutputs next.core focus extended := by
  intro first one last two _
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp one
  rw [raw_sites] at present
  cases List.mem_singleton.mp present
  cases List.mem_singleton.mp within
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp two
  rw [raw_sites] at present
  cases List.mem_singleton.mp present
  cases List.mem_singleton.mp within
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem selected : GeneralNominalVersionedMixedBoundary234.Local registry next root (.selected declaration.id []) := by
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  apply GeneralNominalVersionedDiagnosticLaws232.selected_of_model safe
    (GeneralDictionaryMixedClosedEvidence234.unique valid) valid frame
    GeneralDictionaryMixedClosedFrame234.ready
    (GeneralDictionaryMixedClosedEvidence234.packet valid)
    (GeneralDictionaryMixedClosedFrame234.class_effects (GeneralDictionaryMixedClosedEvidence234.packet valid))
  exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict valid
    (fun focus _ => equal_outputs focus) (equal_outputs root)

theorem source_selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry next root (.selected declaration.id []) :=
  GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr selected

end Yulang.GeneralDictionaryMixedClosedSelected234
