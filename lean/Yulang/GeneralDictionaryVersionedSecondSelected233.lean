import Yulang.GeneralDictionaryVersionedSecondInstall233
import Yulang.GeneralDictionaryVersionedPointInstalledSelected233
import Yulang.GeneralNominalVersionedInstalledEvidenceAt233
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedSecondSelected233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedPointStage233 (point allocated reserved ordinary)
open GeneralDictionaryVersionedSecondInstall233
open GeneralDictionaryVersionedBothModel233 (extended nextNames)
open GeneralDictionaryOptionalCycles229
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalCenters GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232

theorem raw_sites : installed.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] :=
  (GeneralNominalVersionedTerminal232.raw_eq terminal).trans GeneralDictionaryVersionedPointStage233.raw_sites

theorem centers : installed.core.sites = [rootSite snapshot.seed root] :=
  (GeneralNominalVersionedTerminal232.sites_eq terminal).trans GeneralDictionaryVersionedPointStage233.centered_sites

theorem frame : GeneralNominalVersionedEvidence231.Frame registry installed.core root declaration.id
    (GeneralNominalVersionedInstallation231.replayPlan plan) :=
  GeneralNominalVersionedInstalledEvidence233.frame rfl installed_model

theorem model_form (identity : Nat) : ∃ form : Form, (extended identity).1 = form.value := by
  classical
  by_cases assigned : ∃ index : Fin 2, nextNames index = identity
  · obtain ⟨index,rfl⟩ := assigned
    exact ⟨.width,GeneralDictionaryVersionedBothModel233.next_value index⟩
  · have retained : extended identity = GeneralDictionaryVersionedInitialModel233.extended identity :=
      GeneralNominalCenteredModelExtension.assign_outside _ _ _ (fun index same => assigned ⟨index,same⟩)
    rw [retained]
    exact GeneralDictionaryVersionedPointSafety233.model_form identity

theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic installed origin :=
  GeneralNominalVersionedAcyclic232.acyclic installed_model model_form origin

theorem source_form (slot : Fin 5) :
    (extended slot.val).1 = (GeneralDictionaryOptionalStageSafety229.sourceForm slot.val).value := by
  rw [GeneralDictionaryVersionedBothModel233.old_value _ (by
    have small := slot.isLt
    simp only [GeneralDictionaryVersionedBothModel233.pool,GeneralDictionaryVersionedInitialModel233.pool,
      List.mem_cons,List.not_mem_nil,or_false]
    omega)]
  exact GeneralDictionaryOptionalStageSafety229.model_form _

theorem raw_edge_decreases {a b : Fin 5}
    (edge : GeneralNominalMixedRecurrence.Edge installed.core.erased.current.context.state a b) :
    (GeneralDictionaryOptionalStageSafety229.sourceForm b.val).rank <
      (GeneralDictionaryOptionalStageSafety229.sourceForm a.val).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 then .structural 0 Fin.elim0 else .deferred .unresolved :
      GeneralNormalizedObservation.Head view.shapes 5) = .structural kind children at recorded
    split at recorded
    · cases recorded; exact Fin.elim0 index
    · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound _ a b nominal extended installed_model.1.1
    have observation := embed_observation extended _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      change Equivalent (extended a.val).1 _ at equal
      rw [source_form a] at equal
      obtain ⟨child,smaller,meaning⟩ := nominal_child
        (GeneralDictionaryOptionalStageSafety229.sourceForm a.val) equal found
      change Equivalent _ (extended b.val).1 at same
      rw [source_form b] at same
      have rankEq := equivalent_rank child
        (GeneralDictionaryOptionalStageSafety229.sourceForm b.val)
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem no_raw_recurs (slot : Fin 5) :
    ¬ GeneralNominalCycleK2.RecursAt installed.core.erased.current.context.state slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path installed.core.erased.current.context.state a b →
      (GeneralDictionaryOptionalStageSafety229.sourceForm b.val).rank ≤
      (GeneralDictionaryOptionalStageSafety229.sourceForm a.val).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have smaller := raw_edge_decreases edge
  have larger := paths _ _ path
  omega

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady installed root := by
  constructor
  · refine ⟨rootSite snapshot.seed root,?_,rfl⟩
    rw [centers]; exact List.mem_singleton_self _
  · intro first one _ last two _
    rw [centers] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry installed root := by
  refine ⟨GeneralDictionaryVersionedPointFrame233.known _ _ _,?_,?_,?_⟩
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

theorem selected : GeneralNominalVersionedBoundary232.Local registry installed root (.selected declaration.id []) :=
  GeneralDictionaryVersionedPointInstalledSelected233.selected allocated reserved ordinary rfl rfl rfl
    GeneralDictionaryVersionedPointStage233.raw_sites safe installed_model

theorem source_selected : GeneralNominalVersionedSourceBoundary232.Local sourceRegistry installed root (.selected declaration.id []) :=
  GeneralNominalVersionedSourceBoundary232.local_iff.mpr selected

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles)
    sourceRegistry installed root :=
  GeneralNominalVersionedInstalledEvidenceAt233.source_evidenceAt rfl rfl terminal
    (by
      change [] ++ GeneralNominalVersionedChildren232.edges GeneralDictionaryOptionalInstall229.plan = []
      unfold GeneralNominalVersionedChildren232.edges
      rw [GeneralDictionaryVersionedInitialFrame233.children_empty]
      rfl)
    (by intro site member; rw [GeneralDictionaryVersionedPointStage233.raw_sites] at member; cases List.mem_singleton.mp member; rfl)
    source_selected

end Yulang.GeneralDictionaryVersionedSecondSelected233
