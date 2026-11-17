import Yulang.GeneralDictionaryVersionedPointFresh233
import Yulang.GeneralNominalVersionedAcyclic232
import Yulang.GeneralNominalVersionedFrameFunctional232
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedPointSafety233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedInitialModel233 (extended names values)
open GeneralDictionaryVersionedPointStage233
open GeneralDictionaryOptionalCycles229
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalCenters

noncomputable abbrev packet := GeneralDictionaryVersionedPoint233.packet allocated reserved ordinary
noncomputable abbrev plan := GeneralDictionaryVersionedPoint233.plan allocated reserved ordinary

theorem model_form (identity : Nat) : ∃ form : Form, (extended identity).1 = form.value := by
  classical
  by_cases assigned : ∃ index : Fin 2, names index = identity
  · obtain ⟨index,rfl⟩ := assigned
    rw [GeneralDictionaryVersionedInitialModel233.fresh_value]
    by_cases low : index.val = 0
    · exact ⟨.exact,by simp only [values,ite_eq_left low]; rfl⟩
    · exact ⟨.width,by simp only [values,ite_eq_right low]; rfl⟩
  · have retained : extended identity = GeneralDictionaryOptionalInstall229.model identity :=
      GeneralNominalCenteredModelExtension.assign_outside _ names values
        (fun index same => assigned ⟨index,same⟩)
    rw [retained]
    exact ⟨GeneralDictionaryOptionalStageSafety229.sourceForm identity,
      GeneralDictionaryOptionalStageSafety229.model_form identity⟩

theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic point origin :=
  GeneralNominalVersionedAcyclic232.acyclic inhabited model_form origin

theorem source_form (slot : Fin 5) :
    (extended slot.val).1 = (GeneralDictionaryOptionalStageSafety229.sourceForm slot.val).value := by
  rw [GeneralDictionaryVersionedInitialModel233.old_value _ (by
    have small := slot.isLt
    simp only [GeneralDictionaryVersionedInitialModel233.pool,List.mem_cons,List.not_mem_nil,or_false]
    omega)]
  exact GeneralDictionaryOptionalStageSafety229.model_form _

theorem raw_edge_decreases {a b : Fin 5}
    (edge : GeneralNominalMixedRecurrence.Edge point.core.erased.current.context.state a b) :
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
      GeneralNominalMixedRecurrence.actual_edge_sound _ a b nominal extended inhabited.1.1
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
    ¬ GeneralNominalCycleK2.RecursAt point.core.erased.current.context.state slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path point.core.erased.current.context.state a b →
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

theorem second_value (purpose : Nat) :
    (extended (GeneralDictionaryVersionedNames231.freshName purpose)).1 = .emptyRecord := by
  have retained : extended (GeneralDictionaryVersionedNames231.freshName purpose) =
      GeneralDictionaryOptionalInstall229.model (GeneralDictionaryVersionedNames231.freshName purpose) :=
    GeneralNominalCenteredModelExtension.assign_outside _ names values
      (fun index same => GeneralDictionaryVersionedPointFresh233.new_old_distinct purpose index.val same.symm)
  rw [retained]
  have high := GeneralDictionaryVersionedNames231.fresh_above purpose
  have distinct := GeneralDictionaryVersionedNames231.fresh_not_legacy purpose 0
  simp [GeneralDictionaryOptionalInstall229.model,Nat.not_le.mpr high,distinct]

theorem point_values : GeneralDictionaryVersionedPoint233.Values extended := by
  constructor
  · rw [GeneralDictionaryVersionedInitialModel233.old_value 0 (by simp [GeneralDictionaryVersionedInitialModel233.pool])]; rfl
  · rw [GeneralDictionaryVersionedInitialModel233.old_value 2 (by simp [GeneralDictionaryVersionedInitialModel233.pool])]; rfl
  · rw [GeneralDictionaryVersionedInitialModel233.old_value _ (by simp [GeneralDictionaryVersionedInitialModel233.pool])]
    exact GeneralDictionaryOptionalInstall229.actual_value
  · rw [GeneralDictionaryVersionedInitialModel233.old_value 4 (by simp [GeneralDictionaryVersionedInitialModel233.pool])]; rfl
  · exact second_value 0
  · exact second_value 1

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry point.core.erased.current.context root declaration :=
  GeneralDictionaryVersionedPointFrame233.prepared allocated reserved ordinary point_values inhabited.1.1
    (fun purpose _ => GeneralDictionaryVersionedPointFresh233.fresh_outside purpose)

theorem frame : GeneralNominalVersionedEvidence231.Frame registry point.core root declaration.id plan :=
  GeneralDictionaryVersionedPointFrame233.frame allocated reserved ordinary point_values inhabited.1.1
    (fun purpose _ => GeneralDictionaryVersionedPointFresh233.fresh_outside purpose) context_exact raw_sites centered_sites

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady point root := by
  constructor
  · refine ⟨rootSite snapshot.seed root,?_,rfl⟩
    rw [centered_sites]; exact List.mem_singleton_self _
  · intro first one _ last two _
    rw [centered_sites] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry point root := by
  refine ⟨GeneralDictionaryVersionedPointFrame233.known allocated reserved ordinary,?_,?_,?_⟩
  · rintro (raw | (⟨index,cycle⟩ | ⟨site,_,_,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw; exact no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (raw | ⟨candidate,framed,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw; exact no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unready)
    · cases List.mem_singleton.mp visible; exact unprepared prepared
    · exact unready administrative_ready

theorem positions : GeneralNominalVersionedCycles232.Safe point plan := by
  constructor
  · unfold GeneralNominalCenteredSteps.inspection
    change (GeneralNominalRecursiveInspection.inspectMany _
      (GeneralNominalInspection.queries (GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary).state
        interpretation declaration) _ _ _).inspected.length = _
    rw [GeneralDictionaryOptionalCurrent229.query]
    simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
      GeneralNominalRecursiveInspection.typeArguments,GeneralNominalRecursiveInspection.Report.append,
      GeneralNominalRecursiveInspection.Report.visit,Site.observed,rootSite,root,roles]
    change (GeneralNominalRecursiveInspection.inspectMany (GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary).state
      [.variables [0],.variables [0]] [((2 : Fin 5),2),(2,2)]
      (fun index => some ((Origin.source 0).nominal 0 index)) 0).inspected.length =
      (GeneralNominalRecursiveInspection.inspectMany (GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary).state
      [.variables [0],.variables [0]] [((2 : Fin 5),2),(2,2)]
      (fun index => some ((Origin.source 0).nominal 0 index)) 0).tests.length
    simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
      GeneralNominalRecursiveInspection.Report.append]
  · exact fun entry _ => acyclic entry.1

theorem alternatives : GeneralNominalVersionedKernel232.AlternativesSafe registry point plan.input := by
  intro candidate same framed
  have equal := GeneralNominalVersionedFrameFunctional232.frame_plan_unique
    rfl raw_sites centered_sites framed frame
  subst candidate
  exact positions

theorem choice : GeneralNominalCycleSteps.ChoiceCompatible point.core.erased.current packet := by
  intro prior member _
  change prior ∈ [GeneralDictionaryOptionalInstall229.packet] at member
  cases List.mem_singleton.mp member
  rfl

end Yulang.GeneralDictionaryVersionedPointSafety233
