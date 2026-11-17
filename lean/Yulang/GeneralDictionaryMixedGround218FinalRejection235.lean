import Yulang.GeneralDictionaryMixedGround218FinalFresh235
import Yulang.GeneralDictionaryMixedGround218FinalRegression235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218FinalRejection235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (model sourceForm model_small source_form model_forms childSite)
open GeneralDictionaryMixedGround218FinalState235
open GeneralDictionaryMixedGround218FinalRegression235 (sites)
open GeneralDictionaryMixedGround218PointLeaf235 (oldChild leafDecl leafCheck)
open GeneralNominalCenters GeneralNominalRecursiveInspection CommonNominalFullCarrier
noncomputable abbrev current := GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved ordinary

theorem raw_model : GeneralNominalState.Models current model := by
  have raw := final_model.1.1
  rw [final_context] at raw
  exact raw
theorem raw_edge_decreases {a b : Fin 8} (edge : GeneralNominalMixedRecurrence.Edge current a b) :
    (sourceForm b.val).rank < (sourceForm a.val).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 then .structural 0 (fun _ => 0) else if a = 3 then .structural 0 (fun _ => 1) else
      .deferred .unresolved : GeneralNormalizedObservation.Head view.shapes 8) = .structural kind children at recorded
    split at recorded
    · rename_i equal; subst a
      cases recorded
      have zero : b = 0 := child.symm
      subst b
      change 0 < 1; decide
    · split at recorded
      · rename_i equal; subst a
        cases recorded
        have one : b = 1 := child.symm
        subst b
        change 0 < 1; decide
      · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound current a b nominal model raw_model
    have observation := embed_observation model _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      have firstValue : (model a.val).1 = (sourceForm a.val).value :=
        (model_small a.val (by omega)).trans (source_form a.val)
      have lastValue : (model b.val).1 = (sourceForm b.val).value :=
        (model_small b.val (by omega)).trans (source_form b.val)
      rw [firstValue] at equal
      obtain ⟨child,smaller,meaning⟩ := GeneralDictionaryGroundCopy218Cycles.nominal_child
        (sourceForm a.val) equal found
      rw [lastValue] at same
      have rankEq := GeneralDictionaryGroundCopy218Cycles.equivalent_rank child (sourceForm b.val)
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem no_raw_recurs (slot : Fin 8) : ¬ GeneralNominalCycleK2.RecursAt current slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path current a b →
      (sourceForm b.val).rank ≤ (sourceForm a.val).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have smaller := raw_edge_decreases edge
  have larger := paths _ _ path
  omega




theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic finalState origin :=
  GeneralDictionaryMixedGround218Cycles235.acyclic final_model model_forms origin

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady finalState oldChild := by
  refine ⟨⟨childSite,by rw [sites.1]; exact List.mem_cons_of_mem _ List.mem_cons_self,
    GeneralDictionaryMixedGround218LeafFrame235.child_eq⟩,?_⟩
  intro first one _ last two same
  exact GeneralDictionaryMixedGround218PointStable235.merges_closed sites one two same

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry finalState oldChild := by
  have known : ¬ GeneralNominalState.RootPending finalState.core.erased.current.context.state oldChild.demand := by
    rw [final_context]
    exact GeneralDictionaryMixedGround218PointLeaf235.known allocated reserved ordinary
  have noRaw : ∀ slot, ¬ GeneralNominalCycleK2.RecursAt finalState.core.erased.current.context.state slot := by
    rw [final_context]; exact no_raw_recurs
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact noRaw slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact noRaw visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases GeneralDictionaryMixedGround218PointLeaf235.leaf_only visible role
      exact unprepared GeneralDictionaryMixedGround218FinalFresh235.prepared
    · exact unclosed administrative_ready

noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,GeneralDictionaryGroundCopy218SaturatedParent.contextFor allocated reserved ordinary,
    childSite.observed,leafDecl,leafCheck,[(2,3),(2,3)]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,childSite,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry finalState.core oldChild 1 plan := by
  refine ⟨rfl,final_context.symm,GeneralDictionaryMixedGround218LeafFrame235.child_eq,rfl,?_,?_,
    List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl,rfl,GeneralDictionaryMixedGround218FinalFresh235.prepared⟩
  · rw [sites.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [sites.1]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem conflict : GeneralNominalVersionedDiagnostic232.SharingConflict registry finalState oldChild := by
  refine ⟨1,[],GeneralDictionaryMixedGround218FinalFresh235.unique,safe,⟨model,final_model⟩,⟨plan,frame⟩,?_⟩
  rintro ⟨given,valid,candidate,framed,shared⟩
  have childEq : childSite.occurrence = oldChild := GeneralDictionaryMixedGround218LeafFrame235.child_eq
  rw [← childEq] at framed
  exact GeneralDictionaryMixedGround218FinalEvidence235.old_infeasible sites recorded framed given valid shared

theorem rejected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry finalState oldChild .rejected := by
  apply B4TargetV8.Local.sharingRejected conflict
  exact B4TargetV8.unique_not_priorityAmbiguity
    (show B4TargetV8.Unique (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
      sourceRegistry finalState oldChild 1 [] from GeneralDictionaryMixedGround218FinalFresh235.unique)
end Yulang.GeneralDictionaryMixedGround218FinalRejection235
