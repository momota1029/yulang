import Yulang.GeneralDictionaryMixedGround218LeafFrame235
import Yulang.GeneralDictionaryMixedGround218Cycles235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218Safety235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (model sourceForm model_small source_form model_forms childSite)
open GeneralDictionaryMixedGround218Leaf235
open GeneralDictionaryMixedGround218LeafFrame235
open GeneralDictionaryMixedGround218Install234 (installed installed_model)
open GeneralNominalCenters GeneralNominalRecursiveInspection CommonNominalFullCarrier
theorem raw_edge_decreases {a b : Fin 8} (edge : GeneralNominalMixedRecurrence.Edge ctx.state a b) :
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
      GeneralNominalMixedRecurrence.actual_edge_sound ctx.state a b nominal model GeneralDictionaryMixedGround218Fresh235.current_model
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

theorem no_raw_recurs (slot : Fin 8) : ¬ GeneralNominalCycleK2.RecursAt ctx.state slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path ctx.state a b →
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



theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic installed origin :=
  GeneralDictionaryMixedGround218Cycles235.acyclic installed_model model_forms origin

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady installed oldChild := by
  refine ⟨⟨childSite,by rw [sites_exact]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _),child_eq⟩,?_⟩
  intro first one _ last two same
  rw [sites_exact] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  · exact .refl _
  · have impossible := same.1; cases impossible
  · have impossible := same.1; cases impossible
  · exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry installed oldChild := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases leaf_only visible role; exact unprepared GeneralDictionaryMixedGround218Fresh235.prepared
    · exact unclosed administrative_ready
end Yulang.GeneralDictionaryMixedGround218Safety235
