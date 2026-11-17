import Yulang.GeneralDictionaryMixedGround218PointFrame235
import Yulang.GeneralDictionaryMixedGround218Cycles235
import Yulang.GeneralDictionaryMixedGround218LeafFrame235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218PointSafety235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (model sourceForm model_small source_form model_forms childSite parent_only)
open GeneralDictionaryMixedGround218Point235
open GeneralDictionaryMixedGround218PointPacket235 (plan packet)
open GeneralDictionaryMixedGround218PointFrame235 (prepared)
open GeneralNominalCenters GeneralNominalRecursiveInspection CommonNominalFullCarrier
theorem raw_edge_decreases {a b : Fin 8} (edge : GeneralNominalMixedRecurrence.Edge (GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved ordinary) a b) :
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
      GeneralNominalMixedRecurrence.actual_edge_sound (GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved ordinary) a b nominal model (point_snapshot ▸ point_model.1.1)
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

theorem no_raw_recurs (slot : Fin 8) : ¬ GeneralNominalCycleK2.RecursAt (GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved ordinary) slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path (GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved ordinary) a b →
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
theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic point origin :=
  GeneralDictionaryMixedGround218Cycles235.acyclic point_model model_forms origin

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady point root := by
  refine ⟨⟨_,List.mem_cons_self,rfl⟩,?_⟩
  intro first one _ last two same
  change first ∈ GeneralDictionaryMixedGround218Install234.installed.core.sites at one
  rw [GeneralDictionaryMixedGround218LeafFrame235.sites_exact] at one
  change last ∈ GeneralDictionaryMixedGround218Install234.installed.core.sites at two
  rw [GeneralDictionaryMixedGround218LeafFrame235.sites_exact] at two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  · exact .refl _
  · have impossible := same.1; cases impossible
  · have impossible := same.1; cases impossible
  · exact .refl _

theorem known : ¬ GeneralNominalState.RootPending point.core.erased.current.context.state root.demand := by
  rintro ⟨index,unknown⟩
  rw [point_snapshot] at unknown
  exact unknown ⟨6,rfl,Or.inr ⟨exactCopy,rfl⟩⟩

theorem current_no_raw_recurs : ∀ slot, ¬ GeneralNominalCycleK2.RecursAt point.core.erased.current.context.state slot := by
  rw [point_snapshot]
  exact no_raw_recurs

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry point root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact current_no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact current_no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases parent_only visible role
      exact unprepared (GeneralDictionaryMixedGround218PointPacket235.context_eq ▸ prepared)
    · exact unclosed administrative_ready
end Yulang.GeneralDictionaryMixedGround218PointSafety235
