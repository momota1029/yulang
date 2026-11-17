import Yulang.GeneralDictionaryUpper230Prepared
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Safety
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Snapshot GeneralDictionaryUpper230Step
open GeneralDictionaryUpper230Prepared
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
noncomputable abbrev current := extendedContext

theorem acyclic (origin) : ¬ GeneralNominalCenteredHeadMatStepCycles.Cyclic after origin :=
  GeneralDictionaryOptionalCycles229.acyclic GeneralDictionaryUpper230Step.inhabited
    (fun identity => ⟨GeneralDictionaryOptionalStageSafety229.sourceForm identity,
      GeneralDictionaryOptionalStageSafety229.model_form identity⟩) origin

theorem raw_edge_decreases {a b : Fin 6} (edge : GeneralNominalMixedRecurrence.Edge current.state a b) :
    (GeneralDictionaryOptionalEnable229.sourceForm (GeneralDictionaryUpper230Base.source b)).rank <
      (GeneralDictionaryOptionalEnable229.sourceForm (GeneralDictionaryUpper230Base.source a)).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 ∨ a = 5 then .structural 0 Fin.elim0 else .deferred .unresolved :
      GeneralNormalizedObservation.Head GeneralDictionaryUpper230Base.viewShapes 6) = .structural kind children at recorded
    split at recorded
    · cases recorded
      exact Fin.elim0 index
    · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound current.state a b nominal modelHigh GeneralDictionaryUpper230Models.high_raw
    have observation := embed_observation modelHigh _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      rw [GeneralDictionaryOptionalEnable229.high_form] at equal
      obtain ⟨child,smaller,meaning⟩ := GeneralDictionaryJournalRefinement228Cycles.nominal_child
        (GeneralDictionaryOptionalEnable229.sourceForm (GeneralDictionaryUpper230Base.source a)) equal found
      rw [GeneralDictionaryOptionalEnable229.high_form] at same
      have rankEq := GeneralDictionaryJournalRefinement228Cycles.equivalent_rank child
        (GeneralDictionaryOptionalEnable229.sourceForm (GeneralDictionaryUpper230Base.source b))
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem no_raw_recurs (slot : Fin 6) : ¬ GeneralNominalCycleK2.RecursAt current.state slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path current.state a b →
      (GeneralDictionaryOptionalEnable229.sourceForm (GeneralDictionaryUpper230Base.source b)).rank ≤
      (GeneralDictionaryOptionalEnable229.sourceForm (GeneralDictionaryUpper230Base.source a)).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have smaller := raw_edge_decreases edge
  have larger := paths _ _ path
  omega

theorem administrative_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady after root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one _ last two _
  cases List.mem_singleton.mp one; cases List.mem_singleton.mp two
  exact .refl _

theorem known : ¬ GeneralNominalState.RootPending current.state
    (GeneralNominalCenteredHeadCandidates.inputs root).demand := by
  rintro ⟨index,unknown⟩
  exact unknown GeneralDictionaryUpper230Support.known_zero

theorem safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry after root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases List.mem_singleton.mp visible; exact unprepared current_prepared
    · exact unclosed administrative_ready
end Yulang.GeneralDictionaryUpper230Safety
