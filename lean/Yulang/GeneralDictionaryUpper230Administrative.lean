import Yulang.GeneralDictionaryUpper230Prepared
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Administrative
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Snapshot GeneralDictionaryUpper230Step
open CommonNominalFullCarrier

theorem no_refresh (context : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh after context)
    (member : identity ∈ GeneralNominalState.sources after.core.erased.current.context.state)
    (unknown : ¬ GeneralNominalState.Known after.core.erased.current.context.state identity)
    (known : GeneralNominalState.Known context.state identity) : False := by
  rcases GeneralDictionaryUpper230Support.unknown_cases member unknown with rfl | rfl | rfl
  · obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
    have valid := GeneralNominalCenteredHeadMatStepRefresh.refresh_exact_transport certificate model GeneralDictionaryUpper230Step.inhabited
    have held := GeneralNominalCenteredHeadAllocMergeStable.head_holds head
      (GeneralCanonicalObservations.recorded_sound context.state model valid
        (GeneralNominalSupport.head_recorded head))
    change test.Holds .top at held
    exact GeneralDictionaryGroundCopy218Refresh.top_no_head test held
  · exact GeneralDictionaryOptionalExpression229.no_refresh_known GeneralDictionaryUpper230Step.inhabited rfl certificate known
  · exact GeneralDictionaryOptionalExpression229.no_refresh_known GeneralDictionaryUpper230Step.inhabited lower_value certificate known

theorem point_closed : GeneralNominalReobservationSteps.PointClosed extendedSnapshot := by
  intro slot d found
  change (if slot = 0 ∨ slot = 1 then some pointDesc else none) = some d at found
  split at found
  · cases Option.some.inj found
    intro parameter member
    change parameter ∈ [GeneralNominalState.Parameter.type ((2 : Fin 6),2),.type (2,2)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> rfl
  · cases found

theorem no_reobserve (revision : GeneralNominalReobservationSteps.Revision after.core.erased.current) :
    ¬ GeneralNominalReobservationSteps.Improves revision :=
  GeneralNominalReobservationSteps.pointClosed_no_revision point_closed revision

theorem generated_only (demand)
    (generated : GeneralNominalSaturationState.Generated after.core.erased.current root demand) : demand = root := by
  induction generated with
  | root => rfl
  | child generated edge ih =>
    change _ ∈ [] ++ packet.children.map (fun child => (root,child)) at edge
    rw [children_empty] at edge
    cases edge
  | alias generated first last same ih =>
    cases List.mem_singleton.mp last
    rfl

end Yulang.GeneralDictionaryUpper230Administrative
