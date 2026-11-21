import Yulang.GeneralVersionedHistoricalSupport314
import Yulang.GeneralDictionaryCountedInspection216
import Yulang.GeneralNominalVersionedMixedAncestry237

set_option backward.isDefEq.respectTransparency false
/-! Derive actual constructor tests for every checked reachable frame, not only
the original root. Real installed ancestors supply semantic counted labels;
the current inspection and actual center interval prove the tests. -/
namespace Yulang.GeneralVersionedReachableTests314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models initial)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedSharingBinderRows313 (Tests)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin)

theorem tests {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core focus key p)
    (m : Assignment) (valid : Models s m) : Tests p m := by
  obtain ⟨start,⟨legacy,⟨ctx,labels,formation,point,ground,coverage,rfl⟩,rfl⟩,steps⟩ := actual
  have compiledSource : GeneralNominalSourceFormation.InitialSource (Compiled registry) ctx root :=
    GeneralNominalCenteredHeadAllocEncoding.initial_source formation
  have compiledCoverage := GeneralNominalCenteredHeadAllocEncoding.coverage coverage
  obtain ⟨depth,ps,ancestry,inputs,bound⟩ :=
    GeneralNominalVersionedMixedAncestry237.sites_bounded compiledSource point ground compiledCoverage
      steps m valid p.input frame.center_recorded
  have located := GeneralNominalPacketCaptureReadback.locate_sources
    p.packet.context.state.base (List.ofFn focus.demand.arguments) p.packet.bounds frame.located
  have occurrence := p.input_exact.trans frame.occurrence_eq
  have length : p.packet.bounds.length = (roles p.input.occurrence.demand.role).arity := by
    rw [occurrence]
    simpa only [List.length_map,List.length_ofFn] using congrArg List.length located
  apply GeneralDictionaryCountedInspection216.many_tests p.packet.context.state m
    (constructors := (Compiled registry).constructors) (interpretation := ctx.interpretation)
  · rw [frame.context_eq]; exact valid.1.1
  · intro i
    have within : i.val < (roles p.input.occurrence.demand.role).arity := by rw [← length]; exact i.isLt
    have counted := inputs.2 ⟨i.val,within⟩
    have labelled := GeneralDictionaryCountedObservation216.counted_source counted
    simpa only [Nat.zero_add,List.getElem?_ofFn,within,↓reduceDIte,Option.getD_some] using labelled
  · intro i
    simpa only [Nat.zero_add] using GeneralNominalVersionedCurrentProjection237.root_bounds p frame m valid i
  · exact GeneralNominalVersionedCurrentProjection237.frame_finished p frame

end Yulang.GeneralVersionedReachableTests314
