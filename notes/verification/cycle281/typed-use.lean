import Yulang.GeneralRebasePhaseCache281
import Yulang.GeneralRebaseLoopReplay281
import Yulang.GeneralRebaseTermReplay281
import Yulang.GeneralRebasePacketFootprint281

open Yulang
open GeneralRebaseLoopReplay281
open GeneralRebasePortProjection280 (Project)
open GeneralNominalState (Models Known)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralRebaseAggregateLift281 (sourceView)
open GeneralRebaseActualReplay281 (fixedState)
open GeneralRebaseAggregateTags281 (fixed)

namespace Cycle281TypedUse

theorem version_readback (n : Nat) (outer : Assignment) :
    Project (sourceView (GeneralDictionaryVersionLoopBook239.packet n))
      (Models (replayPlan (GeneralDictionaryVersionLoopBook239.plan n)).packet.context.state) outer ↔
      Project (sourceView (GeneralDictionaryVersionLoopBook239.packet n))
        (Models (fixedState (GeneralDictionaryVersionLoopBook239.packet n)
          ((Version.rows n).map (fixed (GeneralDictionaryVersionLoopBook239.packet n))))) outer :=
  Version.projected_equal n outer

theorem loose_known (n id : Nat) :
    Known (replayPlan (GeneralDictionaryLooseIterationBook240.plan n)).packet.context.state id ↔
      Known (fixedState (GeneralDictionaryLooseIterationBook240.packet n)
          ((Loose.rows n).map (fixed (GeneralDictionaryLooseIterationBook240.packet n)))) id :=
  Loose.known_equal n id

theorem private_service_check (n : Nat) :
    ¬ GeneralRebasePhaseMachine281.Step GeneralRebasePhaseLoop281.oldEmpty
      (GeneralRebasePhaseLoop281.onceCodec GeneralDictionaryVersionLoopSource237.roles)
      GeneralDictionaryVersionLoopSource237.sourceRegistry GeneralDictionaryVersionLoopSource237.root
      (GeneralDictionaryVersionLoopIteration239.state (n+1)) (GeneralRebaseVersionMicro278.installed (n+1)) :=
  GeneralRebasePhaseLoop281.Version.no_repeat n

theorem private_service_point :
    GeneralRebasePhaseMachine281.Step GeneralRebaseChartFixtures281.outputChart
      GeneralRebasePhaseFixture281.codec GeneralDictionaryOptionalInitial229.sourceRegistry
      GeneralDictionaryJournalRefinement228Source.root GeneralDictionaryVersionedPointStage233.point
      GeneralDictionaryVersionedSecondInstall233.installed :=
  GeneralRebasePhaseFixture281.retained_service

theorem arbitrary_packet (q : GeneralNominalCenters.Plan roles) (m : Assignment) :
    Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) m ↔
      GeneralRebaseActualReplay281.Baseline q.packet m ∧
        GeneralRebaseTermCopy281.Respects (GeneralRebaseTermCopy281.kept (sourceView q.packet)
          (GeneralRebaseTermAggregate281.writes q.packet false)) m :=
  GeneralRebaseTermReplay281.actual_project q m

theorem reduced_chart (q : GeneralNominalCenters.Plan roles) (m : Assignment) :
    Project (GeneralRebasePacketFootprint281.footprint q.packet)
      (Models (replayPlan q).packet.context.state) m ↔
    Project (GeneralRebasePacketFootprint281.footprint q.packet) (Models q.packet.context.state) m ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model m (GeneralRebasePacketChart281.pool q.packet) :=
  GeneralRebasePacketFootprint281.projected_exact q
    (GeneralRebasePacketFootprint281.footprint_in_source q.packet) (fun _ h => h) m

end Cycle281TypedUse
