import Yulang.GeneralVersionedAggregatePeer311
import Yulang.GeneralNominalVersionedSelectiveAggregate236
import Yulang.GeneralNominalVersionedMixedSeedLedger237
import Yulang.GeneralNominalSemanticRawFrame236
import Yulang.GeneralNominalReportErasure

set_option backward.isDefEq.respectTransparency false
/-! Choice needs private head feasibility, not a new compound journal model.
The semantic raw pool excludes bare reservations. Keep already constrained
aggregate slots using actual ledger equations, and change only other ones. -/
namespace Yulang.GeneralVersionedProtectedPeer312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalVersionedPlans231 (HeadModels Holds)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalSaturationState (Packet Alias)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSemanticRawFrame236 (sources)
open GeneralNominalVersionedAggregateLedger236 (packetEntries ProtectedCovered)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralNominalReportErasure (Data erase)
open GeneralVersionedAggregatePeer311 (probe)
open GeneralVersionedPeerChoice311 (reads)

abbrev semanticPool (p : Packet roles) := sources p.context.state

def Raw (p : Packet roles) (m : Assignment) : Prop :=
  GeneralNominalAllocation.Compatible p.bindings m ∧
  PresenceNormalForm.All CommonNominalFullCarrier.model m
    (GeneralNominalRecursiveInspection.selfChecks p.context.state (GeneralNominalPacketSupport.report p)) ∧
  GeneralNominalRecursiveInspection.ProjectionModels p.context.state (GeneralNominalPacketSupport.report p) m

theorem raw_of_head {p : Packet roles} {m : Assignment} (held : HeadModels p m) : Raw p m := by
  obtain ⟨_,cross,_,checks⟩ := (GeneralNominalVersionedPlans231.private_models_iff p m).mp held.1
  exact ⟨cross,checks,held.2⟩

def Observation (p : Packet roles) : Data := erase p.context.state (GeneralNominalPacketSupport.report p)

theorem raw_iff_observation (p : Packet roles) (m : Assignment) : Raw p m ↔
    GeneralNominalAllocation.Compatible (Observation p).bindings m ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model m (Observation p).selfChecks ∧
    (Observation p).Projections m := by
  unfold Raw Observation
  rw [GeneralNominalReportErasure.bindings_exact,GeneralNominalReportErasure.checks_exact,
    GeneralNominalReportErasure.projections_exact]
  rfl

theorem raw_transport {old current : Packet roles} {m : Assignment}
    (same : Observation old = Observation current) (held : Raw old m) : Raw current m :=
  (raw_iff_observation current m).mpr (same ▸ (raw_iff_observation old m).mp held)

theorem recorded_raw {state : State roles} {prior : Packet roles} {m : Assignment}
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (present : prior ∈ state.core.erased.current.packets) (valid : Models state m) : Raw prior m := by
  obtain ⟨plan,member,rfl⟩ := GeneralNominalVersionedMixedChoiceHistory236.packet_plan path present
  exact raw_of_head (GeneralNominalVersionedPlans231.head_models (valid.2.1 plan member))

noncomputable def completed (p : Packet roles) (m : Assignment) : Assignment :=
  GeneralNominalVersionedSelectiveAggregate236.patch p.context.state.seed p.site.occurrence.identity
    p.declaration.id p.bindings p.declaration.inputNames (semanticPool p) m

theorem preserves (p : Packet roles) (m : Assignment) :
    ∀ n ∈ semanticPool p, completed p m n = m n :=
  GeneralNominalSelectiveEquationRealization236.preserves _ _

theorem complete_head (p : Packet roles) (m : Assignment)
    (source : GeneralNominalState.Models p.context.state m) (raw : Raw p m)
    (reused : ∀ entry ∈ packetEntries p, entry.1 ∈ semanticPool p →
      PresenceNormalForm.All CommonNominalFullCarrier.model m (GeneralNominalAllocation.equations entry.1 entry.2)) :
    HeadModels p (completed p m) := by
  have same : ∀ n ∈ semanticPool p, m n = completed p m n :=
    fun n present => (preserves p m n present).symm
  have endpoints := GeneralNominalSemanticRawFrame236.report_endpoints p.context.state (GeneralNominalPacketSupport.report p)
  have valid := (GeneralNominalSemanticRawFrame236.source_models_same _ same).mp source
  have cross : GeneralNominalAllocation.Compatible p.bindings (completed p m) := by
    intro a one b two name
    change CommonNominalFullCarrier.Subtype (completed p m a.2.1).1 (completed p m b.2.2).1
    rw [← same _ (endpoints a one).1,← same _ (endpoints b two).2]
    exact raw.1 a one b two name
  have self : PresenceNormalForm.All CommonNominalFullCarrier.model (completed p m)
      (GeneralNominalRecursiveInspection.selfChecks p.context.state (GeneralNominalPacketSupport.report p)) := by
    intro atom present
    apply (GeneralNominalCenteredModelExtension.atom_same atom (fun n h => same n
      (GeneralNominalSemanticRawFrame236.checks_sources _ _ atom present h))).mp
    exact raw.2.1 atom present
  have merges := GeneralNominalVersionedSelectiveAggregate236.merges p.context.state p.registry
    p.site.occurrence.identity p.declaration p.bindings m reused endpoints
  have projected := (GeneralNominalSemanticRawFrame236.projection_iff p.context.state (GeneralNominalPacketSupport.report p)
    (fun n present => same n (GeneralNominalSemanticRawFrame236.report_sources_subset p.context p.declaration p.bounds present))).mp raw.2.2
  exact ⟨(GeneralNominalVersionedPlans231.private_models_iff p _).mpr
    ⟨valid,cross,merges,self⟩,projected⟩

theorem complete_on_trace {state : State roles} {p : Packet roles} {m : Assignment}
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (current : p.context = state.core.erased.current.context)
    (valid : Models state m) (raw : Raw p m)
    (coverage : IdCovered (semanticPool p) state p) : HeadModels p (completed p m) := by
  refine complete_head p m ?_ raw ?_
  · rw [current]
    exact valid.1.1
  · exact GeneralNominalVersionedAggregateLedger236.protected_equations
      (GeneralNominalVersionedMixedSeedLedger237.covered
        (GeneralNominalVersionedMixedSeedLedger237.reachable path) current coverage) valid

/-- A completed private model may differ outside the semantic raw pool;
    this theorem does not claim full journal invariance for that model. -/
theorem prepared_on_trace {state : State roles} {p : Packet roles} {m : Assignment}
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (current : p.context = state.core.erased.current.context)
    (locate : reads p.context p.site.occurrence = some p.bounds)
    (metadata : GeneralNominalRecursiveCandidates.Metadata p.registry p.context)
    (linked : GeneralNominalState.Linked p.context.state (inputs p.site.occurrence).demand)
    (fresh : GeneralNominalVersionedAllocation231.Fresh p.context.state p.registry p.site.occurrence.identity p.bindings)
    (finished : GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report p))
    (valid : Models state m) (raw : Raw p m)
    (coverage : IdCovered (semanticPool p) state p) :
    Prepared p.registry p.context p.site.occurrence p.declaration :=
  ⟨metadata,linked,p.bounds,locate,fresh,finished,completed p m,
    (GeneralNominalVersionedCandidates231.headModels_packet_iff p _).mpr
      (complete_on_trace path current valid raw coverage)⟩

end Yulang.GeneralVersionedProtectedPeer312
