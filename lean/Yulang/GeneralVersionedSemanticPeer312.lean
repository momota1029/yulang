import Yulang.GeneralVersionedAliasChoice312
import Yulang.GeneralNominalVersionedTraceSupport237

set_option backward.isDefEq.respectTransparency false
/-! Aggregate reuse need only cover the exact report reads and a semantic
support of the live journal. Redundant observed raw atoms are not forcibly
protected. Unlike private completion alone, this patch preserves Models. -/
namespace Yulang.GeneralVersionedSemanticPeer312
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalVersionedPlans231 (HeadModels)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralVersionedProtectedPeer312 (Raw)
open GeneralVersionedHistoricalTransport312 (atFocus)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalSaturationState (Packet Alias)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedPeerChoice311 (reads)
open GeneralVersionedHistoryEvidence310 (Compiled)

abbrev reportPool (p : Packet roles) :=
  GeneralNominalReportSupport237.sources p.context.state (GeneralNominalPacketSupport.report p)

def protectedPool (p : Packet roles) (names : List Nat) : List Nat := names ++ reportPool p

noncomputable def complete (p : Packet roles) (names : List Nat) (m : Assignment) : Assignment :=
  GeneralNominalVersionedSelectiveAggregate236.patch p.context.state.seed p.site.occurrence.identity
    p.declaration.id p.bindings p.declaration.inputNames (protectedPool p names) m

def Sufficient (s : State roles) (p : Packet roles) : Prop :=
  ∃ names, Support s names ∧ IdCovered (protectedPool p names) s p

theorem full_head {s : State roles} {p : Packet roles} {m : Assignment}
    (current : p.context = s.core.erased.current.context)
    (support : Support s names)
    (valid : Models s m)
    (raw : Raw p m)
    (reused : ∀ entry ∈ packetEntries p, entry.1 ∈ protectedPool p names →
      PresenceNormalForm.All CommonNominalFullCarrier.model m (GeneralNominalAllocation.equations entry.1 entry.2)) :
    Models s (complete p names m) ∧ HeadModels p (complete p names m) := by
  let patch := complete p names m
  have same : ∀ k ∈ protectedPool p names, m k = patch k :=
    fun n h => (GeneralNominalSelectiveEquationRealization236.preserves _ _ n h).symm
  have live := (support m patch (fun n h => same n (List.mem_append_left _ h))).mp valid
  have reportSame : ∀ k ∈ reportPool p, m k = patch k := fun k h => same k (List.mem_append_right _ h)
  have found := GeneralNominalReportSupport237.report_endpoints p.context.state (GeneralNominalPacketSupport.report p)
  have cross : GeneralNominalAllocation.Compatible p.bindings patch := by
    intro a one b two name
    change CommonNominalFullCarrier.Subtype (patch a.2.1).1 (patch b.2.2).1
    rw [← reportSame _ (found a one).1,← reportSame _ (found b two).2]
    exact raw.1 a one b two name
  have checks : PresenceNormalForm.All CommonNominalFullCarrier.model patch
      (GeneralNominalRecursiveInspection.selfChecks p.context.state (GeneralNominalPacketSupport.report p)) := by
    intro atom h
    apply (GeneralNominalCenteredModelExtension.atom_same atom (fun k hk =>
      reportSame k (GeneralNominalReportSupport237.checks_sources _ _ atom h hk))).mp
    exact raw.2.1 atom h
  have merges := GeneralNominalVersionedSelectiveAggregate236.merges p.context.state p.registry
    p.site.occurrence.identity p.declaration p.bindings m reused (by
      intro item present
      obtain ⟨a,b⟩ := found item present
      exact ⟨List.mem_append_right _ a,List.mem_append_right _ b⟩)
  have projected := (GeneralNominalReportSupport237.projection_iff p.context.state
    (GeneralNominalPacketSupport.report p) reportSame).mp raw.2.2
  have base : GeneralNominalState.Models p.context.state patch := by
    rw [current]
    exact live.1.1
  exact ⟨live,(GeneralNominalVersionedPlans231.private_models_iff p patch).mpr
    ⟨base,cross,merges,checks⟩,projected⟩

theorem full_head_of_trace {s : State roles} {p : Packet roles} {m : Assignment}
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (current : p.context = s.core.erased.current.context)
    (valid : Models s m) (raw : Raw p m) (adequate : Sufficient s p) :
    ∃ n, Models s n ∧ HeadModels p n := by
  obtain ⟨names,support,covered⟩ := adequate
  have seed := GeneralNominalVersionedMixedSeedLedger237.reachable path
  exact ⟨_,full_head current support valid raw (GeneralNominalVersionedAggregateLedger236.protected_equations
    (GeneralNominalVersionedMixedSeedLedger237.covered seed current covered) valid)⟩

variable {roles : Roles.RoleDecls} {registry : Registry} {s : State roles}
  {root focus : Occurrence roles} {m : Assignment}

def Coverage (registry : Registry) (s : State roles) (focus : Occurrence roles) (decl : Declaration) : Prop :=
  ∀ checked bounds, reads s.core.erased.current.context focus = some bounds →
    Sufficient s (atFocus s registry focus decl checked bounds)

theorem coverage_of_trace (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (certificate : ∀ names, Support s names → ∀ checked bounds,
      reads s.core.erased.current.context focus = some bounds →
      let p := atFocus s registry focus decl checked bounds
      IdCovered (protectedPool p names) s p) :
    Coverage registry s focus decl := by
  obtain ⟨_,names,_,_,supported⟩ := GeneralNominalVersionedTraceSupport237.source path
  intro checked bounds seen
  exact ⟨names,supported,certificate names supported checked bounds seen⟩

theorem prepared
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (selected : Local registry s focus (.selected key children))
    (valid : Models s m)
    {prior : Packet roles} (stored : prior ∈ s.core.erased.current.packets)
    (alias : Alias s.core.erased.current focus.identity prior.site.occurrence.identity)
    (coverage : Coverage registry s focus prior.declaration) :
    Prepared (Compiled registry) s.core.erased.current.context focus prior.declaration := by
  rcases GeneralNominalVersionedMixedChoice236.historical_prepared_or_failed checked path selected stored alias with ready|failed
  · exact ready
  obtain ⟨metadata,bounds,located,fresh,blocked,arity,_⟩ := failed
  have compiled := GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked
  have verify (decl : Declaration) (shown : decl ∈ (Compiled registry).declarations) :
      DeclarationChecked (Compiled registry).constructors roles decl :=
    Eq.mp (congrArg (fun rs => DeclarationChecked (Compiled registry).constructors rs decl) compiled.1)
      (compiled.2.2 decl shown)
  have verified := verify prior.declaration (GeneralNominalVersionedMixedChoiceHistory236.visible path stored)
  let p := atFocus s registry focus prior.declaration verified bounds
  obtain ⟨current,frame,_⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
  let now : GeneralNominalCenters.Plan roles := ⟨p,current.input,current.input_exact.trans frame.occurrence_eq⟩
  obtain ⟨historical,member,same⟩ := GeneralNominalVersionedMixedChoiceHistory236.packet_plan path stored
  have linked : Alias s.core.erased.current now.packet.site.occurrence.identity historical.packet.site.occurrence.identity := by
    rw [same]
    exact alias
  have meaning := GeneralVersionedAliasReport312.from_alias checked path historical now member frame.center_recorded
    rfl located linked (congrArg Packet.declaration same).symm m valid
  obtain ⟨next,_,head⟩ := full_head_of_trace (p := p) path rfl valid meaning.2 (coverage verified bounds located)
  exact ⟨metadata,frame.prepared.2.1,bounds,located,fresh,⟨blocked,meaning.1,arity⟩,next,
    (GeneralNominalVersionedCandidates231.headModels_packet_iff p next).mpr head⟩

theorem choice {packet : Packet roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (selected : Local registry s packet.site.occurrence (.selected packet.declaration.id children))
    (inhabited : ∃ m, Models s m)
    (coverage : ∀ prior ∈ s.core.erased.current.packets,
      Alias s.core.erased.current packet.site.occurrence.identity prior.site.occurrence.identity →
      Coverage registry s packet.site.occurrence prior.declaration) :
    GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current packet := by
  obtain ⟨_,valid⟩ := inhabited
  apply (GeneralNominalVersionedMixedChoice236.choice_iff_prepared checked path selected).mpr
  intro prior stored alias
  exact prepared checked path selected valid stored alias (coverage prior stored alias)

end Yulang.GeneralVersionedSemanticPeer312
