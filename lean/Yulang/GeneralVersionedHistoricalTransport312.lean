import Yulang.GeneralVersionedProtectedPeer312

set_option backward.isDefEq.respectTransparency false
/-! At an actual selected node, historical candidates are already classified
as prepared-or-failed. A current conflict-free report, a model for its
non-aggregate tests and finite ledger coverage rule out the failed case.
No ordinary-extension bound equality, same occurrence, or key agreement. -/
namespace Yulang.GeneralVersionedHistoricalTransport312
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalSaturationState (Packet Alias)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralVersionedAggregatePeer311 (probe)
open GeneralVersionedPeerChoice311 (reads)
open GeneralVersionedProtectedPeer312 (semanticPool Raw Observation)

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {root focus : Occurrence roles} {m : Assignment}

abbrev atFocus (state : State roles) (registry : Registry) (focus : Occurrence roles)
    (decl : Declaration) (checked : DeclarationChecked (Compiled registry).constructors roles decl)
    (bounds : List (GeneralNominalInspection.Bounds state.core.erased.current.context.state)) : Packet roles :=
  probe (Compiled registry) state.core.erased.current.context focus decl checked bounds

def Transfer (registry : Registry) (state : State roles) (focus : Occurrence roles)
    (decl : Declaration) (m : Assignment) : Prop :=
  ∀ checked : DeclarationChecked (Compiled registry).constructors roles decl,
  ∀ bounds, reads state.core.erased.current.context focus = some bounds →
    let p := atFocus state registry focus decl checked bounds
    (GeneralNominalPacketSupport.report p).conflicts = [] ∧ Raw p m ∧
      IdCovered (semanticPool p) state p

theorem prepared
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (selected : Local registry state focus (.selected key children))
    (valid : Models state m)
    {prior : Packet roles} (present : prior ∈ state.core.erased.current.packets)
    (alias : Alias state.core.erased.current focus.identity prior.site.occurrence.identity)
    (proof : Transfer registry state focus prior.declaration m) :
    Prepared (Compiled registry) state.core.erased.current.context focus prior.declaration := by
  rcases GeneralNominalVersionedMixedChoice236.historical_prepared_or_failed checked path selected present alias with ready|failed
  · exact ready
  obtain ⟨metadata,bounds,located,fresh,blocked,arity,_⟩ := failed
  have compiled := GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked
  have visible := GeneralNominalVersionedMixedChoiceHistory236.visible path present
  have verifyDecl (decl : Declaration) (shown : decl ∈ (Compiled registry).declarations) :
      DeclarationChecked (Compiled registry).constructors roles decl :=
    Eq.mp (congrArg (fun rs => DeclarationChecked (Compiled registry).constructors rs decl) compiled.1)
      (compiled.2.2 decl shown)
  have verified := verifyDecl prior.declaration visible
  obtain ⟨current,frame,_⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
  obtain ⟨conflicts,raw,covered⟩ := proof verified bounds located
  exact GeneralVersionedProtectedPeer312.prepared_on_trace
    (p := atFocus state registry focus prior.declaration verified bounds) path rfl located metadata frame.prepared.2.1
    fresh ⟨blocked,conflicts,arity⟩ valid raw covered

theorem choice {packet : Packet roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (selected : Local registry state packet.site.occurrence (.selected packet.declaration.id children))
    (valid : Models state m)
    (transport : ∀ prior ∈ state.core.erased.current.packets,
      Alias state.core.erased.current packet.site.occurrence.identity prior.site.occurrence.identity →
      Transfer registry state packet.site.occurrence prior.declaration m) :
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current packet := by
  apply (GeneralNominalVersionedMixedChoice236.choice_iff_prepared checked path selected).mpr
  intro prior present alias
  exact prepared checked path selected valid present alias (transport prior present alias)

theorem transfer_of_observations
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    {prior : Packet roles} (present : prior ∈ state.core.erased.current.packets)
    (valid : Models state m)
    (observed : ∀ checked bounds, reads state.core.erased.current.context focus = some bounds →
      let peer := atFocus state registry focus prior.declaration checked bounds
      (GeneralNominalPacketSupport.report peer).conflicts = [] ∧
      Observation prior = Observation peer ∧ IdCovered (semanticPool peer) state peer) :
    Transfer registry state focus prior.declaration m := by
  intro verified bounds located
  obtain ⟨noConflict,observation,covered⟩ := observed verified bounds located
  exact ⟨noConflict,GeneralVersionedProtectedPeer312.raw_transport observation
    (GeneralVersionedProtectedPeer312.recorded_raw path present valid),covered⟩

end Yulang.GeneralVersionedHistoricalTransport312
