import Yulang.GeneralVersionedPeerChoice311
import Yulang.GeneralNominalVersionedPrivateCompletion236

set_option backward.isDefEq.respectTransparency false
/-! In the choice bridge, HeadModels is existential in the private assignment.
Fresh aggregate names can be realized without changing any live raw input;
the resulting assignment is not assumed to satisfy the full journal. -/
namespace Yulang.GeneralVersionedAggregatePeer311
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedCandidates231 (Prepared HeadModels inputs)
open GeneralNominalRecursiveCandidates (Context report)
open GeneralNominalRecursiveInspection (bindings)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalSaturationState (Alias Packet)
open GeneralVersionedHistoryChoice310 (OrdinaryOwner)
open GeneralVersionedPeerChoice311 (reads)
open GeneralNominalVersionedAllocation231 (Fresh)

abbrev probe (r : Registry) (c : Context) (d : Occurrence roles) (decl : Declaration)
    (checked : DeclarationChecked r.constructors roles decl)
    (bounds : List (GeneralNominalInspection.Bounds c.state)) : Packet roles :=
  ⟨r,c,GeneralNominalDemandMerging.pointSite d,decl,checked,bounds⟩

abbrev Apart (r : Registry) (c : Context) (d : Occurrence roles) (decl : Declaration)
    (checked : DeclarationChecked r.constructors roles decl)
    (bounds : List (GeneralNominalInspection.Bounds c.state)) : Prop :=
  GeneralNominalVersionedPrivateCompletion236.Fresh (probe r c d decl checked bounds)

theorem apart_of_unallocated (r : Registry) (c : Context) (d : Occurrence roles) (decl : Declaration)
    (checked : DeclarationChecked r.constructors roles decl)
    (bounds : List (GeneralNominalInspection.Bounds c.state))
    (visible : decl ∈ r.declarations)
    (fresh : Fresh c.state r d.identity (bindings c.state (report c decl bounds)))
    (never : ∀ k ∈ GeneralNominalVersionedAllocation231.keys r d.identity
      (bindings c.state (report c decl bounds)), k ∉ c.state.allocated) :
    Apart r c d decl checked bounds := by
  intro name named _
  have keys := GeneralNominalVersionedAllocation231.input_keys (root := d.identity)
    (bindings := bindings c.state (report c decl bounds)) visible named
  exact ⟨GeneralNominalVersionedAllocation231.fresh_key fresh keys.1 (never _ keys.1),
    GeneralNominalVersionedAllocation231.fresh_key fresh keys.2 (never _ keys.2)⟩

theorem prepared_at_fresh_peer (r : Registry) (c : Context) (a b : Occurrence roles) (decl : Declaration)
    (checked : DeclarationChecked r.constructors roles decl)
    (old : Prepared r c a decl)
    (observations : reads c a = reads c b)
    (registered : GeneralNominalState.Linked c.state (inputs b).demand)
    (fresh : ∀ bounds, reads c b = some bounds →
      Fresh c.state r b.identity (bindings c.state (report c decl bounds)))
    (apart : ∀ bounds, reads c b = some bounds → Apart r c b decl checked bounds) :
    Prepared r c b decl := by
  obtain ⟨metadata,_,bounds,located,_,finished,m,held⟩ := old
  have loc : reads c b = some bounds := observations.symm.trans located
  obtain ⟨raw,cross,_,checks⟩ :=
    (GeneralNominalVersionedCandidates231.private_models_iff r c (inputs a) decl bounds m).mp held.1
  let p := probe r c b decl checked bounds
  refine ⟨metadata,registered,bounds,loc,fresh bounds loc,finished,
    GeneralNominalVersionedPrivateCompletion236.extended p m,?_⟩
  exact (GeneralNominalVersionedCandidates231.headModels_packet_iff p _).mpr
    (GeneralNominalVersionedPrivateCompletion236.head_models p m (apart bounds loc) raw cross checks held.2)

variable {roles : Roles.RoleDecls} {registry : Registry} {s : State roles}
  {root focus : Occurrence roles} {m : Assignment}

def FreshPeerCertificate (r : Registry) (s : State roles) (prior : Packet roles) (focus : Occurrence roles) : Prop :=
  OrdinaryOwner s prior prior.site.occurrence ∧
  reads s.core.erased.current.context prior.site.occurrence = reads s.core.erased.current.context focus ∧
  (∀ bounds, reads s.core.erased.current.context focus = some bounds →
    Fresh s.core.erased.current.context.state (Compiled r) focus.identity
      (bindings s.core.erased.current.context.state (report s.core.erased.current.context prior.declaration bounds))) ∧
  ∀ bounds, reads s.core.erased.current.context focus = some bounds →
    Apart prior.registry s.core.erased.current.context focus prior.declaration prior.checked bounds

theorem choice {packet : Packet roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (selected : Local registry s packet.site.occurrence (.selected packet.declaration.id kids))
    (valid : Models s m)
    (transfer : ∀ prior ∈ s.core.erased.current.packets,
      Alias s.core.erased.current packet.site.occurrence.identity prior.site.occurrence.identity →
      FreshPeerCertificate registry s prior packet.site.occurrence) :
    GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current packet := by
  apply (GeneralNominalVersionedMixedChoice236.choice_iff_prepared checked path selected).mpr
  intro prior present linked
  obtain ⟨owner,obs,fresh,apart⟩ := transfer prior present linked
  have previous := GeneralVersionedHistoryChoice310.historical_prepared path present owner valid
  obtain ⟨current,frame,_⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
  have compiled : prior.registry = Compiled registry :=
    by
      obtain ⟨effect,recorded,packetEq⟩ := GeneralVersionedHistoryChoice310.historical_effect path present
      rw [← packetEq]
      exact effect.frame.registry_eq.trans
        ((GeneralNominalVersionedMixedRegistry234.reachable path).2.2 effect recorded)
  cases prior with
  | mk source context site decl verified bounds =>
    change source = Compiled registry at compiled
    subst source
    exact prepared_at_fresh_peer _ _ _ _ _ verified previous obs frame.prepared.2.1 fresh apart

end Yulang.GeneralVersionedAggregatePeer311
