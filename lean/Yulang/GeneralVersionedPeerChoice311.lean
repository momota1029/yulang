import Yulang.GeneralVersionedHistoryChoice310
import Yulang.GeneralNominalVersionedMixedSelectedFrame235

set_option backward.isDefEq.respectTransparency false
/-! Retargeting historical head feasibility across actual alias peers. Current
observation agreement, fresh reservations and changes of aggregate equations
are distinct conditions; alias membership cannot be used in their place. -/
namespace Yulang.GeneralVersionedPeerChoice311
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedCandidates231 (Prepared HeadModels inputs)
open GeneralNominalRecursiveCandidates (Context arguments report)
open GeneralNominalRecursiveInspection (bindings)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalSaturationState (Alias Packet)
open GeneralVersionedHistoryChoice310 (OrdinaryOwner)
open GeneralNominalVersionedAllocation231 (Fresh merges)

abbrev reads (c : Context) (d : Occurrence roles) := arguments c (inputs d)

def Linear (c : Context) (decl : Declaration) (bounds : List (GeneralNominalInspection.Bounds c.state)) : Prop :=
  ∀ name ∈ decl.inputNames, ∃ endpoints,
    GeneralNominalAllocation.occurrences (bindings c.state (report c decl bounds)) name = [endpoints]

theorem linear_empty (c : Context) (r : Registry) (d : Occurrence roles) (decl : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds c.state)) (linear : Linear c decl bounds) :
    merges c.state r d.identity decl (bindings c.state (report c decl bounds)) = [] := by
  unfold merges
  apply List.flatMap_eq_nil_iff.mpr
  intro name mem
  obtain ⟨ends,exactly⟩ := linear name mem
  rw [exactly]

theorem head_transport (r : Registry) (c : Context) (a b : Occurrence roles) (decl : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds c.state)) (m : Assignment)
    (joint : PresenceNormalForm.All CommonNominalFullCarrier.model m
      (merges c.state r a.identity decl (bindings c.state (report c decl bounds))) →
      PresenceNormalForm.All CommonNominalFullCarrier.model m
      (merges c.state r b.identity decl (bindings c.state (report c decl bounds)))) :
    HeadModels r c a decl bounds m → HeadModels r c b decl bounds m := by
  intro old
  obtain ⟨raw,cross,equations,checks⟩ :=
    (GeneralNominalVersionedCandidates231.private_models_iff r c (inputs a) decl bounds m).mp old.1
  exact ⟨(GeneralNominalVersionedCandidates231.private_models_iff r c (inputs b) decl bounds m).mpr
    ⟨raw,cross,joint equations,checks⟩,old.2⟩

theorem linear_head_iff (r : Registry) (c : Context) (a b : Occurrence roles) (decl : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds c.state)) (m : Assignment)
    (linear : Linear c decl bounds) :
    HeadModels r c a decl bounds m ↔ HeadModels r c b decl bounds m := by
  constructor <;> apply head_transport
  · intro _
    rw [linear_empty c r b decl bounds linear]
    exact PresenceNormalForm.all_nil _ _
  · intro _
    rw [linear_empty c r a decl bounds linear]
    exact PresenceNormalForm.all_nil _ _

theorem prepared_at_peer (r : Registry) (c : Context) (a b : Occurrence roles) (decl : Declaration)
    (old : Prepared r c a decl)
    (observations : reads c a = reads c b)
    (registered : GeneralNominalState.Linked c.state (inputs b).demand)
    (fresh : ∀ bounds, reads c b = some bounds →
      Fresh c.state r b.identity (bindings c.state (report c decl bounds)))
    (linear : ∀ bounds, reads c a = some bounds → Linear c decl bounds) :
    Prepared r c b decl := by
  obtain ⟨metadata,_,bounds,located,_,finished,m,held⟩ := old
  have loc : reads c b = some bounds := observations.symm.trans located
  exact ⟨metadata,registered,bounds,loc,fresh bounds loc,finished,m,
    (linear_head_iff r c a b decl bounds m (linear bounds located)).mp held⟩

variable {roles : Roles.RoleDecls} {registry : Registry} {s : State roles}
  {root focus : Occurrence roles} {m : Assignment}

def PeerCertificate (r : Registry) (s : State roles) (prior : Packet roles) (focus : Occurrence roles) : Prop :=
  OrdinaryOwner s prior prior.site.occurrence ∧
  reads s.core.erased.current.context prior.site.occurrence = reads s.core.erased.current.context focus ∧
  (∀ bounds, reads s.core.erased.current.context focus = some bounds →
    Fresh s.core.erased.current.context.state (Compiled r) focus.identity
      (bindings s.core.erased.current.context.state (report s.core.erased.current.context prior.declaration bounds))) ∧
  ∀ bounds, reads s.core.erased.current.context prior.site.occurrence = some bounds →
    Linear s.core.erased.current.context prior.declaration bounds

/-- The former owner's exact demand may differ from the new peer. No
assumption that the historical/current declaration keys agree is made. -/
theorem choice {packet : Packet roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (selected : Local registry s packet.site.occurrence (.selected packet.declaration.id kids))
    (valid : Models s m)
    (transfer : ∀ prior ∈ s.core.erased.current.packets,
      Alias s.core.erased.current packet.site.occurrence.identity prior.site.occurrence.identity →
      PeerCertificate registry s prior packet.site.occurrence) :
    GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current packet := by
  apply (GeneralNominalVersionedMixedChoice236.choice_iff_prepared checked path selected).mpr
  intro prior present linked
  obtain ⟨owner,obs,fresh,linear⟩ := transfer prior present linked
  have previous := GeneralVersionedHistoryChoice310.historical_prepared path present owner valid
  obtain ⟨current,frame,_⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
  exact prepared_at_peer _ _ _ _ _ previous obs frame.prepared.2.1 fresh linear

end Yulang.GeneralVersionedPeerChoice311
