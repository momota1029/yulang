import Yulang.GeneralVersionedRevisitCut315

set_option backward.isDefEq.respectTransparency false
/-! Deterministic same-owner head completion from any live assignment.
Old journal values and all actual report reads remain untouched; neither
class output semantics nor the centered head requires a second model. -/
namespace Yulang.GeneralVersionedCompleteInModel315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedSemanticPeer312 (complete reportPool protectedPool)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralVersionedAliasHeadWrites312 (rows pool)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (applyWrites)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalSaturationState (Alias)
open GeneralVersionedEndpointWholeRhs315 (AgreeRhs)
open GeneralVersionedChildEndpointCut315 (BaseReady)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)

noncomputable def fill (s : State roles) (p q : Plan roles) (m : Assignment) : Assignment :=
  let initial := complete p.packet (sources s) m
  applyWrites (rows p q initial) (pool p (sources s)) initial

theorem preserved (s : State roles) (p q : Plan roles) (m : Assignment) :
    Agree (sources s ++ reportPool p.packet) m (fill s p q m) := by
  intro id present
  have base : m id = complete p.packet (sources s) m id :=
    (GeneralNominalSelectiveEquationRealization236.preserves _ _ id present).symm
  have stays : id ∈ pool p (sources s) := by
    rcases List.mem_append.mp present with journal|read
    · simp [pool,journal]
    · have checked : id ∈ GeneralNominalVersionedResidualFrame237.headSources p.packet :=
        List.mem_append_right _ read
      simp [pool,checked]
  exact base.trans (GeneralFiniteTypedWrites312.preserved _ _ _ id stays)

theorem shared {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans) (same : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (m : Assignment) (models : Models s m) :
    let ready := fill s p q m
    Models s ready ∧ HeadModels p.packet ready ∧ SchemaHolds p p.headSchema ready ∧
      ClassEffects s.core p.packet.site.occurrence p ready := by
  have decl := (GeneralVersionedHistoricalHead314.declaration checked actual selected frame models stored same).symm
  have alias : Alias s.core.erased.current p.packet.site.occurrence.identity q.packet.site.occurrence.identity :=
    same.symm ▸ Alias.refl _
  have locate := frame.occurrence_eq.symm ▸ frame.located
  have raw := (GeneralVersionedAliasReport312.from_alias checked actual q p stored frame.center_recorded
    frame.context_eq locate alias decl m models).2
  have support := GeneralNominalVersionedModelSupport237.current s
  have ledger := GeneralVersionedHistoricalHead314.ledger checked actual selected frame models
  have covered := GeneralNominalVersionedMixedSeedLedger237.covered
    (GeneralNominalVersionedMixedSeedLedger237.reachable actual) frame.context_eq ledger
  have validEquations := GeneralNominalVersionedAggregateLedger236.protected_equations covered models
  let before := complete p.packet (sources s) m
  obtain ⟨valid,head⟩ := GeneralVersionedSemanticPeer312.full_head frame.context_eq support models raw validEquations
  have exactFrame : Frame (Compiled registry) s.core p.packet.site.occurrence p.packet.declaration.id p :=
    frame.occurrence_eq.symm ▸ frame.key_eq.symm ▸ frame
  obtain ⟨coherent,fixed⟩ := GeneralVersionedBinderReuse312.head_table checked actual exactFrame stored alias decl
    (GeneralVersionedPrivateJournal314.owned checked actual frame) before valid head
  obtain ⟨live,packet,centered⟩ := GeneralVersionedAliasHeadWrites312.complete checked actual exactFrame stored alias decl
    support before valid head coherent fixed
  exact ⟨live,packet,centered.2.2,
    GeneralVersionedHistoricalClasses315.live checked actual selected frame stored same _ live centered.2.2⟩

theorem joint {s : State roles} {e : Effect roles} {q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids))
    (rg : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (stored : q ∈ s.plans) (same : q.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity)
    (m : Assignment) (valid : Models s m) (rhs : AgreeRhs e.plan q (fill s e.plan q m)) :
    ∃ n, GeneralNominalVersionedMixedMaterialization237.Residual s e n := by
  have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    rg ▸ snapshot ▸ e.frame
  obtain ⟨live,head,schema,_⟩ := shared checked actual selected frame stored same m valid
  exact (GeneralVersionedEndpointWholeRhs315.joint_with_rhs checked actual selected rg snapshot stored same).mpr
    ⟨_,live,head,schema,rhs⟩

end Yulang.GeneralVersionedCompleteInModel315
