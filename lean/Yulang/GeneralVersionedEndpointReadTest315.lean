import Yulang.GeneralVersionedEndpointCuts315
import Yulang.GeneralVersionedChildDemandCut315

set_option backward.isDefEq.respectTransparency false
/-! Turn an exact read-level sufficient certificate into the narrowed
recursive endpoint obligation. Nonempty raw captures are derived from the
checked source head, not added to the certificate interface. -/
namespace Yulang.GeneralVersionedEndpointReadTest315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedFrame231 (capture)
open GeneralNominalMaterialization (Mode)
open GeneralNominalRecursiveInspection (Finished)
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralVersionedEndpointCuts315 (occurs merged LowerSame UpperSame)
open GeneralVersionedTightOperands315 (TightSide)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatSchemas (generated)
open GeneralVersionedRootWrites312 (whereRequests)
open GeneralVersionedEndpointLedger314 (Endpoint)
open GeneralNominalVersionedExpressionFrame236 (reads)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralVersionedJointWrites312 (protect)

theorem nonempty (p : Plan roles) (finished : Finished (headInspection p)) (name : Nat)
    (named : name ∈ p.packet.declaration.inputNames) :
    occurs p.packet name ≠ [] := by
  obtain ⟨origin,seen⟩ := GeneralNominalHeadSchemaSemantic186.input_use p finished name named
  obtain ⟨capture,member,same,_⟩ := GeneralNominalSchemaCapture187.schemas_capture
    p.packet.context.state _ p.packet.bounds _ 0 finished ⟨name,origin,.actual⟩ seen
  change capture.name = name at same
  unfold occurs
  rw [← GeneralDictionaryDefaultProjectionBounds215.head_bindings p,← same]
  exact GeneralNominalCaptureBounds187.occurrence_nonempty _ _ _ member

def Test (p q : Plan roles) (m : Assignment) (mode : Mode) (name : Nat) : Prop :=
  (name ∈ p.packet.declaration.inputNames ∨ name ∈ p.packet.declaration.outputNames) ∧
  (mode = .actual ∨ name ∈ p.packet.declaration.outputNames ∨
    (TightSide q m mode name ∧ TightSide p m mode name) ∨
    (mode = .lower ∧ LowerSame q.packet p.packet m name) ∨
    (mode = .upper ∧ UpperSame q.packet p.packet m name))

theorem operand {s : State roles} {p q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (identity : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (rule : q.packet.declaration = p.packet.declaration)
    (m : Assignment) (valid : Models s m) (head : HeadModels p.packet m) (schema : SchemaHolds p p.headSchema m)
    (mode : Mode) (name : Nat) (certificate : Test p q m mode name) :
    Equivalent (variables q m mode name) (variables p m mode name) := by
  obtain ⟨named,rfl|output|tight|⟨rfl,lower⟩|⟨rfl,upper⟩⟩ := certificate
  · exact GeneralVersionedTightOperands315.operand checked actual frame stored identity rule m valid head schema _ _ named (.inl rfl)
  · exact GeneralVersionedTightOperands315.operand checked actual frame stored identity rule m valid head schema _ _ named (.inr (.inl output))
  · exact GeneralVersionedTightOperands315.operand checked actual frame stored identity rule m valid head schema _ _ named (.inr (.inr tight))
  all_goals
    by_cases isOut : name ∈ p.packet.declaration.outputNames
    · exact GeneralVersionedTightOperands315.operand checked actual frame stored identity rule m valid head schema _ _ named (.inr (.inl isOut))
    have oldOut : name ∉ q.packet.declaration.outputNames := by rwa [rule]
    have currentName := named.resolve_right isOut
    have oldName : name ∈ q.packet.declaration.inputNames := rule.symm ▸ currentName
    have currentNonempty := nonempty p (GeneralNominalVersionedCurrentProjection237.frame_finished p frame) name currentName
    have oldNonempty := nonempty q (GeneralVersionedSiteOrigins312.stored_finished actual stored) name oldName
    have oldEquation : merged q.packet m := (valid.2.1 q stored).2.1.1.2.1
    have currentEquation : merged p.packet m :=
      ((GeneralNominalVersionedPlans231.private_models_iff ..).mp head.1).2.2.1
    simp only [variables,isOut,oldOut,ite_false]
  · exact (GeneralVersionedEndpointCuts315.lower_equivalent q.packet p.packet m name oldName currentName
      oldEquation currentEquation oldNonempty currentNonempty).mpr lower
  · exact (GeneralVersionedEndpointCuts315.upper_equivalent q.packet p.packet m name oldName currentName
      oldEquation currentEquation oldNonempty currentNonempty).mpr upper

def Certificate (s : State roles) (e : Effect roles) : Prop :=
  ∀ m, Models s m → HeadModels e.plan.packet m → SchemaHolds e.plan e.plan.headSchema m → e.Live s.core m →
    (∃ p ∈ s.plans, p.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity) →
    ∀ row ∈ (generated e.plan.packet.registry.constructors e.plan.packet.context.interpretation
      (whereRequests e.plan)).equations, row.target ∈ protect s e (sources s) → Endpoint e.plan row →
      ∃ p ∈ s.plans, p.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity ∧
        ∀ cell ∈ reads row.mode row.expression, Test e.plan p m cell.1 cell.2

theorem readback {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key e.plan)
    (certified : Certificate s e) : GeneralVersionedEndpointReduction314.Readback s e := by
  intro m valid head schema live history row emitted guarded endpoint
  obtain ⟨p,stored,owner,tests⟩ := certified m valid head schema live history row emitted guarded endpoint
  have rule := GeneralVersionedHistoricalHead314.declaration checked actual selected frame valid stored owner
  exact ⟨p,stored,owner,fun cell member =>
    operand checked actual frame stored owner rule m valid head schema cell.1 cell.2 (tests cell member)⟩

end Yulang.GeneralVersionedEndpointReadTest315
