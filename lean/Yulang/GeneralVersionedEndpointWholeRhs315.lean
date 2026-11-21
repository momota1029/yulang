import Yulang.GeneralVersionedHistoricalClasses315

set_option backward.isDefEq.respectTransparency false
/-! On a true same-owner revisit the matched compound endpoint rows are in
the live journal's support automatically. In one shared head model, the
exact extra condition is equivalence of the whole old/current RHS, with
no requirement that each individual operand remain equivalent. -/
namespace Yulang.GeneralVersionedEndpointWholeRhs315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds variables emittedSchema)
open GeneralVersionedEndpointLedger314 (Endpoint)
open GeneralVersionedEndpointEquationCut315 (whereRows EndpointEquations)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (transitive symmetric)
open CommonNominalFullCarrier (Equivalent)

abbrev Row := GeneralNominalCenteredHeadMatSchemas.Equation

theorem target_support {s : State roles} {q : Plan roles} {row : Row}
    (stored : q ∈ s.plans)
    (earlier : row ∈ (emittedSchema q).equations) : row.target ∈ sources s := by
  apply List.mem_append_left
  apply List.mem_append_right
  refine List.mem_flatMap.mpr ⟨q,stored,?_⟩
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨row,earlier,List.mem_cons_self⟩

def AgreeRhs (p q : Plan roles) (m : Assignment) : Prop :=
  ∀ row ∈ whereRows p, Endpoint p row →
    Equivalent (value (variables q m) row.mode row.expression)
      (value (variables p m) row.mode row.expression)

theorem endpoint_iff {s : State roles} {e : Effect roles} {q : Plan roles} {m : Assignment}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (f : Frame (Compiled registry) s.core focus key e.plan)
    (stored : q ∈ s.plans) (owner : q.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity)
    (valid : Models s m) :
    EndpointEquations s e m ↔ AgreeRhs e.plan q m := by
  have rule := GeneralVersionedHistoricalHead314.declaration checked actual selected f valid stored owner
  have original {row : Row} (cell : Endpoint e.plan row) :
      row ∈ (emittedSchema q).equations :=
    GeneralVersionedEndpointLedger314.previous_of_endpoint actual f stored owner rule cell
  constructor
  · intro endpoints row listed cell
    have was := (valid.2.1 q stored).2.2 row (original cell)
    have target := target_support stored (original cell)
    have isNow := endpoints row listed (by simp [GeneralVersionedJointWrites312.protect,target]) cell
    exact transitive (symmetric was) isNow
  · intro agree row listed _ cell
    have was := (valid.2.1 q stored).2.2 row (original cell)
    exact transitive was (agree row listed cell)

theorem joint_with_rhs {s : State roles} {e : Effect roles} {q : Plan roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids))
    (rg : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (stored : q ∈ s.plans) (owner : q.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity) :
    (∃ m, Residual s e m) ↔
    ∃ m, Models s m ∧ HeadModels e.plan.packet m ∧ SchemaHolds e.plan e.plan.headSchema m ∧ AgreeRhs e.plan q m := by
  have f : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    rg ▸ snapshot ▸ e.frame
  constructor
  · rintro ⟨m,residual⟩
    have ready := GeneralVersionedEndpointEquationCut315.ready_of_residual residual
    exact ⟨m,ready.1,ready.2.1,ready.2.2.1,(endpoint_iff checked actual selected f stored owner ready.1).mp ready.2.2.2.2⟩
  · rintro ⟨m,valid,head,schema,agree⟩
    exact GeneralVersionedEndpointEquationCut315.from_ready checked actual selected rg snapshot
      ⟨valid,head,schema,GeneralVersionedHistoricalClasses315.live checked actual selected f stored owner m valid schema,
        (endpoint_iff checked actual selected f stored owner valid).mpr agree⟩

end Yulang.GeneralVersionedEndpointWholeRhs315
