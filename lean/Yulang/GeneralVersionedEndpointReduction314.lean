import Yulang.GeneralVersionedEndpointLedger314

set_option backward.isDefEq.respectTransparency false
/-! Checked reduction of general recursive dictionary evidence: exact
foreign alias compatibility and old/live agreement only at operand reads
of protected compound where endpoints. This module assumes those two
remaining inputs; it is not a proof of the unconditional boundary. -/
namespace Yulang.GeneralVersionedEndpointReduction314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds variables childSchema)
open GeneralNominalCenteredHeadMatSchemas (generated)
open GeneralVersionedRootWrites312 (inner whereRequests)
open GeneralVersionedEndpointLedger314 (Endpoint)
open GeneralNominalVersionedExpressionFrame236 (reads)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralVersionedJointWrites312 (protect)
open CommonNominalFullCarrier (Equivalent)
open GeneralVersionedRemainingWrites314 (ForeignChoice ReusedRows)

def Readback (s : State roles) (e : Effect roles) : Prop :=
  ∀ m, Models s m → HeadModels e.plan.packet m → SchemaHolds e.plan e.plan.headSchema m → e.Live s.core m →
    (∃ p ∈ s.plans, p.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity) →
    ∀ row ∈ (generated e.plan.packet.registry.constructors e.plan.packet.context.interpretation
      (whereRequests e.plan)).equations, row.target ∈ protect s e (sources s) → Endpoint e.plan row →
      ∃ p ∈ s.plans, p.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity ∧
        ∀ cell ∈ reads row.mode row.expression,
          Equivalent (variables p m cell.1 cell.2) (variables e.plan m cell.1 cell.2)

theorem reused {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key e.plan)
    (required : Readback s e) : ReusedRows s e := by
  classical
  intro m valid head schema live row enters guarded nontrivial
  by_cases history : ∃ p ∈ s.plans, p.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity
  · rcases List.mem_append.mp enters with whereRow|childRow
    · rcases GeneralVersionedEndpointLedger314.exact_where e.plan row whereRow with trivial|endpoint|output
      · exact trivial m
      · obtain ⟨p,stored,owner,same⟩ := required m valid head schema live history row whereRow guarded endpoint
        have rule := GeneralVersionedHistoricalHead314.declaration checked actual selected frame valid stored owner
        exact GeneralVersionedEndpointLedger314.on_reads stored valid
          (GeneralVersionedEndpointLedger314.previous_of_endpoint actual frame stored owner rule endpoint) same
      · obtain ⟨p,stored,owner⟩ := history
        have rule := GeneralVersionedHistoricalHead314.declaration checked actual selected frame valid stored owner
        exact GeneralVersionedRevisitActual314.output checked actual frame stored owner rule m valid schema row output
    · obtain ⟨p,stored,owner⟩ := history
      have rule := GeneralVersionedHistoricalHead314.declaration checked actual selected frame valid stored owner
      obtain ⟨c,_,equation⟩ := List.mem_flatMap.mp childRow
      exact GeneralVersionedRevisitActual314.child checked actual frame stored owner rule m valid schema c.val c.property _ row equation
  · have unseen : GeneralVersionedUnseenBinder313.Unseen s e.plan :=
      fun p stored owner => history ⟨p,stored,owner⟩
    rcases nontrivial with cell|computed
    · exact False.elim (GeneralVersionedNewOwnerInstall314.cell_free actual unseen frame cell guarded)
    · exact False.elim (GeneralVersionedNewOwnerInstall314.output_free actual unseen frame computed guarded)

theorem closed_reads {s : State roles} {e : Effect roles}
    (noRead : ∀ row ∈ (generated e.plan.packet.registry.constructors e.plan.packet.context.interpretation
      (whereRequests e.plan)).equations,
      row.target ∈ protect s e (sources s) → Endpoint e.plan row → reads row.mode row.expression = []) :
    Readback s e := by
  intro m valid head schema live history row member guarded endpoint
  obtain ⟨p,stored,owner⟩ := history
  exact ⟨p,stored,owner,fun cell atCell => False.elim (by rw [noRead row member guarded endpoint] at atCell; cases atCell)⟩

theorem installable {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m) (alias : ForeignChoice s e.plan.packet)
    (readback : Readback s e) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled registry) s e :=
  GeneralVersionedRemainingWrites314.installable checked actual selected registryEq snapshot inhabited alias
    (reused checked actual selected (registryEq ▸ snapshot ▸ e.frame) readback)

theorem node_and_edges {s : State roles} {root focus : Occurrence roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (stable : (boundary roles).Stable registry s focus)
    (reached : focus = root ∨ GeneralNominalSaturationState.Generated s.core.erased.current root focus)
    (valid : Models s m)
    (ordered : CommonRoleOutermostResolver.All₂ (Evidence (Compiled registry) s.core m) kids dictionaries)
    (justify : ∀ e : Effect roles, e.registry = Compiled registry → e.snapshot = s.core →
      e.plan.packet.site.occurrence = focus → e.plan.packet.declaration.id = key →
      ForeignChoice s e.plan.packet ∧ Readback s e) :
    Evidence (Compiled registry) s.core m focus (.node key dictionaries) ∧
      ∀ child ∈ kids, GeneralNominalSaturationState.Generated s.core.erased.current root child := by
  apply GeneralVersionedRemainingWrites314.node_and_edges checked actual selected stable reached valid ordered
  intro e reg snap occ keyEq
  obtain ⟨yes,proof⟩ := justify e reg snap occ keyEq
  exact ⟨yes,reused checked actual selected (reg ▸ snap ▸ occ ▸ keyEq ▸ e.frame) proof⟩

end Yulang.GeneralVersionedEndpointReduction314
