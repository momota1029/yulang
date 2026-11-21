import Yulang.GeneralVersionedRevisitActual314

set_option backward.isDefEq.respectTransparency false
/-! The full selected write table now reduces to protected lower/upper
compound where endpoints. Actual child centers and computed where outputs
can reuse the prior frame under arbitrary intervening interval versions. -/
namespace Yulang.GeneralVersionedRevisitEndpoints314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds variables childSchema)
open GeneralNominalVersionedFrame231 (capture frame)
open GeneralNominalCenteredHeadMatSchemas (generated materialize)
open GeneralVersionedRootWrites312 (inner whereRequests from_request)
open GeneralVersionedComputedRows313 (OutputCell output_row)
open GeneralVersionedCompoundRows313 (Cell Taut lower_or_upper materializes)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralVersionedJointWrites312 (protect)

abbrev Row := GeneralNominalCenteredHeadMatSchemas.Equation

def Bounds (s : State roles) (e : Effect roles) : Prop :=
  ∀ m, Models s m → HeadModels e.plan.packet m → SchemaHolds e.plan e.plan.headSchema m → e.Live s.core m →
    ∀ row ∈ (generated e.plan.packet.registry.constructors e.plan.packet.context.interpretation
      (whereRequests e.plan)).equations,
    row.target ∈ protect s e (sources s) →
    Cell e.plan row → row.mode ≠ .actual → row.Holds (variables e.plan m) m

theorem emitted (p : Plan roles) (eq : Row)
    (found : eq ∈ (generated p.packet.registry.constructors p.packet.context.interpretation
      (whereRequests p)).equations) : Taut p eq ∨ (Cell p eq ∧ eq.mode ≠ .actual) ∨ OutputCell p eq := by
  obtain ⟨rq,seen,materialized⟩ := from_request found
  obtain ⟨emit,emitted,inside⟩ := List.mem_flatMap.mp seen
  have posted := (GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity p.packet.declaration
    p.packet.checked (capture p.packet) ((frame p.packet).allocation p.packet.declaration.id)).mem_iff.mpr emitted
  unfold GeneralDeclarationDemands.emitAll at posted
  obtain ⟨item,_,rfl⟩ := List.mem_map.mp posted
  let clause := item.val
  have requirement := p.packet.checked.signature.2.2.2 clause item.property
  unfold GeneralNominalCenteredHeadMatSchemas.emissionRequests at inside
  rcases List.mem_append.mp inside with input|output
  · obtain ⟨arg,args,byArg⟩ := List.mem_flatMap.mp input
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp args
    rcases List.mem_cons.mp byArg with rfl|next
    · have split := lower_or_upper p clause item.property requirement index 3 (.inl rfl) eq materialized
      exact split.elim .inl (fun cell => .inr (.inl ⟨cell,fun no => by
        have mode := (materializes materialized).2.2
        rw [no] at mode
        cases mode⟩))
    · cases List.mem_singleton.mp next
      have split := lower_or_upper p clause item.property requirement index 4 (.inr rfl) eq materialized
      exact split.elim .inl (fun cell => .inr (.inl ⟨cell,fun no => by
        have mode := (materializes materialized).2.2
        rw [no] at mode
        cases mode⟩))
  · obtain ⟨request,requestMember,rfl⟩ := List.mem_map.mp output
    obtain ⟨rule,ruleMember,rfl⟩ := List.mem_map.mp requestMember
    exact (output_row p clause item.property rule ruleMember eq materialized).elim .inl
      (fun h => .inr (.inr h))

theorem reused {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (picked : Local registry s focus (.selected key kids))
    (current : Frame (Compiled registry) s.core focus key e.plan)
    (bounds : Bounds s e) : GeneralVersionedRemainingWrites314.ReusedRows s e := by
  classical
  intro m valid head schema live row found guarded nontrivial
  by_cases history : ∃ p ∈ s.plans, p.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity
  · obtain ⟨p,stored,same⟩ := history
    have rule := GeneralVersionedHistoricalHead314.declaration checked actual picked current valid stored same
    rcases List.mem_append.mp found with whereRow|childRow
    · rcases emitted e.plan row whereRow with taut|⟨cell,mode⟩|computed
      · exact taut m
      · exact bounds m valid head schema live row whereRow guarded cell mode
      · exact GeneralVersionedRevisitActual314.output checked actual current stored same rule m valid schema row computed
    · obtain ⟨clause,_,atClause⟩ := List.mem_flatMap.mp childRow
      exact GeneralVersionedRevisitActual314.child checked actual current stored same rule m valid schema
        clause.val clause.property _ row atClause
  · have unseen : GeneralVersionedUnseenBinder313.Unseen s e.plan :=
      fun p stored own => history ⟨p,stored,own⟩
    rcases nontrivial with cell|computed
    · exact False.elim (GeneralVersionedNewOwnerInstall314.cell_free actual unseen current cell guarded)
    · exact False.elim (GeneralVersionedNewOwnerInstall314.output_free actual unseen current computed guarded)

theorem installable {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (picked : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m)
    (alias : GeneralVersionedRemainingWrites314.ForeignChoice s e.plan.packet)
    (bounds : Bounds s e) : GeneralNominalVersionedMixedKernel234.Installable (Compiled registry) s e :=
  GeneralVersionedRemainingWrites314.installable checked actual picked registryEq snapshot inhabited alias
    (reused checked actual picked (registryEq ▸ snapshot ▸ e.frame) bounds)

end Yulang.GeneralVersionedRevisitEndpoints314
