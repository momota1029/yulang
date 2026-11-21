import Yulang.GeneralVersionedEndpointReadTest315

set_option backward.isDefEq.respectTransparency false
/-! For the selected ordinary effect, one preinstallation assignment with
the true protected endpoint equations suffices. Other rows are handled by
the actual source proofs. This need not identify endpoint operands one by
one, and need not hold in every compatible head/class model. -/
namespace Yulang.GeneralVersionedEndpointEquationCut315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds variables emittedSchema emittedRequests)
open GeneralNominalCenteredHeadMatSchemas (generated)
open GeneralVersionedRootWrites312 (inner whereRequests internalRows)
open GeneralVersionedEndpointLedger314 (Endpoint)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralVersionedJointWrites312 (protect)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralFiniteTypedWrites312 (Protected reflexive)
open GeneralVersionedCompoundRows313 (coherent_address)
open GeneralVersionedComputedRows313 (classifies addresses_disjoint)

abbrev whereRows (p : Plan roles) := (generated p.packet.registry.constructors
  p.packet.context.interpretation (whereRequests p)).equations

def EndpointEquations (s : State roles) (e : Effect roles) (m : Assignment) : Prop :=
  ∀ row ∈ whereRows e.plan, row.target ∈ protect s e (sources s) → Endpoint e.plan row →
    row.Holds (variables e.plan m) m

def ReadyModel (s : State roles) (e : Effect roles) (m : Assignment) : Prop :=
  Models s m ∧ HeadModels e.plan.packet m ∧ SchemaHolds e.plan e.plan.headSchema m ∧
    e.Live s.core m ∧ EndpointEquations s e m

theorem free_coherent {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry)
    (frame : Frame (Compiled registry) s.core focus key e.plan)
    (m : Assignment) :
    GeneralVersionedRootWrites312.FreeCoherent (internalRows e.plan m) (protect s e (sources s)) := by
  have output := GeneralVersionedFirstComputed313.proper_keys e.plan
    (GeneralVersionedCompiledFirstInstall313.key_coherence checked.2 frame.visible) m
  intro a aIn b bIn equal free
  obtain ⟨one,ho,rfl⟩ := List.mem_map.mp aIn
  obtain ⟨two,ht,rfl⟩ := List.mem_map.mp bIn
  have first := (classifies e.plan _ ho).resolve_left
    (fun taut => free (GeneralVersionedNewOwnerInstall314.taut_protected ho taut))
  have last := (classifies e.plan _ ht).resolve_left
    (fun taut => free (equal.symm ▸ GeneralVersionedNewOwnerInstall314.taut_protected ht taut))
  rcases first with first|first <;> rcases last with last|last
  · rw [coherent_address first last equal]
    exact reflexive _
  · exact False.elim (addresses_disjoint first last equal)
  · exact False.elim (addresses_disjoint last first equal.symm)
  · exact output _ _ first last equal

theorem guarded {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (frame : Frame (Compiled registry) s.core focus key e.plan)
    (m : Assignment) (valid : Models s m) (schema : SchemaHolds e.plan e.plan.headSchema m)
    (whereHeld : EndpointEquations s e m) :
    Protected (internalRows e.plan m) (protect s e (sources s)) m := by
  classical
  intro write present used
  obtain ⟨row,listed,rfl⟩ := List.mem_map.mp present
  change row.Holds (variables e.plan m) m
  by_cases history : ∃ p ∈ s.plans, p.packet.site.occurrence.identity = e.plan.packet.site.occurrence.identity
  · obtain ⟨q,stored,identity⟩ := history
    have rule := GeneralVersionedHistoricalHead314.declaration checked actual selected frame valid stored identity
    rcases List.mem_append.mp listed with whereRow|childRow
    · rcases GeneralVersionedEndpointLedger314.exact_where e.plan row whereRow with taut|endpoint|output
      · exact taut m
      · exact whereHeld row whereRow used endpoint
      · exact GeneralVersionedRevisitActual314.output checked actual frame stored identity rule m valid schema row output
    · obtain ⟨c,_,member⟩ := List.mem_flatMap.mp childRow
      exact GeneralVersionedRevisitActual314.child checked actual frame stored identity rule m valid schema
        c.val c.property _ row member
  · have unseen : GeneralVersionedUnseenBinder313.Unseen s e.plan :=
      fun q stored same => history ⟨q,stored,same⟩
    rcases classifies e.plan row listed with taut|cell|output
    · exact taut m
    · exact False.elim (GeneralVersionedNewOwnerInstall314.cell_free actual unseen frame cell used)
    · exact False.elim (GeneralVersionedNewOwnerInstall314.output_free actual unseen frame output used)

theorem from_ready {s : State roles} {e : Effect roles} {m : Assignment}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (ready : ReadyModel s e m) :
    ∃ n, Residual s e n := by
  have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    registryEq ▸ snapshot ▸ e.frame
  obtain ⟨valid,head,schema,live,endpoints⟩ := ready
  obtain ⟨coherent,fixed⟩ := GeneralVersionedRootWrites312.lift_table snapshot live
    (free_coherent checked frame m) (guarded checked actual selected frame m valid schema endpoints)
  exact ⟨_,GeneralVersionedJointWrites312.complete frame.context_eq
    (GeneralNominalVersionedModelSupport237.current s) valid head schema live coherent fixed⟩

theorem output_contains {p : Plan roles} {q : GeneralNominalCenteredHeadMatSchemas.Equation}
    (seen : q ∈ whereRows p) : q ∈ (emittedSchema p).equations := by
  unfold emittedSchema emittedRequests
  rw [GeneralVersionedRootWrites312.generated_append]
  exact List.mem_append_right _ seen

theorem ready_of_residual {s : State roles} {e : Effect roles} {m : Assignment}
    (residual : Residual s e m) : ReadyModel s e m := by
  refine ⟨residual.1,residual.2.1,residual.2.2.1,residual.2.2.2.2.2,?_⟩
  intro row seen _ _
  exact residual.2.2.2.1 row (output_contains seen)

theorem residual_iff {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (selected : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core) :
    (∃ m, Residual s e m) ↔ ∃ m, ReadyModel s e m :=
  ⟨fun ⟨m,res⟩ => ⟨m,ready_of_residual res⟩,
    fun ⟨_,ready⟩ => from_ready checked actual selected registryEq snapshot ready⟩

end Yulang.GeneralVersionedEndpointEquationCut315
