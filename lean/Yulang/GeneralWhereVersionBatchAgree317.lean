import Yulang.GeneralVersionedEndpointBatch315

set_option backward.isDefEq.respectTransparency false
/-! The checked batch write exposes exact preservation on old journal support,
not just existence of another model. No prior coordinate can be reinterpreted. -/
namespace Yulang.GeneralWhereVersionBatchAgree317
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedTraceDomain313 (seed)
open GeneralNominalIdentities (Origin source)
open GeneralVersionedEndpointAddress315 (Side atCell fields key)
open GeneralVersionedEndpointSourceKey315 (SourceRow Row)
open GeneralVersionedEndpointPatch315 (operand_absent head_absent schema_absent classes_absent)
open GeneralVersionedChildEndpointCut315 (BaseReady)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralNominalVersionedExpressionFrame236 (reads variable_value value_eq)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (Write Coherent Protected Holds applyWrites reflexive)
open GeneralNominalVersionedJournalFrame236 (sources)
open CommonNominalFullCarrier (Equivalent)

open GeneralVersionedEndpointBatch315 (Proposal outside compatible)

theorem batch_agrees {s : State roles} {e : Effect roles} {m : Assignment}
    (actual : Reachable registry root s)
    (rg : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (before : BaseReady s e m) (proposed : List (Proposal e.plan)) :
    ∃ n, BaseReady s e n ∧ GeneralNominalCenteredFrame179.Agree (sources s) m n ∧ ∀ row ∈ proposed, Equivalent (n row.target).1 (row.rhs n) := by
  let rows := proposed.map (fun r => r.write m)
  let next := applyWrites rows [] m
  let p := e.plan
  have f : Frame (Compiled registry) s.core p.packet.site.occurrence p.packet.declaration.id p :=
    rg ▸ snapshot ▸ e.frame
  have coincides (id : Nat) (safe : ∀ k : Origin, 9 < k.2.2.1 → id ≠ source (seed s) k) :
      m id = next id := by
    apply outside
    intro row present
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp present
    have equal : r.target = source (seed s) (key p r.side r.clause.id r.pos r.row.expression) := by
      change source p.packet.context.state.seed _ = _
      rw [f.context_eq]
    have tag : 9 < (key p r.side r.clause.id r.pos r.row.expression).2.2.1 := by
      change 9 < r.side.purpose
      cases r.side <;> decide
    exact fun eq => safe _ tag (eq.symm.trans equal)
  have conf : Coherent rows := by
    intro a one b two eq
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp one
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp two
    change Equivalent (r.rhs m) (z.rhs m)
    rw [compatible r z eq m]
    exact reflexive _
  have fixed : Protected rows [] m := by intro _ _ empty; cases empty
  have yes := GeneralFiniteTypedWrites312.solves rows [] m conf fixed
  have valid := (GeneralNominalVersionedModelSupport237.current s m next
    (fun id seen => coincides id (fun _ high => GeneralVersionedHighJournal315.all actual high id seen))).mp before.1
  have raw₀ : GeneralNominalState.Models p.packet.context.state m := f.context_eq.symm ▸ before.1.1.1
  have raw₁ : GeneralNominalState.Models p.packet.context.state next := f.context_eq.symm ▸ valid.1.1
  have head := (GeneralNominalVersionedResidualFrame237.head_models_iff p.packet raw₀ raw₁
    (fun id seen => coincides id (fun _ k => head_absent actual k f id seen))).mp before.2.1
  have schema := (GeneralNominalVersionedHeadFrame236.schema_iff p p.headSchema
    (fun id seen => coincides id (fun _ k => schema_absent actual k f id seen))).mp before.2.2.1
  have live := (GeneralNominalVersionedJournalFrame236.class_iff s.core p.packet.site.occurrence p
    (fun id seen => coincides id (fun _ k => classes_absent actual k f id seen))).mp before.2.2.2
  refine ⟨next,⟨valid,head,schema,live⟩,?_,?_⟩
  · intro id seen
    exact coincides id (fun _ high => GeneralVersionedHighJournal315.all actual high id seen)
  intro row occurs
  have wrote := yes (row.write m) (List.mem_map.mpr ⟨row,occurs,rfl⟩)
  have sameRhs : row.rhs m = row.rhs next := by
    unfold Proposal.rhs
    apply value_eq
    intro cell _seen
    simp only [variable_value]
    exact congrArg Prod.fst (coincides _ (fun _ high => operand_absent actual f.context_eq high cell.1 cell.2))
  change Equivalent (next row.target).1 (row.rhs m) at wrote
  exact sameRhs ▸ wrote

end Yulang.GeneralWhereVersionBatchAgree317
