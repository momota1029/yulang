import Yulang.GeneralRebaseRowOutputHeadSupport288

/-! The independently justified child head fits the existing DecisionGuard.
This proves readiness of matching, not entitlement to record settlement. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseRowLeafDecisionGuard288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowLedger288 (supplemented)
open GeneralRebaseRowLeafReceipt288 (receipt)
open GeneralRebaseLeafReceipt288 (Receipt)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedSupport233 (ReadyAt DecisionGuard)
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)

variable {roleDecls : Roles.RoleDecls}

theorem ready_from_source {r : Registry} {s : State roleDecls} {o : Occurrence roleDecls}
    {k : Nat} {p : Plan roleDecls} (received : Receipt r s o k p) (i : Fin (roleDecls o.demand.role).arity) :
    ReadyAt s (o.demand.arguments i).1 := by
  obtain ⟨test,observation,read,sound⟩ := received.rootReadback i
  exact ⟨test,observation,read,[],.source,_,observation,read,sound⟩

variable {context : GeneralNominalCandidates.Context}

theorem only_variable_query (cert : Refresh supplemented context) :
    GeneralNominalInspection.queries context.state context.interpretation opaqueChild = [.variables [0]] := by
  have same : GeneralNominalInspection.queries context.state context.interpretation opaqueChild =
      GeneralNominalInspection.queries (GeneralRebaseRowGeneratedChild287.current true).state
        (GeneralRebaseRowGeneratedChild287.current true).interpretation opaqueChild := by
    simp only [GeneralNominalInspection.queries,cert.interpretation,cert.refines.constructors]
    rfl
  exact same.trans GeneralRebaseRowWholeChild287.query

theorem actual_guard (cert : Refresh supplemented context) :
    DecisionGuard (registry true) (refresh supplemented context) (child true) := by
  constructor
  · intro i
    exact ready_from_source (receipt cert) i
  · intro declaration member role bounds _ slot read
    cases GeneralRebaseRowLocal287.child_at_role true declaration member role
    change slot ∈ GeneralNominalSupport.readsMany context.state
      (GeneralNominalInspection.queries context.state context.interpretation opaqueChild) bounds at read
    rw [only_variable_query cert] at read
    cases bounds <;> simp [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads] at read

end Yulang.GeneralRebaseRowLeafDecisionGuard288
