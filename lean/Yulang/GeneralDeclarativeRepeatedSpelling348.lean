import Yulang.GeneralDeclarativeRepeatedVisible348

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 45000000
namespace Yulang.GeneralDeclarativeRepeatedSpelling348
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (declaration)
open GeneralLiveCompoundPostRootHead316 (adds)
open GeneralLiveCompoundCurrentRoot316 (packet bindings_exact)
open GeneralNominalVersionedInstallation231 (reserved atoms allocated)
open GeneralNominalVersionedTransport231 (packet_bindings extendedPacket)
open GeneralNominalVersionedExpressionFrame236 (variableSource)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeRepeatedRows348 (loRow hiRow low high)
open GeneralDeclarativeWhereAttributed346 (literal)
open GeneralWhereVersionInstall317 (fixed Models)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralDeclarativeTxnNormalized348 (same_rhs)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)

theorem bindings : rootPlan.packet.bindings = [(0,2,2),(0,2,2)] :=
  (packet_bindings (reserved adds) (atoms adds) (allocated adds) packet).trans bindings_exact

theorem names (mode : Mode) (nonactual : mode ≠ .actual) : 2 < variableSource rootPlan mode 0 := by
  have zero : ¬ (0 : Nat) ∈ rootPlan.packet.declaration.outputNames := by decide +kernel
  unfold variableSource
  simp only [zero,ite_false]
  have normalized :
      (GeneralNominalVersionedFrame231.capture rootPlan.packet).inputs 0 =
        (GeneralNominalAggregateVersion231.slot rootPlan.packet.context.state.seed
          rootPlan.packet.site.occurrence.identity rootPlan.packet.declaration.id 0 0 rootPlan.packet.bindings,
        GeneralNominalAggregateVersion231.slot rootPlan.packet.context.state.seed
          rootPlan.packet.site.occurrence.identity rootPlan.packet.declaration.id 1 0 rootPlan.packet.bindings) := by
    unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
    simp [GeneralNominalVersionedAllocation231.capture,bindings,GeneralNominalAllocation.occurrences]
  have four : rootPlan.packet.context.state.seed = 4 := rfl
  cases mode with
  | actual => exact False.elim (nonactual rfl)
  | lower =>
    rw [normalized]
    have h := GeneralNominalAggregateVersion231.above_seed rootPlan.packet.context.state.seed
      rootPlan.packet.site.occurrence.identity rootPlan.packet.declaration.id 0 0 rootPlan.packet.bindings
    exact Nat.lt_trans (show 2 < rootPlan.packet.context.state.seed by rw [four]; decide) h
  | upper =>
    rw [normalized]
    have h := GeneralNominalAggregateVersion231.above_seed rootPlan.packet.context.state.seed
      rootPlan.packet.site.occurrence.identity rootPlan.packet.declaration.id 1 0 rootPlan.packet.bindings
    exact Nat.lt_trans (show 2 < rootPlan.packet.context.state.seed by rw [four]; decide) h

theorem lower_spelling : loRow ≠ literal low := by
  intro same
  have rhs := congrArg Equation.right same
  change Expr.variant 0 (.variable 2) = .variant 0 (.variable (variableSource rootPlan .lower 0)) at rhs
  have eq := Expr.variable.inj (Expr.variant.inj rhs).2
  exact (Nat.ne_of_gt (names .lower (by decide))) eq.symm

theorem upper_spelling : hiRow ≠ literal high := by
  intro same
  have rhs := congrArg Equation.right same
  change Expr.variant 0 (.variable 2) = .variant 0 (.variable (variableSource rootPlan .upper 0)) at rhs
  have eq := Expr.variable.inj (Expr.variant.inj rhs).2
  exact (Nat.ne_of_gt (names .upper (by decide))) eq.symm

/-- The raw scan genuinely simplifies the aggregate operand names in
this repeated-C316 instance. A literal-only release would miss both.
Actual author/target receipts let us keep both spellings without
mistaking RHS equivalence for writing a different cell. -/
theorem actual_cut (m : Assignment) (fit : Models fixed m) :
    loRow ≠ literal low ∧ hiRow ≠ literal high ∧
    Equivalent (value (environment m) .actual loRow.right) (value (environment m) .actual (literal low).right) ∧
    Equivalent (value (environment m) .actual hiRow.right) (value (environment m) .actual (literal high).right) := by
  obtain ⟨lo,hi⟩ := GeneralDeclarativeRepeatedVisible348.exact_rows m fit
  exact ⟨lower_spelling,upper_spelling,(same_rhs lo m fit).2.2,(same_rhs hi m fit).2.2⟩

end Yulang.GeneralDeclarativeRepeatedSpelling348
