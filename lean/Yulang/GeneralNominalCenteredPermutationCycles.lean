import Yulang.GeneralNominalCenteredPermutationContext

set_option backward.isDefEq.respectTransparency false

/-! Metadata enumeration preserves the slot graph and the local cycle tests. -/
namespace Yulang.GeneralNominalCenteredPermutationCycles
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralNominalMetadataEquivalence (replace)

variable (state : GeneralNominalState.State)
variable (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)

theorem mixed_path (a b : Fin state.base.slots) :
    GeneralNominalMixedRecurrence.Path (replace state allocated reserved) a b ↔
      GeneralNominalMixedRecurrence.Path state a b := by
  constructor
  · intro path
    exact GeneralNominalMixedRecurrence.Path.rec (state := replace state allocated reserved) (motive := fun a b _ => GeneralNominalMixedRecurrence.Path state a b)
      (fun _ => .nil _) (fun edge _ ih => .cons edge ih) path
  · intro path
    exact GeneralNominalMixedRecurrence.Path.rec (state := state) (motive := fun a b _ => GeneralNominalMixedRecurrence.Path (replace state allocated reserved) a b)
      (fun _ => .nil _) (fun edge _ ih => .cons edge ih) path

theorem mixed_cycle (root : Fin state.base.slots) :
    GeneralNominalMixedRecurrence.Cycle (replace state allocated reserved) root ↔
      GeneralNominalMixedRecurrence.Cycle state root := by
  simp only [GeneralNominalMixedRecurrence.Cycle,mixed_path]
  rfl

theorem mixed_recurs (root : Fin state.base.slots) :
    GeneralNominalMixedRecurrence.RecursAt (replace state allocated reserved) root ↔
      GeneralNominalMixedRecurrence.RecursAt state root := by
  simp only [GeneralNominalMixedRecurrence.RecursAt,mixed_cycle]
  rfl

theorem direct_path (a b : Fin state.base.slots) :
    GeneralNominalCycleK2.DirectPath (replace state allocated reserved) a b ↔
      GeneralNominalCycleK2.DirectPath state a b := by
  constructor
  · intro path
    exact GeneralNominalCycleK2.DirectPath.rec (state := replace state allocated reserved) (motive := fun a b _ => GeneralNominalCycleK2.DirectPath state a b)
      (fun _ => .nil _) (fun edge _ ih => .cons edge ih) path
  · intro path
    exact GeneralNominalCycleK2.DirectPath.rec (state := state) (motive := fun a b _ => GeneralNominalCycleK2.DirectPath (replace state allocated reserved) a b)
      (fun _ => .nil _) (fun edge _ ih => .cons edge ih) path

theorem direct_cycle (root : Fin state.base.slots) :
    GeneralNominalCycleK2.DirectCycle (replace state allocated reserved) root ↔
      GeneralNominalCycleK2.DirectCycle state root := by
  simp only [GeneralNominalCycleK2.DirectCycle,direct_path]
  rfl

theorem recurs (root : Fin state.base.slots) :
    GeneralNominalCycleK2.RecursAt (replace state allocated reserved) root ↔
      GeneralNominalCycleK2.RecursAt state root := by
  simp only [GeneralNominalCycleK2.RecursAt,direct_cycle,mixed_cycle]
  rfl

variable {roles : Roles.RoleDecls}
variable (same : GeneralNominalMetadataEquivalence.Same state (replace state allocated reserved))
include same

theorem mixed_root (demand : GeneralSourceState.Demand roles) :
    GeneralNominalMixedRecurrence.RootK2 (replace state allocated reserved) demand ↔
      GeneralNominalMixedRecurrence.RootK2 state demand := by
  simp only [GeneralNominalMixedRecurrence.RootK2,mixed_recurs,
    ← GeneralNominalMetadataEquivalence.linked same]
  rfl

theorem root (demand : GeneralSourceState.Demand roles) :
    GeneralNominalCycleK2.RootK2 (replace state allocated reserved) demand ↔
      GeneralNominalCycleK2.RootK2 state demand := by
  simp only [GeneralNominalCycleK2.RootK2,recurs,
    ← GeneralNominalMetadataEquivalence.linked same]
  rfl

omit same
variable (old : Context)
variable (sameContext : GeneralNominalMetadataEquivalence.Same old.state (replace old.state allocated reserved))
include sameContext
open GeneralNominalCenteredPermutationContext (context)

theorem recursive_candidate (registry) (root : Occurrence roles) :
    GeneralNominalRecursiveCandidates.CandidateK2 registry (context old allocated reserved) root ↔
      GeneralNominalRecursiveCandidates.CandidateK2 registry old root := by
  simp only [GeneralNominalRecursiveCandidates.CandidateK2,
    GeneralNominalCenteredPermutationContext.head_ready old allocated reserved sameContext,
    GeneralNominalCenteredPermutationContext.report]
  simp only [context,GeneralNominalReportMetadata.report,mixed_recurs]
  rfl

theorem candidate (registry) (root : Occurrence roles) :
    GeneralNominalCycleK2.CandidateK2 registry (context old allocated reserved) root ↔
      GeneralNominalCycleK2.CandidateK2 registry old root := by
  simp only [GeneralNominalCycleK2.CandidateK2,
    GeneralNominalCenteredPermutationContext.head_ready old allocated reserved sameContext,
    GeneralNominalCenteredPermutationContext.report]
  simp only [context,GeneralNominalReportMetadata.report,recurs]
  rfl

theorem inspection_pending (registry) (root : Occurrence roles) :
    GeneralNominalCycleK2.InspectionPending registry (context old allocated reserved) root ↔
      GeneralNominalCycleK2.InspectionPending registry old root := by
  have one := mixed_root old.state allocated reserved sameContext root.demand
  have two := GeneralNominalCenteredPermutationCycles.root old.state allocated reserved sameContext root.demand
  simp only [GeneralNominalCycleK2.InspectionPending,
    GeneralNominalCenteredPermutationContext.inspection_pending old allocated reserved sameContext,
    recursive_candidate allocated reserved old sameContext,candidate allocated reserved old sameContext]
  change (_ ∨ (¬ GeneralNominalState.RootPending old.state root.demand ∧
    ((GeneralNominalMixedRecurrence.RootK2 (replace old.state allocated reserved) root.demand ∧
        ¬ GeneralNominalCycleK2.RootK2 (replace old.state allocated reserved) root.demand) ∨ _))) ↔ _
  rw [one,two]

end Yulang.GeneralNominalCenteredPermutationCycles
