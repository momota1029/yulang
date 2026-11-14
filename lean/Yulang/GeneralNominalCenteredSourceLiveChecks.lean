import Yulang.GeneralNominalCenteredSourceLiveReadbacks
import Yulang.GeneralNominalCenteredInstallCounterexample

/-! The earlier initial inventory loses a future child's source meaning.
The full-frontier initializer has the stronger invariant, while that smaller
inventory cannot satisfy it under any selected trusted ledger. -/
namespace Yulang.GeneralNominalCenteredSourceLiveChecks
open GeneralNominalCenteredInstallExample GeneralNominalCenteredInstallCounterexample
open GeneralNominalCenteredSourceLiveReadbacks GeneralNominalCenteredSourceInvariant

theorem future_child : FutureRead registry root initialState 2 :=
  FutureRead.candidate planP guardP.1 enabledP input_relevant ⟨witness,witness_initial⟩

theorem source_member : 2 ∈ GeneralNominalState.sources context.state :=
  GeneralNominalAllocationSupport.slot_source source (2 : Fin 4)

theorem counterexample_inventory_excluded
    (journal : GeneralNominalCanonicalHoleJournal.Journal context root initialState.erased start.inventory) :
    ¬ Nonempty (Coverage' registry context root initialState start.inventory journal) := by
  rintro ⟨coverage⟩
  have valid := GeneralNominalCenteredSourceTrace.trusted_models (registry := registry) (root := root)
    B4Target.Steps.refl coverage.centeredTrusted witness_initial
  apply GeneralNominalCenteredOriginSeparation.no_value_of_heads valid missing_leaf missing_head
  exact ⟨coverage.retention.value 2 source_member future_child,
    coverage.retention.vocabulary 2 source_member future_child⟩

theorem old_job_excluded :
    ¬ Nonempty (Coverage' registry context root job.state job.inventory job.journal) :=
  counterexample_inventory_excluded job.journal

theorem full_frontier_initialized :
    ∃ inventory : GeneralNominalHoleElimination.Inventory,
      inventory.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length ∧
      GeneralNominalHoleElimination.Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory ∧
      ∃ journal : GeneralNominalCanonicalHoleJournal.Journal context root initialState.erased inventory,
        Nonempty (Coverage' registry context root initialState inventory journal) :=
  initialized initial_source point

end Yulang.GeneralNominalCenteredSourceLiveChecks
