import Yulang.GeneralNominalCenteredHolePhases
import Yulang.GeneralNominalCenteredIdentityJournal

/-! The journal simulation reduction for the full centered relation.
Its source transition field is explicit and independent of raw compatibility. -/
namespace Yulang.GeneralNominalCenteredJournalSimulation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalHoleElimination GeneralNominalCanonicalHoleJournal

variable {roles : Roles.RoleDecls}

structure Simulation (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles) where
  keys : List Nat
  start : Inventory
  holes : start.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length
  valid : Valid (GeneralNominalSourceLabelVocabulary.tests keys) start
  invariant : (state : State roles) → (inventory : Inventory) → Journal context root state.erased inventory → Prop
  initial : Journal context root (GeneralNominalCenteredSteps.initial context root).erased start
  initialInvariant : invariant _ _ initial
  next : ∀ state, B4Target.Steps (Step registry root) (GeneralNominalCenteredSteps.initial context root) state →
    ∀ inventory, Valid (GeneralNominalSourceLabelVocabulary.tests keys) inventory →
    ∀ journal : Journal context root state.erased inventory, invariant state inventory journal →
    ∀ after, Step registry root state after →
      ∃ updated growth count, Trace (GeneralNominalSourceLabelVocabulary.tests keys) growth inventory updated count ∧
        ∃ journal : Journal context root after.erased updated, invariant after updated journal

def phase_cover (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (simulation : Simulation registry context root) : GeneralNominalCenteredHolePhases.PhaseCover registry context root where
  start := simulation.start
  tests := GeneralNominalSourceLabelVocabulary.tests simulation.keys
  holes := simulation.holes
  valid := simulation.valid
  invariant := fun state inventory => Valid (GeneralNominalSourceLabelVocabulary.tests simulation.keys) inventory ∧
    ∃ journal : Journal context root state.erased inventory, simulation.invariant state inventory journal
  initial := ⟨simulation.valid,simulation.initial,simulation.initialInvariant⟩
  basis := fun inventory => GeneralNominalSnapshotCover.signatures checked source (inventoryMass inventory)
  next := by
    intro state path inventory ⟨valid,journal,invariant⟩ after step
    obtain ⟨updated,growth,count,trace,next⟩ := simulation.next state path inventory valid journal invariant after step
    exact ⟨updated,growth,count,trace,trace_valid trace valid,next⟩
  covers := by
    intro state path inventory ⟨valid,journal,invariant⟩ plan support generated enabled novel guard
    exact GeneralNominalCenteredSnapshot.covers checked source path (GeneralNominalCenteredSnapshot.journal_parents path journal) enabled

theorem accessible (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (simulation : Simulation registry context root) :
    Acc (fun next current => Step registry root current next) (GeneralNominalCenteredSteps.initial context root) :=
  GeneralNominalCenteredHolePhases.accessible (phase_cover checked source simulation)

theorem eliminated_holes (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (simulation : Simulation registry context root)
    (path : B4Target.Steps (Step registry root) (GeneralNominalCenteredSteps.initial context root) state) :
    ∃ inventory count,
      GeneralNominalHolePhases.History (GeneralNominalSourceLabelVocabulary.tests simulation.keys) simulation.start inventory count ∧
      count ≤ simulation.start.holes.length ∧
      ∃ journal : Journal context root state.erased inventory, simulation.invariant state inventory journal := by
  obtain ⟨inventory,count,history,⟨valid,journal,invariant⟩,bounded,_⟩ :=
    GeneralNominalCenteredHolePhases.replay (phase_cover checked source simulation) path
  exact ⟨inventory,count,history,bounded,journal,invariant⟩

def ClassPSourceProduction (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles),
    GeneralNominalSourceFormation.InitialSource registry context root →
    GeneralNominalActualBudget.PointSource context root → Nonempty (Simulation registry context root)

theorem class_p_accessible (production : ClassPSourceProduction roles) (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root) :
    Acc (fun next current => Step registry root current next) (initial context root) := by
  obtain ⟨simulation⟩ := production registry checked context root source point
  exact accessible checked source simulation

end Yulang.GeneralNominalCenteredJournalSimulation
