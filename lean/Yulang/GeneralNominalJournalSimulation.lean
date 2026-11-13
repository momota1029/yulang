import Yulang.GeneralNominalLabelledExposureElimination

/-! A local source simulation over the established nonterminal packet
journal. Terminal packets create no ancestry edge and need no synthetic
head-mass presentation. The source transition construction remains explicit. -/
namespace Yulang.GeneralNominalJournalSimulation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
open GeneralNominalActualInspectionSteps GeneralNominalHoleElimination GeneralNominalCanonicalHoleJournal

variable {roles : Roles.RoleDecls}

structure Simulation (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles) where
  keys : List Nat
  start : Inventory
  holes : start.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length
  valid : Valid (GeneralNominalSourceLabelVocabulary.tests keys) start
  invariant : (state : Tracked roles) → (inventory : Inventory) → Journal context root state inventory → Prop
  initial : Journal context root (GeneralNominalSupport.initial context root) start
  initialInvariant : invariant _ _ initial
  next : ∀ state, B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state →
    ∀ inventory, Valid (GeneralNominalSourceLabelVocabulary.tests keys) inventory →
    ∀ journal : Journal context root state inventory, invariant state inventory journal →
    ∀ after, Step registry root state after →
      ∃ updated growth count, Trace (GeneralNominalSourceLabelVocabulary.tests keys) growth inventory updated count ∧
        ∃ journal : Journal context root after updated, invariant after updated journal

def phase_cover (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (simulation : Simulation registry context root) : GeneralNominalHolePhases.PhaseCover registry context root where
  start := simulation.start
  tests := GeneralNominalSourceLabelVocabulary.tests simulation.keys
  holes := simulation.holes
  valid := simulation.valid
  invariant := fun state inventory => Valid (GeneralNominalSourceLabelVocabulary.tests simulation.keys) inventory ∧
    ∃ journal : Journal context root state inventory, simulation.invariant state inventory journal
  initial := ⟨simulation.valid,simulation.initial,simulation.initialInvariant⟩
  basis := fun inventory => GeneralNominalSnapshotCover.signatures checked source (inventoryMass inventory)
  next := by
    intro state path inventory ⟨valid,journal,invariant⟩ after step
    obtain ⟨updated,growth,count,trace,next⟩ := simulation.next state path inventory valid journal invariant after step
    exact ⟨updated,growth,count,trace,trace_valid trace valid,next⟩
  covers := by
    intro state path inventory ⟨valid,journal,invariant⟩ packet support generated enabled novel guard
    exact GeneralNominalSnapshotCover.covers checked source path (journal_parents source path journal) enabled

theorem accessible (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (simulation : Simulation registry context root) :
    Acc (fun next current => Step registry root current next) (GeneralNominalSupport.initial context root) :=
  GeneralNominalHolePhases.accessible (phase_cover checked source simulation) source

theorem eliminated_holes (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (simulation : Simulation registry context root)
    (path : B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state) :
    ∃ inventory count,
      GeneralNominalHolePhases.History (GeneralNominalSourceLabelVocabulary.tests simulation.keys) simulation.start inventory count ∧
      count ≤ simulation.start.holes.length ∧
      ∃ journal : Journal context root state inventory, simulation.invariant state inventory journal := by
  obtain ⟨inventory,count,history,⟨valid,journal,invariant⟩,bounded,_⟩ :=
    GeneralNominalHolePhases.replay (phase_cover checked source simulation) path
  exact ⟨inventory,count,history,bounded,journal,invariant⟩

end Yulang.GeneralNominalJournalSimulation
