import Yulang.GeneralNominalCenteredSourceLiveTransport

/-! The source-retention invariant supplies every administrative and terminal
branch. The remaining installation contract quantifies over the strengthened
coverage and feeds the existing centered journal simulation directly. -/
namespace Yulang.GeneralNominalCenteredSourceLiveConstruction
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination GeneralNominalCenteredSourceInvariant
open GeneralNominalCenteredSourceLiveReadbacks GeneralNominalCenteredSourceLiveTransport

variable {roles : Roles.RoleDecls} {root : Occurrence roles}

def NonterminalInstallPreservation' (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ∀ state, B4Target.Steps (Step registry root) (initial context root) state →
    ∀ inventory, Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory →
    ∀ journal : Journal context root state.erased inventory,
    Coverage' registry context root state inventory journal →
    ∀ plan : Plan roles, ∀ support,
      GeneralNominalSaturationState.Generated state.erased.current root plan.packet.site.occurrence →
      GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet →
      ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet →
      PacketGuard state plan support → plan.packet.declaration.requirements ≠ [] →
      ∃ updated growth count, Trace (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry))
        growth inventory updated count ∧
        ∃ next : Journal context root (install state plan support).erased updated,
          Nonempty (Coverage' registry context root (install state plan support) updated next)

theorem retained_next (retained : Retained registry context root before after inventory journal) :
    ∃ updated growth count, Trace (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry))
      growth inventory updated count ∧
      ∃ next : Journal context root after.erased updated,
        Nonempty (Coverage' registry context root after updated next) := by
  obtain ⟨next,_,coverage⟩ := retained
  exact ⟨inventory,(fun _ => 0),0,.refl _,next,coverage⟩

theorem next (produce : NonterminalInstallPreservation' registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (valid : Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory)
    (coverage : Coverage' registry context root state inventory journal)
    (step : Step registry root state after) :
    ∃ updated growth count, Trace (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry))
      growth inventory updated count ∧
      ∃ next : Journal context root after.erased updated,
        Nonempty (Coverage' registry context root after updated next) := by
  classical
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative focus after action => exact retained_next (administrative coverage generated action)
  | refresh focus context certificate source member unknown known =>
    exact retained_next (refresh coverage generated certificate source member unknown known)
  | merge first last support one two same novel guard =>
    exact retained_next (merge coverage generated one two same novel guard)
  | install plan support enabled novel guard =>
    by_cases terminal : plan.packet.declaration.requirements = []
    · exact retained_next (terminal_install coverage generated enabled novel guard terminal)
    · exact produce state path inventory valid journal coverage plan support generated enabled novel guard terminal

theorem simulation
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : GeneralNominalActualBudget.PointSource context root)
    (produce : NonterminalInstallPreservation' registry context root) :
    Nonempty (GeneralNominalCenteredJournalSimulation.Simulation registry context root) := by
  obtain ⟨inventory,holes,valid,journal,coverage⟩ :=
    GeneralNominalCenteredSourceLiveReadbacks.initialized source point
  exact ⟨{
    keys := keyMenu registry
    start := inventory
    holes := holes
    valid := valid
    invariant := fun state inventory journal => Nonempty (Coverage' registry context root state inventory journal)
    initial := journal
    initialInvariant := coverage
    next := by
      intro state path inventory valid journal coverage after step
      obtain ⟨coverage⟩ := coverage
      exact next produce path valid coverage step }⟩

theorem accessible (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : GeneralNominalActualBudget.PointSource context root)
    (produce : NonterminalInstallPreservation' registry context root) :
    Acc (fun next current => Step registry root current next) (initial context root) := by
  obtain ⟨simulation⟩ := simulation source point produce
  exact GeneralNominalCenteredJournalSimulation.accessible checked source simulation

def ClassPInstallPreservation' (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles),
    GeneralNominalSourceFormation.InitialSource registry context root →
    GeneralNominalActualBudget.PointSource context root → NonterminalInstallPreservation' registry context root

theorem class_p_source_production (produce : ClassPInstallPreservation' roles) :
    GeneralNominalCenteredJournalSimulation.ClassPSourceProduction roles := by
  intro registry checked context root source point
  exact simulation source point (produce registry checked context root source point)

end Yulang.GeneralNominalCenteredSourceLiveConstruction
