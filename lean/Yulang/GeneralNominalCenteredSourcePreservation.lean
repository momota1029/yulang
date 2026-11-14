import Yulang.GeneralNominalCenteredSourceInvariant

/-! Every non-installation constructor retains the concrete coverage invariant.
Terminal installation also retains it, since it emits no child site. -/
namespace Yulang.GeneralNominalCenteredSourcePreservation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination
open GeneralNominalCenteredSourceInvariant

variable {roles : Roles.RoleDecls} {root : Occurrence roles}

def Retained (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (before after : State roles) (inventory : Inventory)
    (journal : Journal context root before.erased inventory) : Prop :=
  ∃ next : Journal context root after.erased inventory,
    next.labels = journal.labels ∧ Nonempty (Coverage registry context root after inventory next)

theorem administrative (coverage : Coverage registry context root state inventory journal)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root focus)
    (action : GeneralNominalSharedSteps.Administrative registry state.erased.current focus after) :
    Retained registry context root state (GeneralNominalCenteredSteps.administrative state after) inventory journal := by
  let next : Journal context root (GeneralNominalCenteredSteps.administrative state after).erased inventory :=
    journal.administrative action
  exact ⟨next,rfl,⟨coverage.transport ⟨focus,generated,.administrative focus after action⟩
    (fun _ member => member) next rfl⟩⟩

theorem refresh (coverage : Coverage registry context root state inventory journal)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root focus)
    (certificate : Refresh state after) (source : Nat)
    (member : source ∈ GeneralNominalState.sources state.erased.current.context.state)
    (unknown : ¬ GeneralNominalState.Known state.erased.current.context.state source)
    (known : GeneralNominalState.Known after.state source) :
    Retained registry context root state (GeneralNominalCenteredSteps.refresh state after) inventory journal := by
  let next : Journal context root (GeneralNominalCenteredSteps.refresh state after).erased inventory :=
    journal.retain (fun _ member => member)
  exact ⟨next,rfl,⟨coverage.transport ⟨focus,generated,.refresh focus after certificate source member unknown known⟩
    (fun _ member => member) next rfl⟩⟩

theorem merge (coverage : Coverage registry context root state inventory journal)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root first.occurrence)
    (one : first ∈ state.sites) (two : last ∈ state.sites)
    (same : SameInputs (Models state) first last)
    (novel : ¬ GeneralNominalSaturationState.Alias state.erased.current first.occurrence.identity last.occurrence.identity)
    (guard : GeneralNominalSupportChoices.MergeGuard state.erased first.observed last.observed support) :
    Retained registry context root state (GeneralNominalCenteredSteps.merge state first last support) inventory journal := by
  let next : Journal context root (GeneralNominalCenteredSteps.merge state first last support).erased inventory :=
    journal.retain (fun _ member => member)
  exact ⟨next,rfl,⟨coverage.transport
    ⟨first.occurrence,generated,.merge first last support one two same novel guard⟩
    (fun _ member => member) next rfl⟩⟩

theorem terminal_install (coverage : Coverage registry context root state inventory journal)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root plan.packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet)
    (guard : PacketGuard state plan support) (terminal : plan.packet.declaration.requirements = []) :
    Retained registry context root state (install state plan support) inventory journal := by
  let next : Journal context root (install state plan support).erased inventory :=
    journal.install plan.packet support (fun nonempty => False.elim (nonempty terminal))
  have emitted : plan.emitted = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [Plan.emitted,List.length_map,List.length_attach,terminal,List.length_nil]
  have sites : (install state plan support).sites ⊆ state.sites := by
    intro site member
    change site ∈ state.sites ++ plan.emitted at member
    simpa only [emitted,List.append_nil] using member
  exact ⟨next,rfl,⟨coverage.transport ⟨plan.packet.site.occurrence,generated,.install plan support enabled novel guard⟩
    sites next rfl⟩⟩

theorem retained_next (retained : Retained registry context root before after inventory journal) :
    ∃ updated growth count, Trace (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry))
      growth inventory updated count ∧
      ∃ next : Journal context root after.erased updated, Nonempty (Coverage registry context root after updated next) := by
  obtain ⟨next,same,coverage⟩ := retained
  exact ⟨inventory,(fun _ => 0),0,.refl _,next,coverage⟩

end Yulang.GeneralNominalCenteredSourcePreservation
