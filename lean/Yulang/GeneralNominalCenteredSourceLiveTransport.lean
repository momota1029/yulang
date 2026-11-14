import Yulang.GeneralNominalCenteredSourceLiveReadbacks

/-! Every centered transition transports retained source meanings. Global
replacement uses the centered ledger; its auxiliary raw selection can be empty
while all selected centered facts and historical labels are retained. -/
namespace Yulang.GeneralNominalCenteredSourceLiveTransport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination GeneralNominalCenteredSourceInvariant
open GeneralNominalCenteredSourceLiveReadbacks GeneralNominalLabelledOriginClosure
open GeneralNominalScopedRecipeLabels GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalCaptureRefinement (Operation)

variable {roles : Roles.RoleDecls} {root : Occurrence roles}
variable {registry : Registry} {context : GeneralNominalCandidates.Context}

def Coverage'.transport (coverage : Coverage' registry context root before inventory journal)
    (step : Step registry root before after) (sites : after.sites ⊆ before.sites)
    (next : Journal context root after.erased inventory) (same : next.labels = journal.labels) :
    Coverage' registry context root after inventory next :=
  ⟨coverage.toCoverage.transport step sites next same,coverage.retention.step step⟩

def Retained (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (before after : State roles) (inventory : Inventory)
    (journal : Journal context root before.erased inventory) : Prop :=
  ∃ next : Journal context root after.erased inventory,
    next.labels = journal.labels ∧ Nonempty (Coverage' registry context root after inventory next)

theorem administrative (coverage : Coverage' registry context root state inventory journal)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root focus)
    (action : GeneralNominalSharedSteps.Administrative registry state.erased.current focus after) :
    Retained registry context root state (GeneralNominalCenteredSteps.administrative state after) inventory journal := by
  let next : Journal context root (GeneralNominalCenteredSteps.administrative state after).erased inventory :=
    journal.administrative action
  exact ⟨next,rfl,⟨Coverage'.transport coverage ⟨focus,generated,.administrative focus after action⟩
    (fun _ member => member) next rfl⟩⟩

theorem refresh (coverage : Coverage' registry context root state inventory journal)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root focus)
    (certificate : Refresh state after) (source : Nat)
    (member : source ∈ GeneralNominalState.sources state.erased.current.context.state)
    (unknown : ¬ GeneralNominalState.Known state.erased.current.context.state source)
    (known : GeneralNominalState.Known after.state source) :
    Retained registry context root state (GeneralNominalCenteredSteps.refresh state after) inventory journal := by
  let next : Journal context root (GeneralNominalCenteredSteps.refresh state after).erased inventory :=
    journal.retain (fun _ member => member)
  exact ⟨next,rfl,⟨Coverage'.transport coverage ⟨focus,generated,.refresh focus after certificate source member unknown known⟩
    (fun _ member => member) next rfl⟩⟩

theorem merge (coverage : Coverage' registry context root state inventory journal)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root first.occurrence)
    (one : first ∈ state.sites) (two : last ∈ state.sites)
    (same : SameInputs (Models state) first last)
    (novel : ¬ GeneralNominalSaturationState.Alias state.erased.current first.occurrence.identity last.occurrence.identity)
    (guard : GeneralNominalSupportChoices.MergeGuard state.erased first.observed last.observed support) :
    Retained registry context root state (GeneralNominalCenteredSteps.merge state first last support) inventory journal := by
  let next : Journal context root (GeneralNominalCenteredSteps.merge state first last support).erased inventory :=
    journal.retain (fun _ member => member)
  exact ⟨next,rfl,⟨Coverage'.transport coverage
    ⟨first.occurrence,generated,.merge first last support one two same novel guard⟩
    (fun _ member => member) next rfl⟩⟩

theorem terminal_install (coverage : Coverage' registry context root state inventory journal)
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
  exact ⟨next,rfl,⟨Coverage'.transport coverage ⟨plan.packet.site.occurrence,generated,.install plan support enabled novel guard⟩
    sites next rfl⟩⟩

def Coverage'.replace (coverage : Coverage' registry context root state inventory journal)
    (replacement : Value (GeneralNominalCenteredSupport.Models state.erased state.sourceSites coverage.centeredFacts)
      context (origins context) (inventory.holes.erase hole) (keyMenu registry) (origins context hole))
    (vocabulary : Vocabulary (testMenu context registry) replacement.term) (extra : Nat) :
    Coverage' registry context root state
      (eliminate inventory hole (GeneralNominalPatternInventory.encode replacement.pattern) extra)
      (journal.replace replacement.labelled.1 hole extra) where
  identity := GeneralNominalIdentityJournal.identity_substitute coverage.identity _
  rawFacts := []
  rawReadbacks := []
  rawTrusted := .source
  rawInputs := by intro origin member; cases member
  centeredFacts := coverage.centeredFacts
  centeredTrusted := coverage.centeredTrusted
  legacyIncluded := by intro fact member; cases member
  sites := fun site member => GeneralNominalCenteredCoverageReplacement.site_values (coverage.sites site member)
    replacement vocabulary
  inputs := GeneralNominalCenteredCoverageReplacement.origin_values coverage.inputs replacement vocabulary
  binders := GeneralNominalCenteredCoverageReplacement.origin_values coverage.binders replacement vocabulary
  retention := coverage.retention.replace replacement vocabulary

theorem eliminate (coverage : Coverage' registry context root state inventory journal)
    (valid : Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory)
    (present : hole ∈ inventory.holes)
    (replacement : Value (GeneralNominalCenteredSupport.Models state.erased state.sourceSites coverage.centeredFacts)
      context (origins context) (inventory.holes.erase hole) (keyMenu registry) (origins context hole))
    (vocabulary : Vocabulary (testMenu context registry) replacement.term) :
    ∃ updated growth, Trace (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) growth inventory updated 1 ∧
      Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) updated ∧
      ∃ next : Journal context root state.erased updated,
        ∃ result : Coverage' registry context root state updated next, ¬ result.retention.Live hole := by
  obtain ⟨extra,bounded⟩ := GeneralNominalSourceLabelVocabulary.encoded_bounded replacement.pattern
    replacement.allowed.1 replacement.allowed.2
  have trace := replacement_trace inventory present (GeneralNominalSourceLabelVocabulary.bounded_closed bounded) bounded
  exact ⟨_,_,trace,trace_valid trace valid,journal.replace replacement.labelled.1 hole extra,
    Coverage'.replace coverage replacement vocabulary extra,
    coverage.retention.eliminated_not_live replacement vocabulary valid.1⟩

inductive Replacements (models : GeneralNominalCommonBridge.Assignment → Prop)
    (context : GeneralNominalCandidates.Context) (keys : List Nat) (tests : List Test) :
    Inventory → Inventory → List Operation → Prop
  | refl (inventory) : Replacements models context keys tests inventory inventory []
  | next (op : Operation) (present : op.hole ∈ before.holes)
      (label : GeneralNominalOpenPatternLabels.Label context op.pattern op.tree)
      (readback : GeneralNominalIndexedHoleReadback.Readback models (origins context)
        (before.holes.erase op.hole) (origins context op.hole) op.tree)
      (allowed : GeneralNominalSourceLabelVocabulary.Allowed keys (before.holes.erase op.hole) op.pattern)
      (vocabulary : Vocabulary tests op.tree)
      (bounded : GeneralNominalSharedEnumeration.Bounded (before.holes.erase op.hole)
        (GeneralNominalSourceLabelVocabulary.tests keys) op.extra (GeneralNominalPatternInventory.encode op.pattern))
      (positive : 0 < op.extra)
      (rest : Replacements models context keys tests (op.updated before) after operations) :
      Replacements models context keys tests before after (op :: operations)

theorem Replacements.changes (replacements : Replacements models context keys tests before after operations) :
    GeneralNominalCenteredInstallObligations.Changes context keys before after operations := by
  induction replacements with
  | refl => exact .refl _
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    exact .next op present label bounded positive ih

theorem Replacements.transport
    (coverage : Coverage' registry context root state before journal)
    (replacements : Replacements
      (GeneralNominalCenteredSupport.Models state.erased state.sourceSites coverage.centeredFacts)
      context (keyMenu registry) (testMenu context registry) before after operations) :
    ∃ next : Journal context root state.erased after,
      next.labels = GeneralNominalCaptureFamilies.transformLabels operations journal.labels ∧
      Nonempty (Coverage' registry context root state after next) := by
  generalize facts : coverage.centeredFacts = selected at replacements
  induction replacements with
  | refl => exact ⟨journal,rfl,⟨coverage⟩⟩
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    have raw := readback
    rw [← facts] at raw
    exact ih (Coverage'.replace coverage ⟨op.pattern,op.tree,⟨label,raw⟩,allowed⟩ vocabulary op.extra) facts

end Yulang.GeneralNominalCenteredSourceLiveTransport

