import Yulang.GeneralDictionaryCommittedEvidence
import Yulang.B4SkeletonV4

/-! The faithful thirteen-field saturation boundary, with no strengthened
stability predicate. Its conditional evidence and generation bridges expose
the journal feedback and alias agreement still required by installation. -/
namespace Yulang.GeneralDictionarySaturationBoundary

open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSaturationSteps
open GeneralDictionaryCommittedEvidence

/-- Existing saturation fields and source evidence, on exactly Astra's carrier. -/
def boundary (roles : Roles.RoleDecls) :
    B4Target.SourceBoundary (GeneralNominalSaturationBoundary.vocabulary roles) :=
  GeneralNominalLocalBoundary.complete (GeneralNominalSaturationBoundary.localFields roles)
    { Step := Step
      Stable := Stable
      Generated := fun _ state => Generated state
      Evidence := fun registry state => GeneralDictionaryRecursiveEvidence.Evidence registry state.context }

/-- The actual no-step closure field, with no additional journal invariant. -/
theorem closure (roles : Roles.RoleDecls) :
    ∀ registry, (boundary roles).Checked registry → ∀ state root,
      (∀ next, ¬ (boundary roles).Step registry root state next) →
      (boundary roles).Stable registry state root ∧
        ∀ child, (boundary roles).Generated registry state root child →
          (boundary roles).Stable registry state child := by
  intro registry _ state root halted
  exact halted_closure halted

/-- Journal model preservation is instantiated on the concrete boundary. -/
theorem stepModels (roles : Roles.RoleDecls) :
    ∀ registry, (boundary roles).Checked registry → ∀ root before after,
      (boundary roles).Step registry root before after →
      ∀ model, (boundary roles).Models after model → (boundary roles).Models before model := by
  intro registry _ root before after update model valid
  exact step_models update model valid

/-- The dictionary comparison field has unconditional reflexivity. -/
theorem dictionaryRefl (roles : Roles.RoleDecls) :
    ∀ dictionary, (boundary roles).DictionaryEquivalent dictionary dictionary :=
  GeneralDictionaryPayloadOrder.equivalent_refl

/-- Remaining source invariants at stable selections. This is an explicit
unproved obligation on the frozen arbitrary-State carrier, not a new definition
of Stable and not a completed field of the concrete B4 bridge package. -/
def SelectedJournalInvariants (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root key children,
    Stable registry state root →
    GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles)
      registry state.context root (.selected key children) →
    ContextComplete state ∧ AliasChoiceAgreement state root key

/-- No extra model premise beyond the final state's own Models predicate. The
explicit journal obligation, not the existential candidate witness, is used. -/
theorem evidenceNode_of_journal_invariants (roles : Roles.RoleDecls)
    (invariants : SelectedJournalInvariants roles) : B4SkeletonV4.EvidenceNode (boundary roles) := by
  intro registry checked state model valid root key children dictionaries stable _ safe unique given
  have selected : GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles)
      registry state.context root (.selected key children) := .selected safe unique
  obtain ⟨complete,agreement⟩ := invariants registry checked state root key children stable selected
  exact stable_selected_evidence registry state root key children stable complete agreement selected model valid dictionaries given

/-- Recorded edges supply the extra V4 generation bridge under precisely the
same journal obligation as the node theorem. -/
theorem generatedChildren_of_journal_invariants (roles : Roles.RoleDecls)
    (invariants : SelectedJournalInvariants roles) : B4SkeletonV4.GeneratedChildren (boundary roles) := by
  apply B4SkeletonV4.generatedChildren_of_direct_transitive
  · intro registry checked state root key children stable safe unique child member
    have selected : GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles)
        registry state.context root (.selected key children) := .selected safe unique
    obtain ⟨complete,agreement⟩ := invariants registry checked state root key children stable selected
    exact (stable_selected_instance registry state root key children stable complete agreement selected).2 child member
  · intro _ _ _ _ _ _ first last
    exact generated_trans first last

/-- Assemble both conditional fields together; the hypothesis remains visible. -/
theorem evidence_and_generation_of_journal_invariants (roles : Roles.RoleDecls)
    (invariants : SelectedJournalInvariants roles) :
    B4SkeletonV4.EvidenceNode (boundary roles) ∧ B4SkeletonV4.GeneratedChildren (boundary roles) :=
  ⟨evidenceNode_of_journal_invariants roles invariants,
    generatedChildren_of_journal_invariants roles invariants⟩

end Yulang.GeneralDictionarySaturationBoundary
