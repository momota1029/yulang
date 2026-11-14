import Yulang.GeneralNominalCenteredSourceInvariant

/-! A global replacement preserves every site and selected trusted origin.
Each coarse ledger keeps its own readback obligation; actual-state validity
alone is not used to rewrite a value under a broader model predicate. -/
namespace Yulang.GeneralNominalCenteredCoverageReplacement
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalHoleElimination
open GeneralNominalLabelledOriginClosure GeneralNominalScopedRecipeLabels
open GeneralNominalIndexedHoleReadback GeneralNominalCanonicalHoleJournal
open GeneralNominalCanonicalPacketTransport GeneralNominalCenteredSourceInvariant
open GeneralNominalLabelledExposureElimination

variable {roles : Roles.RoleDecls} {root : Occurrence roles}
variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {remaining keys : List Nat} {tests : List Test}

theorem site_values (known : SiteValues models context remaining keys tests labels site)
    (replacement : Value models context (origins context) (remaining.erase hole) keys (origins context hole))
    (vocabulary : Vocabulary tests replacement.term) :
    SiteValues models context (remaining.erase hole) keys tests
      (substituteLabels labels (patternReplacement hole replacement.pattern)) site := by
  obtain ⟨values,equal,vocab⟩ := known
  refine ⟨fun position => GeneralNominalLabelledExposureElimination.Value.replace (values position) replacement,?_,?_⟩
  · change normalizeArgs (substArgs (patternReplacement hole replacement.pattern) (labels site.occurrence)) = _
    rw [equal]
    simp only [GeneralNominalChildAssembly.substitute_map,GeneralNominalChildAssembly.normalize_map,
      List.map_ofFn]
    rfl
  · intro position
    exact GeneralNominalCaptureRefinement.replacement_vocabulary (vocab position) vocabulary

theorem origin_values (known : OriginValues models context remaining keys tests relevant)
    (replacement : Value models context (origins context) (remaining.erase hole) keys (origins context hole))
    (vocabulary : Vocabulary tests replacement.term) :
    OriginValues models context (remaining.erase hole) keys tests relevant := by
  intro origin member
  obtain ⟨value,vocab⟩ := known origin member
  exact ⟨GeneralNominalLabelledExposureElimination.Value.replace value replacement,
    GeneralNominalCaptureRefinement.replacement_vocabulary vocab vocabulary⟩

def replace (coverage : Coverage registry context root state inventory journal)
    (label : GeneralNominalOpenPatternLabels.Label context pattern term)
    (allowed : GeneralNominalSourceLabelVocabulary.Allowed (keyMenu registry) (inventory.holes.erase hole) pattern)
    (vocabulary : Vocabulary (testMenu context registry) term)
    (raw : Readback (GeneralNominalSharedSupport.Models state.erased coverage.rawFacts)
      (origins context) (inventory.holes.erase hole) (origins context hole) term)
    (centered : Readback (GeneralNominalCenteredSupport.Models state.erased state.sourceSites coverage.centeredFacts)
      (origins context) (inventory.holes.erase hole) (origins context hole) term)
    (extra : Nat) :
    Coverage registry context root state
      (eliminate inventory hole (GeneralNominalPatternInventory.encode pattern) extra)
      (journal.replace label hole extra) where
  identity := GeneralNominalIdentityJournal.identity_substitute coverage.identity _
  rawFacts := coverage.rawFacts
  rawReadbacks := coverage.rawReadbacks
  rawTrusted := coverage.rawTrusted
  rawInputs := GeneralNominalCommonTrustedLedger.inputs_replace coverage.rawInputs
    ⟨pattern,term,⟨label,raw⟩,allowed⟩ vocabulary
  centeredFacts := coverage.centeredFacts
  centeredTrusted := coverage.centeredTrusted
  legacyIncluded := coverage.legacyIncluded
  sites := fun site member => site_values (coverage.sites site member)
    ⟨pattern,term,⟨label,centered⟩,allowed⟩ vocabulary
  inputs := origin_values coverage.inputs ⟨pattern,term,⟨label,centered⟩,allowed⟩ vocabulary
  binders := origin_values coverage.binders ⟨pattern,term,⟨label,centered⟩,allowed⟩ vocabulary

theorem raw_models (coverage : Coverage registry context root state inventory journal)
    (valid : GeneralNominalCenteredSupport.Models state.erased state.sourceSites coverage.centeredFacts model) :
    GeneralNominalSharedSupport.Models state.erased coverage.rawFacts model :=
  ⟨valid.1,fun fact member => valid.2.2 (.legacy fact) (coverage.legacyIncluded fact member)⟩

theorem eliminate (coverage : Coverage registry context root state inventory journal)
    (valid : Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory)
    (present : hole ∈ inventory.holes)
    (replacement : Value (GeneralNominalSharedSupport.Models state.erased coverage.rawFacts)
      context (origins context) (inventory.holes.erase hole) (keyMenu registry) (origins context hole))
    (vocabulary : Vocabulary (testMenu context registry) replacement.term) :
    ∃ updated growth, Trace (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) growth inventory updated 1 ∧
      Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) updated ∧
      ∃ next : Journal context root state.erased updated,
        next.labels = substituteLabels journal.labels (patternReplacement hole replacement.pattern) ∧
        Nonempty (Coverage registry context root state updated next) := by
  obtain ⟨extra,bounded⟩ := GeneralNominalSourceLabelVocabulary.encoded_bounded replacement.pattern
    replacement.allowed.1 replacement.allowed.2
  have trace := replacement_trace inventory present (GeneralNominalSourceLabelVocabulary.bounded_closed bounded) bounded
  refine ⟨_,_,trace,trace_valid trace valid,journal.replace replacement.labelled.1 hole extra,rfl,?_⟩
  exact ⟨replace coverage replacement.labelled.1 replacement.allowed vocabulary replacement.labelled.2
    (GeneralNominalIndexedHoleReadback.restrict replacement.labelled.2 (fun _ valid => raw_models coverage valid)) extra⟩

end Yulang.GeneralNominalCenteredCoverageReplacement
