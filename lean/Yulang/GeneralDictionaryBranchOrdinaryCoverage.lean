import Yulang.GeneralDictionarySpineCoverage
import Yulang.GeneralDictionarySupportOrdinaryExecution

/-! Same-model recursive dictionaries along actual ordinary support histories.
Unlike all-recorded coverage, this criterion admits unrecorded structural leaves.
Historical context growth is derived from the trace, not a per-packet premise. -/
namespace Yulang.GeneralDictionaryBranchOrdinaryCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalSupportBoundary
open GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls}

/-- A structural alternative at each generated selected focus. The recorded
alternative asks only for an actual packet at the occurrence, not its key,
Instance, BranchModels, or context Extension. -/
def Covered (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.current root focus → ∀ key children,
    GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
    (∃ packet ∈ state.current.packets, packet.site.occurrence = focus) ∨
    GeneralDictionarySpineLeaf.HasSpineLeaf registry state.current.context focus ∨
    GeneralDictionaryScalarLeaf.HasScalarLeaf registry state.current.context focus

/-- Every finite actual ordinary history starting at the empty journal supplies
all the historical context transport needed by structural dictionary coverage. -/
theorem coverage_from_trace (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (covered : Covered registry state root) :
    GeneralDictionarySpineCoverage.Covered registry state root := by
  intro focus reached key children selected
  rcases covered focus reached key children selected with recorded | spine | scalar
  · obtain ⟨packet,member,same⟩ := recorded
    exact Or.inl ⟨packet,member,
      GeneralDictionarySupportOrdinaryExecution.initial_packets_extension
        registry root context state path packet member,same⟩
  · exact Or.inr (Or.inl spine)
  · exact Or.inr (Or.inr scalar)

/-- No bound on history length or dictionary depth. Both recorded nonterminal
nodes and unrecorded structural terminal leaves may occur in the same tree.
The finite Classify derivation and residual structural coverage remain explicit. -/
theorem dictionary_evidence (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (covered : Covered registry state root)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  GeneralDictionarySpineCoverage.dictionary_evidence registry root state
    (GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) path)
    (coverage_from_trace registry root context state path covered) model valid dictionary root .root derived

/-- Existing structural certificates can forget their context-growth field.
This implication alone does not establish coverage for arbitrary states. -/
theorem forget_growth (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (covered : GeneralDictionarySpineCoverage.Covered registry state root) :
    Covered registry state root := by
  intro focus reached key children selected
  rcases covered focus reached key children selected with recorded | spine | scalar
  · obtain ⟨packet,member,_,same⟩ := recorded
    exact Or.inl ⟨packet,member,same⟩
  · exact Or.inr (Or.inl spine)
  · exact Or.inr (Or.inr scalar)

/-- On actual ordinary initial histories the strengthened and reduced coverage
criteria coincide: context growth costs no extra proof assumption. -/
theorem covered_iff (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state) :
    Covered registry state root ↔ GeneralDictionarySpineCoverage.Covered registry state root :=
  ⟨coverage_from_trace registry root context state path,forget_growth registry root state⟩

/-- Concrete nonvacuous use with a recorded parent and unrecorded scalar child. -/
theorem recursive_fixture (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models GeneralDictionarySupportRecursiveExample.finish.current model) :
    Evidence GeneralNominalExamples.registry GeneralDictionarySupportRecursiveExample.finish.current.context model
      GeneralNominalExamples.displayRoot (.node 1 [.node 3 []]) := by
  apply dictionary_evidence GeneralNominalExamples.registry GeneralNominalExamples.displayRoot
    (GeneralNominalExamples.context true) GeneralDictionarySupportRecursiveExample.initial_source
    GeneralDictionarySupportRecursiveExample.finish GeneralDictionaryRecordedCoverageLimit.ordinary_trace
    (forget_growth _ _ _ (GeneralDictionarySpineCoverage.of_mixed _ _ _ GeneralDictionaryMixedCoverageExample.covered)) model valid
  exact GeneralDictionarySupportRecursiveClassification.classified
end Yulang.GeneralDictionaryBranchOrdinaryCoverage
