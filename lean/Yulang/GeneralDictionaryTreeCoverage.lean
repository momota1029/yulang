import Yulang.GeneralDictionaryBranchCoverage
import Yulang.GeneralDictionaryCoveredEvidence
import Yulang.GeneralDictionaryScalarLeaf
import Yulang.GeneralDictionaryTreeLeaf
import Yulang.GeneralDictionaryMixedCoverageExample

/-! Recursive dictionary evidence for structurally journal-covered focuses.
Coverage is explicit and is not inferred from unrestricted support stability. -/
namespace Yulang.GeneralDictionaryTreeCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalSupportBoundary
open GeneralDictionaryRecursiveEvidence CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls}

/-- Every generated selected focus has either an actual historical packet with
ordinary observation growth or a purely syntactic unrecorded finite binary nominal tree or scalar leaf.
Neither alternative assumes source Evidence or current BranchModels. -/
def Covered (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.current root focus → ∀ key children,
    GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
    (∃ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context ∧
      packet.site.occurrence = focus) ∨
    GeneralDictionaryTreeLeaf.HasTreeLeaf registry state.current.context focus ∨
    GeneralDictionaryScalarLeaf.HasScalarLeaf registry state.current.context focus

theorem selected_instance (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (covered : Covered registry state root) (reached : Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children ∧
      ∀ child ∈ children, Generated state.current root child := by
  rcases covered focus reached key children selected with historical | leaf | scalar
  · obtain ⟨packet,member,growth,same⟩ := historical
    exact ⟨(GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root focus state formed
      packet member growth same key children selected model valid).2.2,
      (GeneralDictionaryOrdinarySelectedReplay.selected_generated registry root focus state formed
      packet member growth same key children selected model valid).2⟩
  · have result := GeneralDictionaryTreeLeaf.selected_of_coverage registry state.current focus leaf key children
      (GeneralNominalSupportBoundary.selected_old selected) model valid.1
    rw [result.1]
    exact ⟨result.2.1,by intro child member; cases member⟩
  · have result := GeneralDictionaryScalarLeaf.selected_of_coverage registry state.current focus scalar key children
      (GeneralNominalSupportBoundary.selected_old selected) model valid.1
    rw [result.1]
    exact ⟨result.2.1,by intro child member; cases member⟩

mutual
  theorem dictionary_evidence (registry : Registry) (root : Occurrence roles)
      (state : Tracked roles) (formed : SourceFormed registry root state)
      (covered : Covered registry state root) (model : GeneralNominalCommonBridge.Assignment)
      (valid : Models state.current model) (dictionary : GeneralDictionaryReadback.Payload)
      (focus : Occurrence roles) (reached : Generated state.current root focus)
      (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state focus (.selected dictionary)) :
      Evidence registry state.current.context model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨childrenList,safe,unique,children⟩ := GeneralDictionaryCoveredEvidence.classify_node_parts (v := GeneralNominalSupportBoundary.vocabulary roles) (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state focus key dictionaries derived
      have selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key _) :=
        (local_correspondence registry state focus _).mp (B4TargetV3.Local.selected safe unique)
      have source := selected_instance registry root focus state formed covered reached key childrenList selected model valid
      exact evidence_node registry state.current.context model focus key childrenList dictionaries source.1
        (dictionaries_evidence registry root state formed covered model valid _ _ source.2 children)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (registry : Registry) (root : Occurrence roles)
      (state : Tracked roles) (formed : SourceFormed registry root state)
      (covered : Covered registry state root) (model : GeneralNominalCommonBridge.Assignment)
      (valid : Models state.current model) (dictionaries : List GeneralDictionaryReadback.Payload)
      (demands : List (Occurrence roles))
      (reached : ∀ focus ∈ demands, Generated state.current root focus)
      (derived : All₂ (fun focus dictionary =>
        B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state focus (.selected dictionary)) demands dictionaries) :
      All₂ (Evidence registry state.current.context model) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence registry root state formed covered model valid _ _
        (reached _ (by simp)) first)
        (dictionaries_evidence registry root state formed covered model valid _ _
          (fun focus member => reached focus (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

/-- Prior single-fork, spine, scalar and historical certificates embed. -/
theorem of_branch (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (covered : GeneralDictionaryBranchCoverage.Covered registry state root) : Covered registry state root := by
  intro focus reached key children selected
  rcases covered focus reached key children selected with historical | spine | scalar | branch
  · exact Or.inl historical
  · exact Or.inr (Or.inl (GeneralDictionaryTreeLeaf.spine_covered _ _ _ spine))
  · exact Or.inr (Or.inr scalar)
  · exact Or.inr (Or.inl (GeneralDictionaryTreeLeaf.branch_covered _ _ _ branch))

/-- Actual recursive fixture remains covered; this regression is not a general
reachability proof for every structural tree. -/
theorem recursive_fixture (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models GeneralDictionarySupportRecursiveExample.finish.current model) :
    Evidence GeneralNominalExamples.registry GeneralDictionarySupportRecursiveExample.finish.current.context model
      GeneralNominalExamples.displayRoot (.node 1 [.node 3 []]) := by
  apply dictionary_evidence GeneralNominalExamples.registry GeneralNominalExamples.displayRoot
    GeneralDictionarySupportRecursiveExample.finish
    (GeneralNominalSupportBoundary.reachable_formed _ _ _ GeneralDictionarySupportRecursiveExample.actual_reachable)
    (of_branch _ _ _ (GeneralDictionaryBranchCoverage.of_spine _ _ _
      (GeneralDictionarySpineCoverage.of_mixed _ _ _ GeneralDictionaryMixedCoverageExample.covered))) model valid _ _ .root
  exact GeneralDictionarySupportRecursiveClassification.classified

/-- Historical membership or purely syntactic finite-tree/scalar leaf coverage. -/
def TraceCovered (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.current root focus → ∀ key children,
    GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
    (∃ packet ∈ state.current.packets, packet.site.occurrence = focus) ∨
    GeneralDictionaryTreeLeaf.HasTreeLeaf registry state.current.context focus ∨
    GeneralDictionaryScalarLeaf.HasScalarLeaf registry state.current.context focus

theorem of_trace (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (covered : TraceCovered registry state root) : Covered registry state root := by
  intro focus reached key children selected
  rcases covered focus reached key children selected with recorded | tree | scalar
  · obtain ⟨packet,member,same⟩ := recorded
    exact Or.inl ⟨packet,member,GeneralDictionarySupportOrdinaryExecution.initial_packets_extension
      registry root context state path packet member,same⟩
  · exact Or.inr (Or.inl tree)
  · exact Or.inr (Or.inr scalar)

theorem initial_dictionary_evidence (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (covered : TraceCovered registry state root)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  dictionary_evidence registry root state
    (GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) path)
    (of_trace registry root context state path covered) model valid dictionary root .root derived
end Yulang.GeneralDictionaryTreeCoverage
