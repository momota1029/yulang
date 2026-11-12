import Yulang.GeneralDictionaryVariableTree
import Yulang.GeneralDictionaryCoveredEvidence
import Yulang.GeneralDictionaryScalarLeaf

/-! Recursive dictionaries whose selected descendants remain inside an explicit
structural domain. Nonterminal unrecorded branches retain their real children.
Domain closure is not inferred from support Generated or from stability. -/
namespace Yulang.GeneralDictionaryVariableTreeCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalSupportBoundary
open GeneralDictionaryRecursiveEvidence CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls}

/-- Syntactic/historical coverage only: no Instance, Evidence, BranchModels or
Joint appears here. The historical alternative carries actual observation growth. -/
def CoveredOn (registry : Registry) (state : Tracked roles)
    (domain : Occurrence roles → Prop) : Prop :=
  ∀ focus, domain focus → ∀ key children,
    GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
    (∃ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context ∧
      packet.site.occurrence = focus) ∨
    GeneralDictionaryVariableTree.HasVariableTree registry state.current.context focus ∨
    GeneralDictionaryScalarLeaf.HasScalarLeaf registry state.current.context focus

/-- Actual selected children remain in the domain. This is an explicit
structural closure obligation, not a claim that unrecorded children are Generated. -/
def ClosedOn (registry : Registry) (state : Tracked roles)
    (domain : Occurrence roles → Prop) : Prop :=
  ∀ focus, domain focus → ∀ key children,
    GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
    ∀ child ∈ children, domain child

theorem selected_instance (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (domain : Occurrence roles → Prop) (covered : CoveredOn registry state domain)
    (inside : domain focus) (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children := by
  rcases covered focus inside key children selected with historical | tree | scalar
  · obtain ⟨packet,member,growth,same⟩ := historical
    exact (GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root focus state formed
      packet member growth same key children selected model valid).2.2
  · exact GeneralDictionaryVariableTree.selected_of_coverage registry state.current focus tree key children
      (GeneralNominalSupportBoundary.selected_old selected) model valid.1
  · have result := GeneralDictionaryScalarLeaf.selected_of_coverage registry state.current focus scalar key children
      (GeneralNominalSupportBoundary.selected_old selected) model valid.1
    simpa only [result.1] using result.2.1

mutual
  theorem dictionary_evidence (registry : Registry) (root : Occurrence roles)
      (state : Tracked roles) (formed : SourceFormed registry root state)
      (domain : Occurrence roles → Prop) (covered : CoveredOn registry state domain)
      (closed : ClosedOn registry state domain)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
      (dictionary : GeneralDictionaryReadback.Payload) (focus : Occurrence roles)
      (inside : domain focus)
      (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
        registry state focus (.selected dictionary)) :
      Evidence registry state.current.context model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨childrenList,safe,unique,children⟩ := GeneralDictionaryCoveredEvidence.classify_node_parts
        (v := GeneralNominalSupportBoundary.vocabulary roles)
        (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state focus key dictionaries derived
      have selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key _) :=
        (local_correspondence registry state focus _).mp (B4TargetV3.Local.selected safe unique)
      exact evidence_node registry state.current.context model focus key childrenList dictionaries
        (selected_instance registry root focus state formed domain covered inside key childrenList selected model valid)
        (dictionaries_evidence registry root state formed domain covered closed model valid _ _
          (closed focus inside key childrenList selected) children)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (registry : Registry) (root : Occurrence roles)
      (state : Tracked roles) (formed : SourceFormed registry root state)
      (domain : Occurrence roles → Prop) (covered : CoveredOn registry state domain)
      (closed : ClosedOn registry state domain)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
      (dictionaries : List GeneralDictionaryReadback.Payload) (demands : List (Occurrence roles))
      (inside : ∀ focus ∈ demands, domain focus)
      (derived : All₂ (fun focus dictionary => B4TargetV3.Classify
        (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state focus (.selected dictionary))
        demands dictionaries) :
      All₂ (Evidence registry state.current.context model) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence registry root state formed domain covered closed model valid _ _
        (inside _ (by simp)) first)
        (dictionaries_evidence registry root state formed domain covered closed model valid _ _
          (fun focus member => inside focus (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

/-- The structural domain need not equal the journal's Generated graph. In
particular no historical edge is fabricated for an unrecorded nonterminal. -/
theorem reachable_dictionary_evidence (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (domain : Occurrence roles → Prop) (inside : domain root)
    (covered : CoveredOn registry state domain) (closed : ClosedOn registry state domain)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  dictionary_evidence registry root state (reachable_formed registry state root reachable)
    domain covered closed model valid dictionary root inside derived
end Yulang.GeneralDictionaryVariableTreeCoverage
