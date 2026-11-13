import Yulang.GeneralDictionarySettledRootEvidence
import Yulang.GeneralDictionaryFiniteStableCoverage

/-! Finite structural coverage discharges Joint in the actual I26 boundary.
Ordinary extension of historical contexts and explicit syntax/alias coverage
remain real restrictions; no general evidenceNode or reobservation theorem. -/
namespace Yulang.GeneralDictionarySettledFiniteCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open CommonRoleOutermostResolver
open GeneralDictionarySettledProjection (fresh)
variable {roles : Roles.RoleDecls}

/-- Selection projects to the earlier provenance boundary, not stability. -/
theorem selected_support {registry : Registry} {state : Tracked roles}
    {focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}
    (selected : GeneralNominalSettledBoundary.Local registry state focus (.selected key children)) :
    GeneralNominalSupportBoundary.Local registry state focus (.selected key children) := by
  obtain ⟨support,guard⟩ := GeneralDictionarySettledEvidence.selected_support registry state focus key children selected
  cases selected with
  | selected safe unique =>
    refine .selected ⟨safe.1,safe.2.1,safe.2.2.1,?_⟩ unique
    rintro (pending | unsupported)
    · exact safe.2.2.2 (Or.inl (Or.inl pending))
    · exact unsupported ⟨support,guard.1⟩

/-- Every generated selected focus is historical or independently covered by
finite structural syntax. No branch-model or Joint conclusion is an input. -/
def Covered (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.current root focus → ∀ key children,
    GeneralNominalSettledBoundary.Local registry state focus (.selected key children) →
    (∃ packet ∈ state.current.packets, packet.site.occurrence = focus) ∨
    ∃ chosen ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles chosen,
      GeneralDictionaryFiniteAliasJoint.Shape state.current.context registry focus chosen checked ∧
      GeneralDictionaryFiniteAliasJoint.Covered registry state focus chosen checked

theorem covered_of_support {registry : Registry} {state : Tracked roles} {root : Occurrence roles}
    (covered : GeneralDictionaryFiniteStableCoverage.Covered registry state root) :
    Covered registry state root :=
  fun focus generated key children selected => covered focus generated key children (selected_support selected)

/-- Genuine guarded stability is sufficient after deriving Joint from syntax.
History can be nonempty; each historical context must be an ordinary extension. -/
theorem selected_instance_children (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (fresh roles) registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (covered : Covered registry state root)
    (reached : Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSettledBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children ∧
      ∀ child ∈ children, Generated state.current root child := by
  have formed := GeneralNominalDownstreamSteps.formed_old (GeneralNominalValueSteps.formed_old
    (GeneralNominalSettledSteps.formed_old (GeneralNominalSettledBoundary.reachable_formed reachable)))
  have old := selected_support selected
  rcases covered focus reached key children selected with historical | structural
  · obtain ⟨packet,member,same⟩ := historical
    exact ⟨(GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root focus state formed
      packet member (growth packet member) same key children old model valid).2.2,
      (GeneralDictionaryOrdinarySelectedReplay.selected_generated registry root focus state formed
      packet member (growth packet member) same key children old model valid).2⟩
  · obtain ⟨chosen,visible,checked,shape,aliases⟩ := structural
    have joint := GeneralDictionaryFiniteAliasJoint.covered_joint registry root focus state formed growth
      chosen visible checked shape key children old aliases model valid
    have result := GeneralDictionarySettledEvidence.reachable_joint_instance registry state root focus reachable
      key children (GeneralDictionarySettledRootEvidence.stable_generated stable reached) selected joint
    exact ⟨result.1 model valid,fun child member => generated_trans reached (result.2 child member)⟩

mutual
  theorem dictionary_evidence (registry : Registry) (root : Occurrence roles)
      (state : Tracked roles)
      (reachable : B4TargetV5.Reachable (fresh roles) registry root state)
      (growth : ∀ packet ∈ state.current.packets,
        GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
      (stable : GeneralNominalSettledSteps.Stable registry state root)
      (covered : Covered registry state root)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
      (dictionary : Dictionary) (focus : Occurrence roles)
      (reached : Generated state.current root focus)
      (classified : B4TargetV3.Classify (fresh roles).toSourceBoundary
        registry state focus (.selected dictionary)) :
      Evidence registry state.current.context model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨children,safe,unique,all⟩ := GeneralDictionaryCoveredEvidence.classify_node_parts
        (v := GeneralNominalSettledBoundary.vocabulary roles)
        (fresh roles).toSourceBoundary registry state focus key dictionaries classified
      have selected := (GeneralNominalSettledBoundary.local_correspondence registry state focus _).mp
        (B4TargetV3.Local.selected safe unique)
      have result := selected_instance_children registry root focus state reachable growth stable covered
        reached key children selected model valid
      exact evidence_node registry state.current.context model focus key children dictionaries result.1
        (dictionaries_evidence registry root state reachable growth stable covered model valid
          dictionaries children result.2 all)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (registry : Registry) (root : Occurrence roles)
      (state : Tracked roles)
      (reachable : B4TargetV5.Reachable (fresh roles) registry root state)
      (growth : ∀ packet ∈ state.current.packets,
        GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
      (stable : GeneralNominalSettledSteps.Stable registry state root)
      (covered : Covered registry state root)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
      (dictionaries : List Dictionary) (roots : List (Occurrence roles))
      (reached : ∀ focus ∈ roots, Generated state.current root focus)
      (classified : All₂ (fun focus dictionary => B4TargetV3.Classify (fresh roles).toSourceBoundary
        registry state focus (.selected dictionary)) roots dictionaries) :
      All₂ (Evidence registry state.current.context model) roots dictionaries := by
    cases classified with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence registry root state reachable growth stable covered model valid _ _
        (reached _ (by simp)) first)
        (dictionaries_evidence registry root state reachable growth stable covered model valid _ _
          (fun focus member => reached focus (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

/-- All final-model soundness, with no model-existence assumption: inconsistent
final states satisfy this universal statement vacuously. -/
theorem root_dictionary_all_models (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (fresh roles) registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (covered : Covered registry state root)
    (dictionary : Dictionary)
    (classified : B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary)) :
    ∀ model, Models state.current model → Evidence registry state.current.context model root dictionary :=
  fun model valid => dictionary_evidence registry root state reachable growth stable covered model valid
    dictionary root .root classified

theorem completed_evidence (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (fresh roles) registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (covered : Covered registry state root)
    (tree : Tree) (dictionary : Dictionary)
    (resolved : Resolves (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) root tree)
    (completed : B4TargetV3.Completed tree (.selected dictionary)) :
    ∀ model, Models state.current model → Evidence registry state.current.context model root dictionary :=
  root_dictionary_all_models registry root state reachable growth stable covered dictionary
    (B4TargetV3.tree_classifies _ _ _ _ _ _ resolved completed)
end Yulang.GeneralDictionarySettledFiniteCoverage
