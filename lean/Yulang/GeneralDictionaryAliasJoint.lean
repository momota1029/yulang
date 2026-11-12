import Yulang.GeneralDictionarySupportComposition

/-! One common applicability witness can be rerooted at a registered alias.
This does not construct Joint from separately chosen survivor witnesses. -/
namespace Yulang.GeneralDictionaryAliasJoint
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalJointCandidates
variable {roles : Roles.RoleDecls}

/-- Reroot the same simultaneous witness, preserving all named outputs. -/
theorem joint_at_related (registry : Registry) (state : State roles)
    (root : Occurrence roles) (site : GeneralNominalDemandMerging.Site roles) (key : Nat)
    (related : Related state root site) (joint : Joint registry state root key) :
    Joint registry state site.occurrence key := by
  obtain ⟨choices,model,valid,atRoot,all⟩ := joint
  refine ⟨?_,model,valid,all site related,?_⟩
  · intro packet present alias
    exact choices packet present (.trans related.2 alias)
  · intro other rel
    exact all other ⟨rel.1,.trans related.2 rel.2⟩

/-- Joint is constant on the registered sites of a fixed alias class. -/
theorem joint_alias_iff (registry : Registry) (state : State roles)
    (first last : GeneralNominalDemandMerging.Site roles) (key : Nat)
    (one : first ∈ state.sites) (two : last ∈ state.sites)
    (alias : Alias state first.occurrence.identity last.occurrence.identity) :
    Joint registry state first.occurrence key ↔ Joint registry state last.occurrence key :=
  ⟨joint_at_related registry state first.occurrence last key ⟨two,alias⟩,
   joint_at_related registry state last.occurrence first key ⟨one,.symm alias⟩⟩

/-- One representative can discharge the semantic Joint premise for an actual
selected, stable target. Reachability and selection are still required. -/
theorem representative_instance (registry : Registry)
    (state : GeneralNominalSupport.Tracked roles) (root focus representative : Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (site : GeneralNominalDemandMerging.Site roles)
    (related : Related state.current representative site) (same : site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalSupportSteps.Stable registry state focus)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (joint : Joint registry state.current representative key) :
    (∀ model, Models state.current model → GeneralDictionaryRecursiveEvidence.Instance
      registry state.current.context model focus key children) ∧
      ∀ child ∈ children, Generated state.current focus child := by
  have atFocus := joint_at_related registry state.current representative site key related joint
  rw [same] at atFocus
  exact GeneralDictionarySupportEvidence.reachable_joint_instance registry state root focus reachable
    key children stable selected atFocus

end Yulang.GeneralDictionaryAliasJoint
