import Yulang.GeneralDictionarySupportComposition

/-! A weaker explicit residual for V5 EvidenceNode: branch validity only at
the caller's assignment and selected focus, with all EvidenceNode premises.
It neither asserts Joint nor discharges this remaining semantic obligation. -/
namespace Yulang.GeneralDictionarySameModelComposition
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportBoundary
open GeneralNominalRecursiveCandidates
open CommonRoleOutermostResolver
open B4TargetV5

/-- Exact V5 node scope, including child dictionaries at the SAME assignment.
The conclusion is only a checked visible selected branch, not parent Evidence,
Joint, alias-class coherence, or a fresh existential assignment. -/
def SameModelBranchAtSelected (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root,
    Reachable (boundary roles) registry root state → ∀ model,
    (boundary roles).Models state model → ∀ focus key children dictionaries,
    (focus = root ∨ (boundary roles).Generated registry state root focus) →
    (boundary roles).Stable registry state focus →
    (∀ child, child ∈ children → (boundary roles).Stable registry state child) →
    B4Target.SafeKnown (boundary roles).toSourceBoundary registry state focus →
    B4Target.Unique (boundary roles).toSourceBoundary registry state focus key children →
    All₂ (fun child dictionary => (boundary roles).Evidence registry state model child dictionary)
      children dictionaries →
    ∃ declaration ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles declaration,
      declaration.id = key ∧
      ∃ bounds : List (GeneralNominalInspection.Bounds state.current.context.state),
        arguments state.current.context focus = some bounds ∧
        BranchModels registry state.current.context focus declaration checked bounds model

/-- The existing stronger Joint residual implies this model-local residual via
reachable stable packet materialization. The converse is not asserted. -/
theorem of_joint (roles : Roles.RoleDecls)
    (joint : GeneralDictionarySupportComposition.JointAtSelected roles) :
    SameModelBranchAtSelected roles := by
  intro registry checked state root reachable model valid focus key children dictionaries reached stable _ safe unique _
  have generated : Generated state.current root focus := by
    rcases reached with same | reached
    · subst focus; exact .root
    · exact reached
  have selected := (local_correspondence registry state focus (.selected key children)).mp
    (B4TargetV3.Local.selected safe unique)
  have instanceRule := (GeneralDictionarySupportEvidence.reachable_joint_instance registry state root focus
    reachable key children stable selected
    (joint registry checked state root reachable focus generated stable key children selected)).1 model valid
  obtain ⟨decl,visible,check,identity,_,bounds,located,_,_,_,_,branch⟩ := instanceRule
  exact ⟨decl,visible,check,identity,bounds,located,branch⟩

/-- Conditional composition only. No witness at another assignment can be
substituted: the residual must supply the caller's exact model. -/
theorem evidenceNode (roles : Roles.RoleDecls) (branch : SameModelBranchAtSelected roles) :
    B4SkeletonV5.EvidenceNode (boundary roles) := by
  intro registry checked state root reachable model valid focus key children dictionaries reached stable childrenStable safe unique given
  obtain ⟨declaration,visible,checkedDecl,identity,bounds,located,sameModel⟩ :=
    branch registry checked state root reachable model valid focus key children dictionaries
      reached stable childrenStable safe unique given
  exact GeneralDictionaryRecursiveEvidence.evidence_node_of_branch registry checked.2
    state.current.context model focus key children dictionaries unique.1
    declaration visible checkedDecl identity bounds located sameModel given
end Yulang.GeneralDictionarySameModelComposition
