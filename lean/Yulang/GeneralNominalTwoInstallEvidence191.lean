import Yulang.GeneralNominalInstalledEvidence190

/-! A genuine nonempty dictionary tree from two actual WF installations.
Enablement is explicit; child Evidence is derived rather than assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalTwoInstallEvidence191
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryOrdinaryTrace
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
variable {parent child : Plan roles} {parentSupport childSupport : List (Occurrence roles)}

theorem install_growth (enabled : Installable registry state parent parentSupport) :
    Extension state.core.erased.current.context
      (install state parent parentSupport enabled).core.erased.current.context := by
  change Extension state.core.erased.current.context parent.packet.privateContext
  rw [← enabled.frame.context_eq]
  exact packet_extension parent.packet

/-- The parent and terminal child share the final model, not merely a pair of
possibly incompatible existential witnesses. -/
theorem parent_evidence
    (first : Installable registry state parent parentSupport)
    (second : Installable registry (install state parent parentSupport first) child childSupport)
    (oneChild : parent.packet.children = [child.packet.site.occurrence])
    (terminal : child.packet.children = [])
    (model : Assignment)
    (valid : Models (install (install state parent parentSupport first) child childSupport second) model) :
    (boundary roles).Evidence registry
      (install (install state parent parentSupport first) child childSupport second) model
      parent.packet.site.occurrence (.node parent.packet.declaration.id [.node child.packet.declaration.id []]) := by
  have oldValid := ((install_models second model).mp valid).1
  have old := GeneralNominalInstalledEvidence190.current_instance first model oldValid
  have current := instance_extension registry _ _ (install_growth second) model valid.1.1.1 _ _ _ old
  apply GeneralDictionaryRecursiveEvidence.evidence_node registry _ model _ _ _ _ current
  rw [oneChild]
  exact .cons (GeneralNominalInstalledEvidence190.terminal_evidence second terminal model valid) .nil

/-- Genuine enablement supplies an inhabited final state and universal parent
Evidence there. It does not prove arbitrary selected sources are installable. -/
theorem inhabited_evidence
    (first : Installable registry state parent parentSupport)
    (second : Installable registry (install state parent parentSupport first) child childSupport)
    (oneChild : parent.packet.children = [child.packet.site.occurrence])
    (terminal : child.packet.children = []) :
    (∃ model, Models (install (install state parent parentSupport first) child childSupport second) model) ∧
    ∀ model, Models (install (install state parent parentSupport first) child childSupport second) model →
      (boundary roles).Evidence registry
        (install (install state parent parentSupport first) child childSupport second) model
        parent.packet.site.occurrence (.node parent.packet.declaration.id [.node child.packet.declaration.id []]) :=
  ⟨installed_inhabited second,parent_evidence first second oneChild terminal⟩

/-- Every actual parent install records all its canonical child edges. -/
theorem generated_child (root : Occurrence roles)
    (first : Installable registry state parent parentSupport)
    (parentGenerated : GeneralNominalSaturationState.Generated state.core.erased.current root parent.packet.site.occurrence)
    (focus : Occurrence roles) (member : focus ∈ parent.packet.children) :
    GeneralNominalSaturationState.Generated
      (install state parent parentSupport first).core.erased.current root focus := by
  have old := GeneralNominalSaturationSteps.generated_monotone (install_extends first).journal parentGenerated
  apply GeneralNominalSaturationState.Generated.child old
  change (parent.packet.site.occurrence,focus) ∈ state.core.erased.current.edges ++
    parent.packet.children.map (fun child => (parent.packet.site.occurrence,child))
  exact List.mem_append_right _ (List.mem_map.mpr ⟨focus,member,rfl⟩)

/-- These are two actual WF steps when each focus is generated and each action
is semantically novel. The evidence theorem above does not itself assert execution. -/
theorem execution (root : Occurrence roles)
    (first : Installable registry state parent parentSupport)
    (second : Installable registry (install state parent parentSupport first) child childSupport)
    (parentGenerated : GeneralNominalSaturationState.Generated state.core.erased.current root parent.packet.site.occurrence)
    (childGenerated : GeneralNominalSaturationState.Generated
      (install state parent parentSupport first).core.erased.current root child.packet.site.occurrence)
    (parentNovel : ¬ GeneralNominalFeedbackSteps.Committed state.core.erased.current parent.packet)
    (childNovel : ¬ GeneralNominalFeedbackSteps.Committed
      (install state parent parentSupport first).core.erased.current child.packet) :
    B4Target.Steps ((boundary roles).Step registry root) state
      (install (install state parent parentSupport first) child childSupport second) :=
  .tail (.tail .refl ⟨_,parentGenerated,.install parent parentSupport first parentNovel⟩)
    ⟨_,childGenerated,.install child childSupport second childNovel⟩

/-- The second generated-focus premise is discharged by actual recorded edges. -/
theorem linked_execution (root : Occurrence roles)
    (first : Installable registry state parent parentSupport)
    (second : Installable registry (install state parent parentSupport first) child childSupport)
    (oneChild : parent.packet.children = [child.packet.site.occurrence])
    (parentGenerated : GeneralNominalSaturationState.Generated state.core.erased.current root parent.packet.site.occurrence)
    (parentNovel : ¬ GeneralNominalFeedbackSteps.Committed state.core.erased.current parent.packet)
    (childNovel : ¬ GeneralNominalFeedbackSteps.Committed
      (install state parent parentSupport first).core.erased.current child.packet) :
    B4Target.Steps ((boundary roles).Step registry root) state
      (install (install state parent parentSupport first) child childSupport second) :=
  execution root first second parentGenerated
    (generated_child root first parentGenerated _ (oneChild ▸ List.mem_singleton_self _))
    parentNovel childNovel

end Yulang.GeneralNominalTwoInstallEvidence191
