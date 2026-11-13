import Yulang.GeneralNominalCenteredGroundBoundary
import Yulang.GeneralDictionaryCommittedEvidence

/-! A current-context centered installation bridge. The final theorem names
its missing selected-plan producer explicitly; it is not an unconditional
EvidenceNode theorem. Historical stored packets are not substituted for a
packet inspected in the current context. -/
namespace Yulang.GeneralDictionaryCenteredReady176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps
open GeneralNominalCenteredBoundary (Local Installable)
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralDictionaryRecursiveEvidence (Instance Evidence)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}

theorem stable_committed (stable : Stable registry state focus)
    (plan : Plan roles) (same : plan.packet.site.occurrence = focus)
    (enabled : Installable registry state plan) :
    GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet := by
  classical
  apply Classical.byContradiction
  intro novel
  obtain ⟨base,support,guard⟩ := enabled
  exact stable plan.packet.site.occurrence (same ▸ GeneralNominalSaturationState.Generated.root)
    _ (.install plan support base novel guard)

/-- A genuinely enabled, current-context plan supplies its source instance in
all centered models after stability, without replacing the supplied model. -/
theorem stable_instance (stable : Stable registry state focus)
    (plan : Plan roles) (same : plan.packet.site.occurrence = focus)
    (enabled : Installable registry state plan)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    Instance registry state.erased.current.context model focus
      plan.packet.declaration.id plan.packet.children := by
  have packet := enabled.1
  have source := GeneralDictionaryCommittedEvidence.committed_instance
    state.erased.current plan.packet
    (by simpa only [packet.1.1] using packet.1.2.2.2.1)
    packet.1.2.2.2.2.1 packet.1.2.2.2.2.2.1 packet.1.2.2.2.2.2.2.1
    (stable_committed stable plan same enabled) model valid.1
  simpa only [packet.1.1,packet.1.2.1,same] using source

theorem selected_instance (stable : Stable registry state focus)
    (selected : Local registry state focus (.selected key children))
    (plan : Plan roles) (same : plan.packet.site.occurrence = focus)
    (enabled : Installable registry state plan)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    Instance registry state.erased.current.context model focus key children := by
  have one := GeneralNominalCenteredBoundary.installable_selected enabled
  rw [same] at one
  have equal := GeneralNominalCenteredBoundary.local_functional one selected
  have exact := stable_instance stable plan same enabled model valid
  cases equal
  exact exact

theorem selected_evidence (stable : Stable registry state focus)
    (selected : Local registry state focus (.selected key children))
    (plan : Plan roles) (same : plan.packet.site.occurrence = focus)
    (enabled : Installable registry state plan)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List Payload)
    (given : All₂ (Evidence registry state.erased.current.context model) children dictionaries) :
    Evidence registry state.erased.current.context model focus (.node key dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry state.erased.current.context
    model focus key children dictionaries (selected_instance stable selected plan same enabled model valid) given

/-- Remaining producer obligation only at modeled reachable stable selections.
The required plan is inspected in the current context by Installable; a
historical recorded plan alone does not discharge this obligation. -/
def ModeledSelectedInstallable (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (groundBoundary roles).Checked registry →
    ∀ state root, B4TargetV5.Reachable (groundBoundary roles) registry root state →
    (∃ model, Models state model) → ∀ focus key children,
    (focus = root ∨ (groundBoundary roles).Generated registry state root focus) →
    Stable registry state focus → Local registry state focus (.selected key children) →
    ∃ plan : Plan roles, plan.packet.site.occurrence = focus ∧ Installable registry state plan

theorem evidenceNode_of_modeledSelectedInstallable
    (producer : ModeledSelectedInstallable roles) :
    B4SkeletonV5.EvidenceNode (groundBoundary roles) := by
  intro registry checked state root reachable model valid focus key children dictionaries
    reached stable _ safe unique given
  have selected : Local registry state focus (.selected key children) :=
    (GeneralNominalCenteredBoundary.local_correspondence registry state focus _).mp
      (B4TargetV3.Local.selected safe unique)
  obtain ⟨plan,same,enabled⟩ := producer registry checked state root reachable ⟨model,valid⟩
    focus key children reached stable selected
  exact selected_evidence stable selected plan same enabled model valid dictionaries given

end Yulang.GeneralDictionaryCenteredReady176
