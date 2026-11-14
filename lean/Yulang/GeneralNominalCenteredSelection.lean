import Yulang.GeneralNominalCenteredAllocation
import Yulang.GeneralDictionarySupportEvidence

/-! Reachable selected proposals have registered centers. Joint applicability
and merge closure produce ordinary readiness; centered support and a common
branch model are the remaining explicit installation obligations. -/
namespace Yulang.GeneralNominalCenteredSelection
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredTrace
open GeneralNominalCenteredBoundary (Local Installable)
open GeneralNominalSaturationState (Packet Generated)

variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}

theorem selected_feedback (selected : Local registry state focus (.selected key children)) :
    GeneralNominalFeedbackK2.Local registry state.erased.current focus (.selected key children) := by
  cases selected with
  | selected safe unique =>
    exact .selected ⟨safe.1,fun cycle => safe.2.1 (Or.inl cycle),
      fun cycle => safe.2.2.1 (Or.inl cycle),fun pending => safe.2.2.2 (Or.inl pending)⟩ unique

theorem selected_base_plan
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : Generated state.erased.current root focus)
    (selected : Local registry state focus (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.erased.current focus key)
    (merges : ∀ site ∈ state.erased.current.sites, site.occurrence = focus →
      GeneralNominalFeedbackSteps.MergesClosed state.erased.current site) :
    ∃ plan : Plan roles, plan.packet.site.occurrence = focus ∧ plan.packet.declaration.id = key ∧
      plan.packet.children = children ∧ plan.input ∈ state.sites ∧
      GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet := by
  have old := selected_feedback selected
  obtain ⟨model,valid,branch,_⟩ := joint.2
  obtain ⟨declaration,visible,checked,identity,role,prepared,bounds,located,holds⟩ := branch
  obtain ⟨site,member,same⟩ := generated_registered path generated
  obtain ⟨center,recorded,centerSame⟩ := raw_site_centered path site member
  let packet : Packet roles := ⟨registry,state.erased.current.context,site,declaration,checked,bounds⟩
  let plan : Plan roles := ⟨packet,center,centerSame⟩
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.erased.current.context focus key packet.children := by
    refine ⟨?_,declaration,visible,checked,identity,role,bounds,located,prepared,?_⟩
    · cases old with | selected safe _ => exact safe.1
    · change GeneralNominalAllocation.children state.erased.current.context.state registry site.occurrence declaration checked _ = _
      rw [same]
      rfl
  have kids : packet.children = children := by
    cases old with | selected _ unique => exact (unique.2 key packet.children survivor).2
  have localRule : GeneralNominalFeedbackK2.Local registry state.erased.current site.occurrence
      (.selected declaration.id packet.children) := by
    rw [same,identity,kids]; exact old
  have closed := merges site member same
  have enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current packet := by
    refine ⟨⟨rfl,rfl,member,visible,?_,?_,?_,?_,?_,?_,?_,?_⟩,localRule,closed⟩
    · simpa only [packet,same] using role
    · simpa only [packet,same] using located
    · simpa only [packet,same] using prepared
    · exact GeneralNominalFeedbackK2.selected_legacy localRule
    · intro prior present alias
      exact identity.trans (joint.1 prior present (by simpa only [packet,same] using alias)).symm
    · intro other present inputs
      exact closed other present (GeneralDictionaryFeedbackEvidence.sameInputs_recovered state.erased.current site other inputs)
    · exact ⟨model,valid,by simpa only [Packet.Holds,packet,same] using holds⟩
    · simpa only [packet,same,identity] using joint
  exact ⟨plan,same,identity,kids,recorded,enabled⟩

theorem stable_committed (stable : Stable registry state focus) (plan : Plan roles)
    (same : plan.packet.site.occurrence = focus) (enabled : Installable registry state plan) :
    GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet := by
  classical
  apply Classical.byContradiction
  intro novel
  obtain ⟨base,support,guard⟩ := enabled
  exact stable plan.packet.site.occurrence (same ▸ Generated.root) _ (.install plan support base novel guard)

theorem guarded_selected_children
    (stable : Stable registry state focus) (selected : Local registry state focus (.selected key children))
    (plan : Plan roles) (same : plan.packet.site.occurrence = focus)
    (enabled : Installable registry state plan)
    (generated : Generated state.erased.current root focus) :
    ∀ child ∈ children, Generated state.erased.current root child := by
  have selectedPlan := GeneralNominalCenteredBoundary.installable_selected enabled
  rw [same] at selectedPlan
  have identity := GeneralNominalCenteredBoundary.local_functional selectedPlan selected
  have equal : plan.packet.children = children := by cases identity; rfl
  have committed := stable_committed stable plan same enabled
  intro child member
  apply Generated.child generated
  rw [← same]
  exact committed.2 child (equal ▸ member)

end Yulang.GeneralNominalCenteredSelection
