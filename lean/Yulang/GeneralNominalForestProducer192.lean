import Yulang.GeneralNominalReusableForest192
import Yulang.GeneralNominalInitialLeafStep189
import Yulang.GeneralNominalSourceRepeatedEvidence190

/-! Small genuine producers for reusable forest certificates. Arbitrary
recursive classifications are deliberately outside these leaf results. -/
namespace Yulang.GeneralNominalForestProducer192
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralDictionaryReadback (Payload)
open GeneralNominalReusableForest192
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {before after : State roles} {plan : Plan roles} {support : List (Occurrence roles)}

/-- Existing all-novel certificates embed without changing any execution. -/
theorem of_installed {demands : List (Occurrence roles)} {payloads : List Payload}
    (build : GeneralNominalInstalledForest191.Build registry root before demands payloads after) :
    Build registry root before demands payloads after := by
  induction build with
  | nil => exact .nil _
  | cons plan support enabled reached novel children siblings childIH siblingIH =>
    exact .cons plan support enabled reached novel childIH siblingIH

/-- Every nonempty certificate has genuine current-state enablement at its
first occurrence, including when that occurrence is reused without a step. -/
theorem first_enabled {demand : Occurrence roles} {demands : List (Occurrence roles)}
    {payload : Payload} {payloads : List Payload}
    (build : Build registry root before (demand :: demands) (payload :: payloads) after) :
    ∃ plan support, plan.packet.site.occurrence = demand ∧ Installable registry before plan support := by
  cases build with
  | cons plan support enabled reached novel children siblings => exact ⟨plan,support,rfl,enabled⟩
  | reuse plan support enabled reached committed children siblings => exact ⟨plan,support,rfl,enabled⟩

/-- A ready leaf always has a zero-or-one-install certificate. No novelty or
stability premise is required; already committed nodes cause no transition. -/
theorem leaf (enabled : Installable registry before plan support)
    (reached : GeneralNominalSaturationState.Generated before.core.erased.current root plan.packet.site.occurrence)
    (terminal : plan.packet.children = []) :
    ∃ after, Build registry root before [plan.packet.site.occurrence]
      [.node plan.packet.declaration.id []] after ∧
      (after = before ∨ (boundary roles).Step registry root before after) := by
  classical
  by_cases committed : GeneralNominalFeedbackSteps.Committed before.core.erased.current plan.packet
  · refine ⟨before,?_,Or.inl rfl⟩
    apply Build.reuse plan support enabled reached committed
    · rw [terminal]; exact .nil _
    · exact .nil _
  · refine ⟨install before plan support enabled,?_,Or.inr ⟨_,reached,.install plan support enabled committed⟩⟩
    apply Build.cons plan support enabled reached committed
    · rw [terminal]; exact .nil _
    · exact .nil _

/-- Stable states expose the genuine limitation of the old all-novel forest:
no nonempty certificate can start there. -/
theorem stable_no_installed {demand : Occurrence roles} {demands : List (Occurrence roles)}
    {payload : Payload} {payloads : List Payload}
    (stable : (boundary roles).Stable registry before root) :
    ¬ GeneralNominalInstalledForest191.Build registry root before
      (demand :: demands) (payload :: payloads) after := by
  intro build
  cases build with
  | cons plan support enabled reached novel children siblings =>
    exact stable _ reached _ (.install plan support enabled novel)

/-- An arbitrary selected initial no-output leaf produces an inhabited
reachable end state and its dictionary in every final model. No Stable is
assumed; this is not a general recursive-source completion theorem. -/
theorem selected_initial_leaf (checked : Checked registry)
    (source : (boundary roles).Initial registry root before)
    (selected : Local registry before root (.selected key children))
    (terminal : ∀ declaration ∈ registry.declarations, declaration.id = key → declaration.requirements = [])
    (empty : root.demand.outputs = []) :
    children = [] ∧ ∃ after,
      Build registry root before [root] [.node key []] after ∧
      (after = before ∨ (boundary roles).Step registry root before after) ∧
      B4TargetV6.Reachable (boundary roles) registry root after ∧
      (∃ model, Models after model) ∧
      ∀ model, Models after model → (boundary roles).Evidence registry after model root (.node key []) := by
  obtain ⟨candidate,support,frame,kids,enabled⟩ :=
    GeneralNominalInitialLeafStep189.selected_candidate checked source selected terminal empty
  have isLeaf := GeneralNominalHeadLeafPlan189.children_empty candidate
    (terminal candidate.packet.declaration frame.visible frame.key_eq)
  have reached : GeneralNominalSaturationState.Generated before.core.erased.current root candidate.packet.site.occurrence := by
    rw [frame.occurrence_eq]; exact .root
  obtain ⟨after,build,action⟩ := leaf enabled reached isLeaf
  have exactBuild : Build registry root before [root] [.node key []] after := by
    simpa only [frame.occurrence_eq,frame.key_eq] using build
  have sound := GeneralNominalReusableForest192.source_tree_sound (.node key []) source exactBuild
  exact ⟨kids.symm.trans isLeaf,after,exactBuild,action,sound.1,sound.2.1,
    fun model valid => (sound.2.2 model valid).2⟩

/-- Arbitrary finite variable heads, including repeated names and named
requests, produce a real zero-or-one-step dictionary certificate. Explicit
coverage and complete RHS translation are inherited source restrictions. -/
theorem selected_variable_leaf (checked : Checked registry)
    (source : (boundary roles).Initial registry root before)
    (selected : Local registry before root (.selected key children))
    (declarations : ∀ declaration ∈ registry.declarations, declaration.id = key →
      (∃ names : List Nat, declaration.head = names.map GeneralDeclarationPatterns.Pattern.var) ∧
      declaration.requirements = [] ∧
      (∀ output ∈ root.demand.outputs, ∃ equation ∈ declaration.associated, equation.name = output.name) ∧
      ∀ equation ∈ declaration.associated, GeneralNominalHeadMatchMass.Complete
        (GeneralNominalInspection.translate before.core.erased.current.context.state.constructors
          before.core.erased.current.context.interpretation (GeneralDeclarationPatterns.normalize equation.rhs))) :
    children = [] ∧ ∃ after,
      Build registry root before [root] [.node key []] after ∧
      (after = before ∨ (boundary roles).Step registry root before after) ∧
      B4TargetV6.Reachable (boundary roles) registry root after ∧
      (∃ model, Models after model) ∧
      ∀ model, Models after model → (boundary roles).Evidence registry after model root (.node key []) := by
  obtain ⟨candidate,support,frame,kids,enabled⟩ :=
    GeneralNominalSourceRepeatedEvidence190.selected_source_candidate checked source selected declarations
  have isLeaf := GeneralNominalHeadLeafPlan189.children_empty candidate
    (declarations candidate.packet.declaration frame.visible frame.key_eq).2.1
  have reached : GeneralNominalSaturationState.Generated before.core.erased.current root candidate.packet.site.occurrence := by
    rw [frame.occurrence_eq]; exact .root
  obtain ⟨after,build,action⟩ := leaf enabled reached isLeaf
  have exactBuild : Build registry root before [root] [.node key []] after := by
    simpa only [frame.occurrence_eq,frame.key_eq] using build
  have sound := GeneralNominalReusableForest192.source_tree_sound (.node key []) source exactBuild
  exact ⟨kids.symm.trans isLeaf,after,exactBuild,action,sound.1,sound.2.1,
    fun model valid => (sound.2.2 model valid).2⟩

end Yulang.GeneralNominalForestProducer192
