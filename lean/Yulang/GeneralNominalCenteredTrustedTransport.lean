import Yulang.GeneralNominalCenteredSourcePersistence

/-! The coarse centered ledger is unchanged by source-preserving transitions.
Previously justified input and output facts remain justified; no new input
explanation is inferred from equality of outer observation tests. -/
namespace Yulang.GeneralNominalCenteredTrustedTransport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredSupport (Fact Trusted)
open GeneralNominalCenteredSourcePersistence

variable {roles : Roles.RoleDecls} {root : Occurrence roles}

theorem plans_step (step : Step registry root before after) : before.plans ⊆ after.plans := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative | refresh | merge => exact fun _ member => member
  | install => exact fun _ member => List.mem_cons_of_mem _ member

theorem models_step (step : Step registry root before after) (facts : List (Fact roles)) :
    GeneralNominalCenteredSupport.Models after.erased after.sourceSites facts =
      GeneralNominalCenteredSupport.Models before.erased before.sourceSites facts := by
  funext model
  simp only [GeneralNominalCenteredSupport.Models,
    (GeneralNominalCenteredTrace.source_step step).1,(GeneralNominalCenteredTrace.source_step step).2]

theorem trusted_step (step : Step registry root before after)
    (trusted : Trusted before.erased before.sourceSites before.plans facts) :
    Trusted after.erased after.sourceSites after.plans facts := by
  have modelMap (facts : List (Fact roles)) (model : GeneralNominalCommonBridge.Assignment)
      (valid : GeneralNominalCenteredSupport.Models after.erased after.sourceSites facts model) :
      GeneralNominalCenteredSupport.Models before.erased before.sourceSites facts model := by
    rw [models_step step] at valid
    exact valid
  induction trusted with
  | source => exact .source
  | legacy facts readbacks previous =>
    exact .legacy facts readbacks (GeneralNominalCenteredSourcePersistence.trusted_step step previous)
  | input plan support previous member recorded readback ih =>
    refine .input plan support ih (plans_step step member) (facts_step step recorded) ?_
    intro slot visited test observation head model valid
    exact readback slot visited test observation head model (modelMap _ model valid)
  | output plan support previous member recorded included settled ih =>
    exact .output plan support ih (plans_step step member) (facts_step step recorded) included
      (settled_step step settled)
  | merge first last support previous recorded holds same ih =>
    exact .merge first last support ih (facts_step step recorded)
      (fun model valid => holds model (modelMap _ model valid))
      (GeneralNominalCommonTrustedLedger.same_inputs_restrict same (modelMap _))

theorem initial_trusted_empty
    (trusted : Trusted (initial context (root : Occurrence roles)).erased
      (initial context root).sourceSites (initial context root).plans facts) : facts = [] := by
  cases trusted with
  | source => rfl
  | legacy facts readbacks trusted =>
    rw [(GeneralNominalCenteredSourcePersistence.initial_trusted_empty trusted).1]
    rfl
  | input plan support previous member recorded readback => cases member
  | output plan support previous member recorded included settled => cases member
  | merge first last support previous recorded holds same => cases recorded

theorem output_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet support, GeneralNominalSupport.Fact.outputs packet support ∈ state.erased.facts →
      packet.declaration ∈ registry.declarations ∧
      packet.context.state.constructors = context.state.constructors ∧
      packet.context.interpretation = context.interpretation := by
  induction path with
  | refl => intro packet support member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative | refresh => exact ih
    | merge first last dependencies one two same novel guard =>
      intro packet support member
      rcases List.mem_append.mp member with added | old
      · obtain ⟨dependencies,present,equal⟩ := List.mem_map.mp added
        cases equal
      · exact ih packet support old
    | install plan dependencies enabled novel guard =>
      intro packet support member
      rcases List.mem_append.mp member with added | old
      · obtain ⟨dependencies,present,member⟩ := List.mem_flatMap.mp added
        rcases List.mem_cons.mp member with impossible | member
        · cases impossible
        · cases List.mem_singleton.mp member
          have config := GeneralNominalCenteredTrace.configuration_trace path
          exact ⟨enabled.1.2.2.2.1,
            (congrArg (fun ctx : GeneralNominalCandidates.Context => ctx.state.constructors) enabled.1.2.1).trans config.2.1,
            (congrArg GeneralNominalCandidates.Context.interpretation enabled.1.2.1).trans config.2.2⟩
      · exact ih packet support old

theorem promoted_labelled
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (trusted : GeneralNominalSharedSupport.Trusted state.erased facts readbacks)
    (inputs : GeneralNominalSourceProducerHandoff.TrustedInputs state.erased facts context origins
      remaining (GeneralNominalRegistrySourceTemplates.keys registry)
      (GeneralNominalSchemaVocabulary.registryVocabulary context registry))
    (present : GeneralNominalSupport.Fact.outputs packet support ∈ facts)
    (output : GeneralSourceState.Output) (member : output ∈ packet.site.occurrence.demand.outputs) :
    ∃ value : GeneralNominalLabelledOriginClosure.Value (GeneralNominalSharedSupport.Models state.erased facts)
      context origins remaining (GeneralNominalRegistrySourceTemplates.keys registry) (.source output.target),
      GeneralNominalScopedRecipeLabels.Vocabulary
        (GeneralNominalSchemaVocabulary.registryVocabulary context registry) value.term :=
  GeneralNominalRegistrySourceTemplates.promoted_output context trusted
    (fun packet support present => output_configuration path packet support
      (GeneralNominalSettledSupport.trusted_members (GeneralNominalSharedSupport.trusted_old trusted) _ present))
    inputs present output member

end Yulang.GeneralNominalCenteredTrustedTransport
