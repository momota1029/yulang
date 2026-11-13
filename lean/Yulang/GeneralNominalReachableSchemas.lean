import Yulang.GeneralNominalSourceInitialization

/-! The actual trace supplies registry membership and stable interpretation
for every trusted output schema. Only trusted input coverage remains in the
labelled promoted-output producer. -/
namespace Yulang.GeneralNominalReachableSchemas
open GeneralNominalSupport GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralNominalActualInspectionSteps GeneralNominalRegistrySourceTemplates
open GeneralNominalSharedSupport GeneralNominalScopedRecipeLabels

theorem reachable_all_models
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model) : AllModels state model := by
  induction path with
  | refl => exact ⟨valid.1,by intro fact member; cases member⟩
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      exact ih ((GeneralNominalSupportSteps.administrative_models action model).mp valid)
    | install packet support enabled novel guard =>
      obtain ⟨beforeValid,packetValid⟩ := (GeneralNominalSharedSteps.install_models enabled.1.2.1 model).mp valid
      have old := ih beforeValid
      obtain ⟨_,inputs,outputs⟩ := (GeneralNominalPacketSupport.packet_exact packet model).mp packetValid
      refine ⟨old.1,?_⟩
      intro fact member
      rcases List.mem_append.mp member with added | prior
      · obtain ⟨dependencies,present,member⟩ := List.mem_flatMap.mp added
        rcases List.mem_cons.mp member with rfl | member
        · exact inputs
        · cases List.mem_singleton.mp member; exact outputs
      · exact old.2 fact prior
    | merge first last support one two same novel guard =>
      obtain ⟨beforeValid,atoms⟩ := (GeneralNominalSaturationState.merge_models before.current first last model).mp valid
      have old := ih beforeValid
      refine ⟨old.1,?_⟩
      intro fact member
      rcases List.mem_append.mp member with added | prior
      · obtain ⟨dependencies,present,rfl⟩ := List.mem_map.mp added
        exact atoms
      · exact old.2 fact prior

theorem reachable_trusted_models
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (trusted : Trusted state facts readbacks)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model) :
    GeneralNominalSharedSupport.Models state facts model :=
  GeneralNominalSettledSupport.all_models (trusted_old trusted) model (reachable_all_models path model valid)

theorem trusted_inhabited
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (trusted : Trusted state facts readbacks)
    (inhabited : ∃ model, GeneralNominalSaturationState.Models state.current model) :
    ∃ model, GeneralNominalSharedSupport.Models state facts model := by
  obtain ⟨model,valid⟩ := inhabited
  exact ⟨model,reachable_trusted_models path trusted model valid⟩

theorem output_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet support, Fact.outputs packet support ∈ state.facts →
      packet.declaration ∈ registry.declarations ∧
      packet.context.state.constructors = context.state.constructors ∧
      packet.context.interpretation = context.interpretation := by
  induction path with
  | refl => intro packet support member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => exact ih
    | merge first last dependencies one two same novel guard =>
      intro packet support member
      change Fact.outputs packet support ∈
        GeneralNominalSupportChoices.mergedFacts before first last ++ before.facts at member
      rcases List.mem_append.mp member with added | old
      · obtain ⟨dependencies,present,equal⟩ := List.mem_map.mp added
        cases equal
      · exact ih packet support old
    | install installed dependencies enabled novel guard =>
      intro packet support member
      change Fact.outputs packet support ∈
        GeneralNominalSupportChoices.installedFacts before installed ++ before.facts at member
      rcases List.mem_append.mp member with added | old
      · obtain ⟨dependencies,present,member⟩ := List.mem_flatMap.mp added
        rcases List.mem_cons.mp member with impossible | member
        · cases impossible
        · cases List.mem_singleton.mp member
          have config := GeneralNominalActualTraceSupport.configuration_trace path
          exact ⟨enabled.1.2.2.2.1,
            (congrArg (fun ctx : GeneralNominalCandidates.Context => ctx.state.constructors) enabled.1.2.1).trans config.2.1,
            (congrArg GeneralNominalCandidates.Context.interpretation enabled.1.2.1).trans config.2.2⟩
      · exact ih packet support old

theorem trusted_schemas
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (trusted : Trusted state facts readbacks) :
    GeneralNominalSettledLabelledLedger.Schemas facts
      (GeneralNominalSchemaVocabulary.registryVocabulary context registry) :=
  schemas context facts (fun packet support member => output_configuration path packet support
    (GeneralNominalSettledSupport.trusted_members (trusted_old trusted) _ member))

theorem reachable_promoted_output
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (trusted : Trusted state facts readbacks)
    (inputs : GeneralNominalSourceProducerHandoff.TrustedInputs state facts context origins
      remaining (keys registry) (GeneralNominalSchemaVocabulary.registryVocabulary context registry))
    (present : Fact.outputs packet support ∈ facts)
    (output : GeneralSourceState.Output) (member : output ∈ packet.site.occurrence.demand.outputs) :
    ∃ value : GeneralNominalLabelledOriginClosure.Value (GeneralNominalSharedSupport.Models state facts)
      context origins remaining (keys registry) (.source output.target),
      Vocabulary (GeneralNominalSchemaVocabulary.registryVocabulary context registry) value.term :=
  GeneralNominalSettledLabelledLedger.promoted_labelled trusted (trusted_schemas path trusted)
    (registry_templates context registry) inputs present output member

end Yulang.GeneralNominalReachableSchemas
