import Yulang.GeneralNominalRequestCanonical

/-! One finite source-key menu supplies all actual materialization templates.
No coverage condition is imposed on raw associated right-hand sides. -/
namespace Yulang.GeneralNominalRegistrySourceTemplates
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalMaterialization
open GeneralNominalSchemaBudget GeneralNominalSchemaVocabulary
open GeneralNominalSourceLabelVocabulary GeneralNominalScopedRecipeLabels
open GeneralNominalReadbackFunctionality GeneralNominalSaturationState GeneralNominalSupport
open GeneralNominalSettledLabelledLedger

def patterns (registry : Registry) : List Pattern :=
  registry.declarations.flatMap fun declaration => (menu declaration).map normalize

def keys (registry : Registry) : List Nat := collectArgs (patterns registry)

theorem menu_scoped (visible : declaration ∈ registry.declarations) (member : pattern ∈ menu declaration) :
    Scoped (keys registry) (normalize pattern) :=
  collect_args_scoped _ _ (List.mem_flatMap.mpr ⟨declaration,visible,List.mem_map.mpr ⟨pattern,member,rfl⟩⟩)

theorem registry_templates (context : GeneralNominalCandidates.Context) (registry : Registry) :
    NodeTemplates context (keys registry) (registryVocabulary context registry) := by
  intro test member canonical
  obtain ⟨declaration,visible,member⟩ := List.mem_flatMap.mp member
  obtain ⟨pattern,present,member⟩ := List.mem_flatMap.mp member
  exact GeneralNominalRequestTemplates.source_templates context _ (menu_scoped visible present) test member canonical

theorem registry_canonical (context : GeneralNominalCandidates.Context) (registry : Registry) :
    ∀ test ∈ registryVocabulary context registry, TestCanonical test := by
  intro test member
  obtain ⟨declaration,visible,member⟩ := List.mem_flatMap.mp member
  obtain ⟨pattern,present,member⟩ := List.mem_flatMap.mp member
  exact GeneralNominalRequestCanonical.translated_canonical _
    (GeneralNominalRequestCanonical.normalized_tidy pattern) test member

theorem request_scoped (packet : Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (request : Request)
    (member : request ∈ requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings) :
    Scoped (keys registry) (normalize request.pattern) :=
  menu_scoped visible (request_menu packet.context.state packet.registry packet.site.occurrence
    packet.declaration packet.checked packet.bindings request member)

theorem packet_canonical (packet : Packet roles) :
    ∀ entry ∈ (GeneralNominalPacketSupport.namedSchema packet).tests, TestCanonical entry.2 :=
  GeneralNominalRequestCanonical.request_canonical packet.context _

theorem packet_templates (context : GeneralNominalCandidates.Context)
    (packet : Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation) :
    NodeTemplates context (keys registry) ((GeneralNominalPacketSupport.namedSchema packet).tests.map Prod.snd) :=
  fun test member canonical => registry_templates context registry test
    (packet_vocabulary context packet visible constructors interpretation member) canonical

theorem schemas (context : GeneralNominalCandidates.Context) (facts : List (Fact roles))
    (packets : ∀ packet support, Fact.outputs packet support ∈ facts →
      packet.declaration ∈ registry.declarations ∧
      packet.context.state.constructors = context.state.constructors ∧
      packet.context.interpretation = context.interpretation) :
    Schemas facts (registryVocabulary context registry) := by
  intro packet support member entry present
  obtain ⟨visible,constructors,interpretation⟩ := packets packet support member
  exact ⟨packet_canonical packet entry present,
    packet_vocabulary context packet visible constructors interpretation (List.mem_map.mpr ⟨entry,present,rfl⟩)⟩

theorem promoted_output (context : GeneralNominalCandidates.Context)
    (trusted : GeneralNominalSharedSupport.Trusted state facts readbacks)
    (packets : ∀ packet support, Fact.outputs packet support ∈ facts →
      packet.declaration ∈ registry.declarations ∧
      packet.context.state.constructors = context.state.constructors ∧
      packet.context.interpretation = context.interpretation)
    (inputs : GeneralNominalSourceProducerHandoff.TrustedInputs state facts context origins
      remaining (keys registry) (registryVocabulary context registry))
    (present : Fact.outputs packet support ∈ facts)
    (output : GeneralSourceState.Output) (member : output ∈ packet.site.occurrence.demand.outputs) :
    ∃ value : GeneralNominalLabelledOriginClosure.Value
      (GeneralNominalSharedSupport.Models state facts) context origins remaining (keys registry)
      (.source output.target), Vocabulary (registryVocabulary context registry) value.term :=
  promoted_labelled trusted (schemas context facts packets) (registry_templates context registry) inputs present output member

end Yulang.GeneralNominalRegistrySourceTemplates
