import Yulang.GeneralNominalSchemaBudget

/-! Test names and constructor shapes of actual output materialization come
from one finite registry vocabulary, independently of allocation identities. -/
namespace Yulang.GeneralNominalSchemaVocabulary
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalSchemaBudget GeneralDeclarations GeneralDeclarationPatterns
open GeneralNominalInspection (Query)

mutual
  def vocabulary : Query → List Test
    | .variables _ | .deferred _ => []
    | .scalar base => [.scalar base]
    | .node shape children => .structural shape :: vocabularies children
    | .nominal name children => .nominal name children.length :: vocabularies children
  def vocabularies : List Query → List Test
    | [] => []
    | first :: rest => vocabulary first ++ vocabularies rest
end

mutual
  theorem schema_vocabulary (query : Query) (root : Origin) (mode : Mode) :
      (schema query root mode).tests.map Prod.snd = vocabulary query := by
    cases query with
    | variables | deferred | scalar => simp [schema,vocabulary]
    | node shape children =>
      simp only [schema,List.map_cons,vocabulary]
      rw [schemas_vocabulary]
    | nominal name children =>
      simp only [schema,List.map_cons,vocabulary]
      rw [schemas_vocabulary]
  termination_by sizeOf query

  theorem schemas_vocabulary (queries : List Query) (origins : Nat → Origin) (mode : Mode) (index : Nat) :
      (schemas queries origins mode index).tests.map Prod.snd = vocabularies queries := by
    cases queries with
    | nil => simp [schemas,vocabularies]
    | cons first rest =>
      simp only [schemas,Schema.append,List.map_append,vocabularies]
      rw [schema_vocabulary,schemas_vocabulary]
  termination_by sizeOf queries
end

theorem generated_vocabulary (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request) :
    (generated state interpretation requests).tests.map Prod.snd = requests.flatMap
      (fun request => vocabulary (GeneralNominalInspection.translate state.constructors interpretation (normalize request.pattern))) := by
  induction requests with
  | nil => rfl
  | cons first rest ih =>
    simp only [generated,List.map_cons,List.foldr_cons,Schema.append,List.map_append,List.flatMap_cons]
    rw [schema_vocabulary]
    exact congrArg (List.append _) ih

def registryVocabulary (context : GeneralNominalCandidates.Context) (registry : Registry) : List Test :=
  registry.declarations.flatMap fun declaration => (menu declaration).flatMap fun pattern =>
    vocabulary (GeneralNominalInspection.translate context.state.constructors context.interpretation (normalize pattern))

theorem packet_vocabulary (context : GeneralNominalCandidates.Context)
    (packet : GeneralNominalSaturationState.Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation) :
    (GeneralNominalPacketSupport.namedSchema packet).tests.map Prod.snd ⊆ registryVocabulary context registry := by
  intro test member
  change test ∈ (generated packet.context.state packet.context.interpretation _).tests.map Prod.snd at member
  rw [generated_vocabulary] at member
  obtain ⟨request,present,member⟩ := List.mem_flatMap.mp member
  apply List.mem_flatMap.mpr
  refine ⟨packet.declaration,visible,List.mem_flatMap.mpr ⟨request.pattern,?_,?_⟩⟩
  · exact request_menu packet.context.state packet.registry packet.site.occurrence packet.declaration packet.checked packet.bindings request present
  · simpa only [constructors,interpretation] using member

theorem recipe_vocabulary (context : GeneralNominalCandidates.Context)
    (packet : GeneralNominalSaturationState.Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (recipe : GeneralNominalOriginTerms.Recipe (GeneralNominalPacketSupport.namedSchema packet) root term) :
    GeneralNominalSharedEnumeration.Bounded
      ((GeneralNominalPacketSupport.namedSchema packet).variables.map Use.name)
      (registryVocabulary context registry) (registryBudget context registry) term := by
  have bounded := uniform_packet_recipe context packet visible constructors interpretation recipe
  have included := packet_vocabulary context packet visible constructors interpretation
  clear recipe
  generalize registryBudget context registry = depth at bounded ⊢
  induction bounded with
  | leaf name depth member => exact .leaf name depth member
  | node test children member bounded ih => exact .node test children (included member) ih

end Yulang.GeneralNominalSchemaVocabulary
