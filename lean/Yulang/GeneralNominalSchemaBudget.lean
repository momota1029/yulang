import Yulang.GeneralNominalRecipeBounds

/-! Uniform constructor budgets come from the real materialization producer.
Requested targets and repeated requests cannot increase this syntax bound. -/
namespace Yulang.GeneralNominalSchemaBudget
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalOriginTerms GeneralNominalRecipeBounds
open GeneralNominalInspection (Query)
open GeneralDeclarations GeneralDeclarationPatterns

mutual
  def cost : Query → Nat
    | .variables _ | .scalar _ | .deferred _ => 1
    | .node shape children => 1 + shape.arity + costs children
    | .nominal _ children => 1 + children.length + costs children
  def costs : List Query → Nat
    | [] => 0
    | first :: rest => cost first + costs rest
end

theorem cost_positive (query : Query) : 0 < cost query := by
  cases query <;> simp only [cost] <;> omega

mutual
  theorem schema_bound (query : Query) (root : Origin) (mode : Mode)
      (entry : Origin × Test) (member : entry ∈ (schema query root mode).tests) :
      level entry.1 < level root + cost query ∧ arity entry.2 < cost query := by
    cases query with
    | variables | deferred => simp only [schema] at member; cases member
    | scalar base =>
      simp only [schema] at member
      cases List.mem_singleton.mp member
      simp [cost,arity]
    | node shape children =>
      simp only [schema] at member
      rcases List.mem_cons.mp member with same | nested
      · cases same
        simp only [cost,arity]
        constructor <;> omega
      · have bound := schemas_bound children (fun index => .structural root shape index)
          mode 0 (level root+1) (fun _ => rfl) entry nested
        simp only [cost]
        constructor <;> omega
    | nominal name children =>
      simp only [schema] at member
      rcases List.mem_cons.mp member with same | nested
      · cases same
        simp only [cost,arity]
        constructor <;> omega
      · have bound := schemas_bound children (fun index => .nominal root name index)
          .actual 0 (level root+1) (fun _ => rfl) entry nested
        simp only [cost]
        constructor <;> omega
  termination_by sizeOf query

  theorem schemas_bound (queries : List Query) (origins : Nat → Origin) (mode : Mode) (index depth : Nat)
      (levels : ∀ index, level (origins index) = depth)
      (entry : Origin × Test) (member : entry ∈ (schemas queries origins mode index).tests) :
      level entry.1 < depth + costs queries ∧ arity entry.2 < costs queries := by
    cases queries with
    | nil => simp only [schemas] at member; cases member
    | cons query rest =>
      simp only [schemas,Schema.append] at member
      rcases List.mem_append.mp member with first | later
      · have bound := schema_bound query (origins index) mode entry first
        rw [levels] at bound
        simp only [costs]
        constructor <;> omega
      · have bound := schemas_bound rest origins mode (index+1) depth levels entry later
        simp only [costs]
        constructor <;> omega
  termination_by sizeOf queries
end

theorem generated_bound (state : GeneralNominalState.State) (interpretation : GeneralNominalInspection.Interpretation)
    (requests : List Request) (bound : ∀ request ∈ requests,
      cost (GeneralNominalInspection.translate state.constructors interpretation (normalize request.pattern)) ≤ limit)
    (entry : Origin × Test) (member : entry ∈ (generated state interpretation requests).tests) :
    level entry.1 < limit ∧ arity entry.2 < limit := by
  induction requests with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_append.mp member with here | later
    · have bounds := schema_bound (GeneralNominalInspection.translate state.constructors interpretation
        (normalize first.pattern)) (.source first.target) first.mode entry here
      have enough := bound first (List.mem_cons_self ..)
      simp only [level,Nat.zero_add] at bounds
      exact ⟨Nat.lt_of_lt_of_le bounds.1 enough,Nat.lt_of_lt_of_le bounds.2 enough⟩
    · exact ih (fun request present => bound request (List.mem_cons_of_mem _ present)) later

def menu (declaration : Declaration) : List Pattern :=
  declaration.associated.map Equation.rhs ++ declaration.requirements.flatMap fun clause =>
    clause.arguments.map normalize ++ clause.outputs.map Equation.rhs

theorem input_request_pattern (input : GeneralDeclarationDemands.InputRequest)
    (request : Request) (member : request ∈ inputRequests input) : request.pattern = normalize input.pattern := by
  unfold inputRequests at member
  split at member
  · cases member
  · rcases List.mem_cons.mp member with rfl | member
    · rfl
    · cases List.mem_singleton.mp member
      rfl

theorem request_menu (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bindings : GeneralNominalAllocation.Bindings) (request : Request)
    (member : request ∈ requests state registry root declaration checked bindings) :
    request.pattern ∈ menu declaration := by
  rcases List.mem_append.mp member with rootRequest | childRequest
  · obtain ⟨output,requested,present⟩ := List.mem_flatMap.mp rootRequest
    obtain ⟨equation,found,rfl⟩ := List.mem_map.mp present
    have found : declaration.associated.find? (fun equation => equation.name == output.name) = some equation := by
      simpa only [Option.mem_toList] using found
    exact List.mem_append_left _ (List.mem_map.mpr ⟨equation,List.mem_of_find?_eq_some found,rfl⟩)
  · obtain ⟨emission,emitted,member⟩ := List.mem_flatMap.mp childRequest
    have old := (GeneralCanonicalChildOrder.canonicalEmit_perm root.identity declaration checked _ _).mem_iff.mpr emitted
    unfold GeneralDeclarationDemands.emitAll at old
    obtain ⟨clause,_,same⟩ := List.mem_map.mp old
    cases same
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨clause.val,clause.property,?_⟩
    rcases List.mem_append.mp member with input | output
    · obtain ⟨entry,present,member⟩ := List.mem_flatMap.mp input
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
      rw [input_request_pattern _ request member]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_,List.getElem_mem _,rfl⟩)
    · obtain ⟨output,present,rfl⟩ := List.mem_map.mp output
      obtain ⟨equation,equationMember,same⟩ := List.mem_map.mp present
      cases same
      exact List.mem_append_right _ (List.mem_map.mpr ⟨equation,equationMember,rfl⟩)

def declarationBudget (context : GeneralNominalCandidates.Context) (declaration : Declaration) : Nat :=
  (menu declaration).foldr (fun pattern rest =>
    max (cost (GeneralNominalInspection.translate context.state.constructors context.interpretation (normalize pattern))) rest) 1

theorem menu_bounded (member : pattern ∈ menu declaration) :
    cost (GeneralNominalInspection.translate context.state.constructors context.interpretation (normalize pattern)) ≤
      declarationBudget context declaration := by
  have general (patterns : List Pattern) (member : pattern ∈ patterns) :
      cost (GeneralNominalInspection.translate context.state.constructors context.interpretation (normalize pattern)) ≤
        patterns.foldr (fun pattern rest =>
          max (cost (GeneralNominalInspection.translate context.state.constructors context.interpretation (normalize pattern))) rest) 1 := by
    induction patterns with
    | nil => cases member
    | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih member) (Nat.le_max_right ..)
  exact general _ member

theorem packet_tests (packet : GeneralNominalSaturationState.Packet roles)
    (entry : Origin × Test) (member : entry ∈ (GeneralNominalPacketSupport.namedSchema packet).tests) :
    level entry.1 < declarationBudget packet.context packet.declaration ∧
      arity entry.2 < declarationBudget packet.context packet.declaration := by
  apply generated_bound packet.context.state packet.context.interpretation _ ?_ entry member
  intro request present
  exact menu_bounded (request_menu packet.context.state packet.registry packet.site.occurrence
    packet.declaration packet.checked packet.bindings request present)

theorem ceiling_le (body : Schema) (bound : ∀ entry ∈ body.tests, level entry.1 < limit) : ceiling body ≤ limit := by
  have general (entries : List (Origin × Test)) (bound : ∀ entry ∈ entries, level entry.1 < limit) :
      entries.foldr (fun entry rest => max (level entry.1 + 1) rest) 0 ≤ limit := by
    induction entries with
    | nil => exact Nat.zero_le _
    | cons head tail ih =>
      exact Nat.max_le.mpr ⟨bound head (List.mem_cons_self ..),ih (fun entry member => bound entry (List.mem_cons_of_mem _ member))⟩
  exact general _ bound

theorem packet_recipe (packet : GeneralNominalSaturationState.Packet roles)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema packet) root term) :
    GeneralNominalSharedEnumeration.Bounded
      ((GeneralNominalPacketSupport.namedSchema packet).variables.map Use.name)
      ((GeneralNominalPacketSupport.namedSchema packet).tests.map Prod.snd)
      (declarationBudget packet.context packet.declaration) term :=
  GeneralNominalSharedEnumeration.bounded_mono (recipe_bounded recipe _ (by
    intro entry member
    have bound := test_below member
    omega)) (ceiling_le _ (fun entry member => (packet_tests packet entry member).1))

theorem packet_recipe_weight (packet : GeneralNominalSaturationState.Packet roles)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema packet) root term) :
    weight term ≤ treeBound (declarationBudget packet.context packet.declaration)
      (declarationBudget packet.context packet.declaration) := by
  apply weight_bounded (packet_recipe packet recipe)
  intro test member
  obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
  exact Nat.le_of_lt (packet_tests packet entry present).2


def registryBudget (context : GeneralNominalCandidates.Context) (registry : Registry) : Nat :=
  registry.declarations.foldr (fun declaration rest => max (declarationBudget context declaration) rest) 1

theorem declaration_le_registry (visible : declaration ∈ registry.declarations) :
    declarationBudget context declaration ≤ registryBudget context registry := by
  have general (declarations : List Declaration) (member : declaration ∈ declarations) :
      declarationBudget context declaration ≤ declarations.foldr
        (fun declaration rest => max (declarationBudget context declaration) rest) 1 := by
    induction declarations with
    | nil => cases member
    | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih member) (Nat.le_max_right ..)
  exact general _ visible

theorem registry_positive (context : GeneralNominalCandidates.Context) (registry : Registry) :
    0 < registryBudget context registry := by
  have general (declarations : List Declaration) : 0 < declarations.foldr
      (fun declaration rest => max (declarationBudget context declaration) rest) 1 := by
    induction declarations with
    | nil => exact Nat.zero_lt_one
    | cons head tail ih => exact Nat.lt_of_lt_of_le ih (Nat.le_max_right ..)
  exact general _

theorem declaration_context (first last : GeneralNominalCandidates.Context)
    (constructors : first.state.constructors = last.state.constructors)
    (interpretation : first.interpretation = last.interpretation) (declaration : Declaration) :
    declarationBudget first declaration = declarationBudget last declaration := by
  simp only [declarationBudget,constructors,interpretation]

theorem uniform_packet_recipe (context : GeneralNominalCandidates.Context)
    (packet : GeneralNominalSaturationState.Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema packet) root term) :
    GeneralNominalSharedEnumeration.Bounded
      ((GeneralNominalPacketSupport.namedSchema packet).variables.map Use.name)
      ((GeneralNominalPacketSupport.namedSchema packet).tests.map Prod.snd)
      (registryBudget context registry) term := by
  apply GeneralNominalSharedEnumeration.bounded_mono (packet_recipe packet recipe)
  rw [declaration_context packet.context context constructors interpretation]
  exact declaration_le_registry visible

theorem uniform_packet_weight (context : GeneralNominalCandidates.Context)
    (packet : GeneralNominalSaturationState.Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema packet) root term) :
    weight term ≤ treeBound (registryBudget context registry) (registryBudget context registry) := by
  apply weight_bounded (uniform_packet_recipe context packet visible constructors interpretation recipe)
  intro test member
  obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
  have bounded := Nat.le_of_lt (packet_tests packet entry present).2
  rw [declaration_context packet.context context constructors interpretation] at bounded
  exact Nat.le_trans bounded (declaration_le_registry visible)

end Yulang.GeneralNominalSchemaBudget
