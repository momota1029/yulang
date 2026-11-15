import Yulang.GeneralDictionaryMatTerminalAssembly200

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryMatInputVariables201
open GeneralDeclarations GeneralDeclarationDemands GeneralDeclarationPatterns
open GeneralNominalCenters GeneralNominalCenteredHeadMatSchemas GeneralNominalCenteredHeadMatEffects
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem generated_request_holds (catalogue interpretation requests variables model)
    (holds : (generated catalogue interpretation requests).Holds variables model)
    (request : GeneralNominalMaterialization.Request) (member : request ∈ requests) :
    (materialize catalogue interpretation request).Holds variables model := by
  induction requests with
  | nil => cases member
  | cons first rest ih =>
    have both := append_holds.mp holds
    rcases List.mem_cons.mp member with rfl | within
    · exact both.1
    · exact ih both.2 within

/-- Literal input binders only; requirements may repeat and be nonempty. -/
def InputVariableClauses (declaration : Declaration) : Prop :=
  ∀ clause ∈ declaration.requirements, clause.outputs = [] ∧
    ∀ pattern ∈ clause.arguments, ∃ name, pattern = .var name ∧
      name ∈ declaration.inputNames ∧ name ∉ declaration.outputNames

theorem variable_clauses (restricted : InputVariableClauses declaration) :
    GeneralDictionaryVariableRequirements.VariableClauses declaration := by
  intro clause member
  refine ⟨(restricted clause member).1,?_⟩
  intro pattern present
  obtain ⟨name,rfl,_,_⟩ := (restricted clause member).2 pattern present
  exact ⟨name,rfl⟩

theorem normalized_names (patterns : List Pattern) (names : List Nat)
    (inputs : ∀ pattern ∈ patterns, ∃ name, pattern = .var name ∧ name ∈ names) :
    ∀ name ∈ variablesArgs (normalizeArgs patterns), name ∈ names := by
  induction patterns with
  | nil => simp [normalizeArgs,variablesArgs]
  | cons first rest ih =>
    obtain ⟨name,rfl,member⟩ := inputs first (List.mem_cons_self)
    intro other present
    simp only [normalizeArgs,normalize,variablesArgs,Pattern.variables,List.singleton_append,List.mem_cons] at present
    exact present.elim (fun equal => equal ▸ member)
      (ih (fun pattern within => inputs pattern (List.mem_cons_of_mem _ within)) other)

variable {roles : Roles.RoleDecls} (plan : Plan roles) (model : Assignment)

theorem needed_input (restricted : InputVariableClauses plan.packet.declaration)
    (name : Nat) (needed : GeneralNominalSharedCaptures.Needed plan.packet name) :
    name ∈ plan.packet.declaration.inputNames := by
  obtain ⟨clause,member,used⟩ := needed
  exact normalized_names clause.arguments plan.packet.declaration.inputNames
    (fun pattern present => by
      obtain ⟨name,equal,input,_⟩ := (restricted clause member).2 pattern present
      exact ⟨name,equal,input⟩) name used

theorem variable_endpoints (name : Nat) (notOutput : name ∉ plan.packet.declaration.outputNames) :
    ∀ request ∈ inputRequests ⟨0,.var name,(GeneralNominalPacketSupport.capture plan.packet).inputs name⟩,
      (materialize plan.packet.registry.constructors plan.packet.context.interpretation request).Holds
        (variables plan model) model := by
  intro request member
  simp only [inputRequests,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;>
    simp [materialize,GeneralNominalCenteredHeadMatExpressions.translate,Schema.Holds,Equation.Holds,
      GeneralNominalCenteredHeadMatExpressions.value,variables,notOutput,Equivalent,subtype_refl]

theorem emission_holds (clause : Clause) (valid : clause.Signature roles)
    (outputs : clause.outputs = [])
    (inputs : ∀ pattern ∈ clause.arguments, ∃ name, pattern = .var name ∧ name ∉ plan.packet.declaration.outputNames) :
    ∀ request ∈ emissionRequests (emit plan.packet.site.occurrence.identity plan.packet.declaration clause valid
      (GeneralNominalPacketSupport.capture plan.packet)
      (GeneralNominalAllocation.allocation plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration.id clause)),
      (materialize plan.packet.registry.constructors plan.packet.context.interpretation request).Holds
        (variables plan model) model := by
  intro request member
  simp only [emissionRequests,emit,outputs,List.map_nil,List.append_nil] at member
  obtain ⟨input,present,within⟩ := List.mem_flatMap.mp member
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
  have bound : index.val < clause.arguments.length := by rw [valid.1]; exact index.isLt
  obtain ⟨name,equal,notOutput⟩ := inputs clause.arguments[index.val]
    (List.getElem_mem (l := clause.arguments) (n := index.val) (by rw [valid.1]; exact index.isLt))
  simpa only [childDemand,equal,inputInterval,normalize,inputRequests] using
    variable_endpoints plan model name notOutput request (by
      simpa only [childDemand,equal,inputInterval,normalize,inputRequests] using within)

theorem child_schema_holds (clause : Clause) (valid : clause.Signature roles)
    (inputs : ∀ pattern ∈ clause.arguments, ∃ name, pattern = .var name) :
    (GeneralNominalCenteredHeadMatPlans.childSchema plan clause valid).Holds (variables plan model) model := by
  apply GeneralDictionaryMatTerminalAssembly200.generated_holds
  intro request member
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  have bound : index.val < clause.arguments.length := by rw [valid.1]; exact index.isLt
  obtain ⟨name,equal⟩ := inputs clause.arguments[index.val] (List.getElem_mem bound)
  simp [Plan.childSite,Plan.emittedCenter,equal,normalize,materialize,
    GeneralNominalCenteredHeadMatExpressions.translate,Schema.Holds,Equation.Holds,
    GeneralNominalCenteredHeadMatExpressions.value,actual_variable,Equivalent,subtype_refl]

theorem child_site_holds (clause : Clause) (valid : clause.Signature roles)
    (inputs : ∀ pattern ∈ clause.arguments, ∃ name, pattern = .var name ∧ name ∈ plan.packet.declaration.inputNames)
    (head : GeneralNominalCenteredHeadOutputs.HeadEquations plan model) :
    (plan.childSite clause valid).Holds model := by
  intro index
  have bound : index.val < clause.arguments.length := by rw [valid.1]; exact index.isLt
  obtain ⟨name,equal,member⟩ := inputs clause.arguments[index.val] (List.getElem_mem bound)
  simpa only [Plan.childSite,Plan.emittedCenter,GeneralNominalFeedbackSites.clauseChild,
    GeneralDictionaryEmissionPlans.occurrence,emit,childDemand,inputInterval,equal,normalize,
    GeneralNominalFeedbackSites.frame,GeneralNominalAllocation.frame,GeneralNominalPacketSupport.capture]
    using head.2.1 name member

end Yulang.GeneralDictionaryMatInputVariables201
