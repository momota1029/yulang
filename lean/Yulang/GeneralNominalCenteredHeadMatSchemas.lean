import Yulang.GeneralNominalCenteredHeadMatExpressions

namespace Yulang.GeneralNominalCenteredHeadMatSchemas
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadWFSource
open GeneralNominalMaterialization (Mode Request)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {model : Assignment}

structure Equation where
  target : Nat
  mode : Mode
  expression : Expr

def Equation.Holds (variables : Mode → Nat → Ty) (model : Assignment) (equation : Equation) : Prop :=
  Equivalent (model equation.target).1 (value variables equation.mode equation.expression)

structure Schema where
  equations : List Equation := []
  unknown : Bool := false

def Schema.append (first last : Schema) : Schema :=
  ⟨first.equations ++ last.equations,first.unknown || last.unknown⟩

def Schema.Holds (schema : Schema) (variables : Mode → Nat → Ty) (model : Assignment) : Prop :=
  ∀ equation ∈ schema.equations, equation.Holds variables model

def materialize (catalogue : Constructors) (interpretation : Interpretation) (request : Request) : Schema :=
  match translate catalogue interpretation request.pattern with
  | some expression => ⟨[⟨request.target,request.mode,expression⟩],false⟩
  | none => ⟨[],true⟩

def generated (catalogue : Constructors) (interpretation : Interpretation) : List Request → Schema
  | [] => {}
  | first :: rest => (materialize catalogue interpretation first).append (generated catalogue interpretation rest)

def RequestsCovered (catalogue : Constructors) (interpretation : Interpretation) (requests : List Request) : Prop :=
  ∀ request ∈ requests, PatternCovered catalogue interpretation request.pattern

theorem materialize_complete (covered : PatternCovered catalogue interpretation request.pattern) :
    (materialize catalogue interpretation request).unknown = false := by
  obtain ⟨expression,translated⟩ := translate_complete covered
  simp [materialize,translated]

theorem generated_complete (covered : RequestsCovered catalogue interpretation requests) :
    (generated catalogue interpretation requests).unknown = false := by
  induction requests with
  | nil => rfl
  | cons first rest ih =>
      exact Bool.or_eq_false_iff.mpr ⟨materialize_complete (covered first (by simp)),
        ih (fun request member => covered request (List.mem_cons_of_mem _ member))⟩

theorem generated_contains (member : request ∈ requests)
    (translated : translate catalogue interpretation request.pattern = some expression) :
    (⟨request.target,request.mode,expression⟩ : Equation) ∈ (generated catalogue interpretation requests).equations := by
  induction requests with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | within
      · subst first
        exact List.mem_append_left _ (by simp [materialize,translated])
      · exact List.mem_append_right _ (ih within)

theorem generated_equation (holds : (generated catalogue interpretation requests).Holds variables model)
    (member : request ∈ requests)
    (translated : translate catalogue interpretation request.pattern = some expression) :
    Equivalent (model request.target).1 (value variables request.mode expression) :=
  holds _ (generated_contains member translated)

theorem append_holds : (Schema.append first last).Holds variables model ↔
    first.Holds variables model ∧ last.Holds variables model := by
  constructor
  · intro valid
    exact ⟨fun equation member => valid equation (List.mem_append_left _ member),
      fun equation member => valid equation (List.mem_append_right _ member)⟩
  · rintro ⟨first,last⟩ equation member
    exact (List.mem_append.mp member).elim (first equation) (last equation)

theorem ordinary_equations (equation : Equation) (variables model) :
    equation.Holds variables model ↔
      Subtype (model equation.target).1 (value variables equation.mode equation.expression) ∧
      Subtype (value variables equation.mode equation.expression) (model equation.target).1 := Iff.rfl

/-! Endpoint requests retain the source pattern, including open record tails.
Bare variables yield harmless endpoint equalities rather than being omitted. -/
def inputRequests (input : InputRequest) : List Request :=
  [⟨input.pattern,input.endpoints.1,.lower⟩,⟨input.pattern,input.endpoints.2,.upper⟩]

def emissionRequests (emission : Emission roles) : List Request :=
  emission.inputs.flatMap inputRequests ++
    emission.outputs.map (fun output => ⟨output.pattern,output.target,.actual⟩)

def requests (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bindings : GeneralNominalAllocation.Bindings) : List Request :=
  GeneralNominalMaterialization.rootRequests declaration root ++
    (GeneralCanonicalChildOrder.canonicalEmit root.identity declaration checked
      (GeneralNominalAllocation.capture state registry root.identity declaration.id bindings)
      (GeneralNominalAllocation.allocation state registry root.identity declaration.id)).flatMap emissionRequests

theorem patterns_member (covered : PatternsCovered catalogue interpretation patterns) (member : pattern ∈ patterns) :
    PatternCovered catalogue interpretation pattern := by
  induction patterns with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | within
      · exact covered.1
      · exact ih covered.2 within

theorem emitted_covered {clause : Clause} {allocation : Allocation roles clause}
    (inputs : PatternsCovered catalogue interpretation clause.arguments)
    (outputs : ∀ equation ∈ clause.outputs, PatternCovered catalogue interpretation equation.rhs)
    (valid : clause.Signature roles) :
    RequestsCovered catalogue interpretation
      (emissionRequests (emit invocation declaration clause valid capture allocation)) := by
  intro request member
  rcases List.mem_append.mp member with input | output
  · obtain ⟨input,present,within⟩ := List.mem_flatMap.mp input
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
    have covered := patterns_member inputs
      (List.getElem_mem (l := clause.arguments) (n := index.val) (by rw [valid.1]; exact index.isLt))
    rcases List.mem_cons.mp within with rfl | within
    · exact covered
    · cases List.mem_singleton.mp within
      exact covered
  · obtain ⟨output,present,rfl⟩ := List.mem_map.mp output
    obtain ⟨equation,equationMember,rfl⟩ := List.mem_map.mp present
    exact outputs equation equationMember

theorem requests_covered (covered : DeclarationCovered registry.constructors interpretation declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) :
    RequestsCovered registry.constructors interpretation (requests state registry root declaration checked bindings) := by
  intro request member
  rcases List.mem_append.mp member with rootRequest | emitted
  · obtain ⟨output,_,within⟩ := List.mem_flatMap.mp rootRequest
    obtain ⟨equation,found,rfl⟩ := List.mem_map.mp within
    exact covered.2.2 equation (List.mem_of_find?_eq_some (Option.mem_toList.mp found))
  · obtain ⟨emission,present,within⟩ := List.mem_flatMap.mp emitted
    have perm := GeneralCanonicalChildOrder.canonicalEmit_perm root.identity declaration checked
      (GeneralNominalAllocation.capture state registry root.identity declaration.id bindings)
      (GeneralNominalAllocation.allocation state registry root.identity declaration.id)
    obtain ⟨clause,_,equal⟩ := List.mem_map.mp (perm.mem_iff.mpr present)
    subst emission
    exact emitted_covered (covered.2.1 clause.val clause.property).1
      (covered.2.1 clause.val clause.property).2 _ request within

theorem emitted_schema_complete (covered : DeclarationCovered registry.constructors interpretation declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) :
    (generated registry.constructors interpretation (requests state registry root declaration checked bindings)).unknown = false :=
  generated_complete (requests_covered covered checked)

theorem wf_emitted_schema_complete (covered : Coverage registry interpretation)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration) :
    (generated registry.constructors interpretation (requests state registry root declaration checked bindings)).unknown = false :=
  emitted_schema_complete (covered.1 declaration visible) checked

end Yulang.GeneralNominalCenteredHeadMatSchemas
