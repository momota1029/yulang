import Yulang.GeneralNominalCenteredHeadStepDefaults

set_option backward.isDefEq.respectTransparency false

/-! Default equations use positional input centers. Constructor interpretation
is an explicit source-elaboration parameter: Roles.Term constructor numbers
are not decoded through the unrelated counting encoding of general patterns.
This interface adds no diagnostic or deferral rule. -/
namespace Yulang.GeneralNominalCenteredHeadDefaultSchemas
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs
open GeneralDictionaryAssociatedProvenance
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

abbrev ConstructorMeaning := Nat → List Ty → Ty

mutual
  def value (constructors : ConstructorMeaning) (parameters : Nat → Ty) : Roles.Term → Ty
    | .var name => parameters name
    | .app name arguments => constructors name (values constructors parameters arguments)
  def values (constructors : ConstructorMeaning) (parameters : Nat → Ty) : List Roles.Term → List Ty
    | [] => []
    | term :: rest => value constructors parameters term :: values constructors parameters rest
end

def parameters (plan : Plan roles) (model : Assignment) (index : Nat) : Ty :=
  (model ((List.ofFn plan.input.center)[index]?.getD 0)).1

def DefaultEquation (constructors : ConstructorMeaning) (plan : Plan roles)
    (body : Roles.Term) (target : Nat) (model : Assignment) : Prop :=
  Equivalent (model target).1 (value constructors (parameters plan model) body)

theorem positional_parameter (plan : Plan roles) (model : Assignment)
    (index : Fin (roles plan.input.occurrence.demand.role).arity) :
    parameters plan model index.val = (model (plan.input.center index)).1 := by
  simp [parameters,index.isLt]

theorem positional_default (constructors : ConstructorMeaning) (plan : Plan roles) (target model)
    (index : Fin (roles plan.input.occurrence.demand.role).arity) :
    DefaultEquation constructors plan (.var index.val) target model ↔
      Equivalent (model target).1 (model (plan.input.center index)).1 := by
  simp only [DefaultEquation,value,positional_parameter]

def explicitSchema (plan : Plan roles) (equation : Equation) (target : Nat) : GeneralNominalMaterialization.Schema :=
  plan.schema [⟨equation.rhs,target,.actual⟩]

def BodyReady (plan : Plan roles) (target : Nat) : Body → Prop
  | .explicit equation => (explicitSchema plan equation target).unknown = false
  | .default _ _ _ => True

def BodyHolds (constructors : ConstructorMeaning) (plan : Plan roles) (target : Nat) (model : Assignment) : Body → Prop
  | .explicit equation => plan.SchemaHolds (explicitSchema plan equation target) model
  | .default _ _ term => DefaultEquation constructors plan term target model

def RequestsDeclared (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (plan : Plan roles) : Prop :=
  ∀ output ∈ requests state root, ∃ body, (roles plan.packet.declaration.role).assoc output.name = some body

def Ready (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) (plan : Plan roles) : Prop :=
  ∀ output ∈ requests state root, ∃ body,
    lookup roles plan.packet.declaration output.name = some body ∧ BodyReady plan output.target body

def Equations (constructors : ConstructorMeaning) (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles) (model : Assignment) : Prop :=
  (∀ output ∈ requests state root, ∀ body, lookup roles plan.packet.declaration output.name = some body →
    BodyHolds constructors plan output.target model body) ∧ EqualOutputs state root model

variable {state before after : GeneralNominalCenteredSteps.State roles} {root : Occurrence roles}
variable {plan : Plan roles} {model : Assignment}

theorem ready_of_coverage (declared : RequestsDeclared state root plan)
    (explicit : ∀ output ∈ requests state root, ∀ equation ∈ plan.packet.declaration.associated,
      equation.name = output.name → (explicitSchema plan equation output.target).unknown = false) : Ready state root plan := by
  intro output member
  obtain ⟨body,supplied⟩ := declared_covered roles plan.packet.declaration plan.packet.checked.signature
    output.name (declared output member)
  refine ⟨body,(lookup_exact roles plan.packet.declaration plan.packet.checked.identified.2.2.1 output.name body).mpr supplied,?_⟩
  cases supplied with
  | explicit equation present named => exact explicit output member equation present named
  | default => trivial

theorem default_scoped (supplied : Supplies roles plan.packet.declaration name (.default role name body)) :
    body.bound ≤ (roles plan.packet.declaration.role).arity := by
  cases supplied with
  | default term absent declared => exact (roles plan.packet.declaration.role).defaultsScoped name body declared

theorem equations_default (valid : Equations constructors state root plan model)
    (member : output ∈ requests state root)
    (supplied : Supplies roles plan.packet.declaration output.name (.default role output.name body)) :
    DefaultEquation constructors plan body output.target model :=
  valid.1 output member _ ((lookup_exact roles plan.packet.declaration
    plan.packet.checked.identified.2.2.1 output.name _).mpr supplied)

theorem restrict (subset : requests before root ⊆ requests after root)
    (valid : Equations constructors after root plan model) : Equations constructors before root plan model :=
  ⟨fun output member body found => valid.1 output (subset member) body found,
    fun a one b two named => valid.2 a (subset one) b (subset two) named⟩

theorem ready_restrict (subset : requests before root ⊆ requests after root)
    (valid : Ready after root plan) : Ready before root plan :=
  fun output member => valid output (subset member)

theorem default_has_no_schema_deferral (plan : Plan roles) (role name body target) :
    BodyReady plan target (.default role name body) := trivial

namespace Example
open GeneralNominalCenteredHeadStepDefaults
abbrev demand := GeneralNominalCenteredHeadStepDefaults.root

abbrev packet : GeneralNominalSaturationState.Packet GeneralNominalCenteredHeadStepDefaults.roles :=
  ⟨registry,GeneralNominalExamples.context true,GeneralNominalDemandMerging.pointSite demand,
    declaration,declaration_checked,[(1,1)]⟩

abbrev examplePlan : Plan GeneralNominalCenteredHeadStepDefaults.roles :=
  ⟨packet,rootSite (GeneralNominalExamples.state true).seed demand,rfl⟩

theorem request_eq (member : output ∈ requests start.core demand) : output = ⟨0,1⟩ := by
  obtain ⟨site,present,_,within⟩ := mem_requests_iff.mp member
  have one : site = GeneralNominalDemandMerging.pointSite demand := List.mem_singleton.mp present
  rw [one] at within
  exact List.mem_singleton.mp within

theorem ready : Ready start.core demand examplePlan := by
  intro output member
  cases request_eq member
  exact ⟨.default 0 0 (.var 0),rfl,trivial⟩

theorem equations (constructors : ConstructorMeaning) :
    Equations constructors start.core demand examplePlan GeneralNominalExamples.model := by
  constructor
  · intro output member body found
    cases request_eq member
    have equal : body = .default 0 0 (.var 0) := (Option.some.inj found).symm
    subst body
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _
    cases request_eq one
    cases request_eq two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem inhabited_effects (constructors : ConstructorMeaning) :
    GeneralNominalCenteredHeadStepEffects.Models start GeneralNominalExamples.model ∧
      Equations constructors start.core demand examplePlan GeneralNominalExamples.model :=
  ⟨inhabited,equations constructors⟩

theorem old_ready_fails : ¬ EffectsReady start.core demand examplePlan := no_ready examplePlan (List.mem_singleton_self _)

end Example

end Yulang.GeneralNominalCenteredHeadDefaultSchemas
