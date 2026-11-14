import Yulang.GeneralNominalCenteredHeadMatSchemas
import Yulang.GeneralNominalCenteredHeadDefaultSchemas

set_option backward.isDefEq.respectTransparency false

/-! Class effects compile explicit bodies and role defaults through the same
constructor interpretation. Defaults retain positional centers, whereas an
explicit body retains the implementation's shared binder identities. -/
namespace Yulang.GeneralNominalCenteredHeadMatEffects
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs GeneralDictionaryAssociatedProvenance
open GeneralNominalCenteredHeadMatExpressions
open GeneralNominalCenteredHeadMatSchemas (Schema Equation)
open GeneralNominalCenteredHeadWFSource
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}

def variables (plan : Plan roles) (model : Assignment) (mode : Mode) (name : Nat) : Ty :=
  if name ∈ plan.packet.declaration.outputNames then (model (plan.binder name)).1
  else match mode with
    | .actual => (model (plan.binder name)).1
    | .lower => (model ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1).1
    | .upper => (model ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2).1

def defaultVariables (plan : Plan roles) (model : Assignment) (_mode : Mode) (index : Nat) : Ty :=
  (model ((List.ofFn plan.input.center)[index]?.getD 0)).1

def compileBody (plan : Plan roles) : Body → Option Expr
  | .explicit equation => translate plan.packet.registry.constructors plan.packet.context.interpretation equation.rhs
  | .default _ _ term => translateDefault plan.packet.registry.constructors plan.packet.context.interpretation term

def bodySchema (plan : Plan roles) (target : Nat) (body : Body) : Schema :=
  match compileBody plan body with
  | some expression => ⟨[⟨target,.actual,expression⟩],false⟩
  | none => ⟨[],true⟩

def bodyVariables (plan : Plan roles) (model : Assignment) : Body → Mode → Nat → Ty
  | .explicit _ => variables plan model
  | .default _ _ _ => defaultVariables plan model

def BodyHolds (plan : Plan roles) (target : Nat) (model : Assignment) (body : Body) : Prop :=
  (bodySchema plan target body).Holds (bodyVariables plan model body) model

def Ready (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) (plan : Plan roles) : Prop :=
  ∀ output ∈ requests state root, ∃ body, lookup roles plan.packet.declaration output.name = some body ∧
    (bodySchema plan output.target body).unknown = false

def ClassEffects (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (plan : Plan roles) (model : Assignment) : Prop :=
  (∀ output ∈ requests state root, ∀ body, lookup roles plan.packet.declaration output.name = some body →
    BodyHolds plan output.target model body) ∧ EqualOutputs state root model

variable {plan : Plan roles} {model : Assignment}
variable {state before after : GeneralNominalCenteredSteps.State roles} {root : Occurrence roles}

theorem compile_body_complete
    (covered : DeclarationCovered plan.packet.registry.constructors plan.packet.context.interpretation plan.packet.declaration)
    (defaults : DefaultsCovered plan.packet.registry.constructors plan.packet.context.interpretation roles)
    (supplied : Supplies roles plan.packet.declaration name body) :
    ∃ expression, compileBody plan body = some expression := by
  cases supplied with
  | explicit equation present _ => exact translate_complete (covered.2.2 equation present)
  | default term _ declared => exact translateDefault_complete (defaults _ _ term declared)

theorem body_schema_complete
    (covered : DeclarationCovered plan.packet.registry.constructors plan.packet.context.interpretation plan.packet.declaration)
    (defaults : DefaultsCovered plan.packet.registry.constructors plan.packet.context.interpretation roles)
    (supplied : Supplies roles plan.packet.declaration name body) :
    (bodySchema plan target body).unknown = false := by
  obtain ⟨expression,translated⟩ := compile_body_complete covered defaults supplied
  simp [bodySchema,translated]

theorem ready_of_coverage
    (covered : DeclarationCovered plan.packet.registry.constructors plan.packet.context.interpretation plan.packet.declaration)
    (defaults : DefaultsCovered plan.packet.registry.constructors plan.packet.context.interpretation roles)
    (declared : GeneralNominalCenteredHeadDefaultSchemas.RequestsDeclared state root plan) : Ready state root plan := by
  intro output member
  obtain ⟨body,supplied⟩ := declared_covered roles plan.packet.declaration plan.packet.checked.signature
    output.name (declared output member)
  exact ⟨body,(lookup_exact roles plan.packet.declaration plan.packet.checked.identified.2.2.1 _ _).mpr supplied,
    body_schema_complete covered defaults supplied⟩

theorem ready_of_wf
    (covered : Coverage plan.packet.registry plan.packet.context.interpretation)
    (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
    (agree : plan.packet.registry.roles = roles)
    (declared : GeneralNominalCenteredHeadDefaultSchemas.RequestsDeclared state root plan) : Ready state root plan := by
  apply ready_of_coverage (covered.1 _ visible) _ declared
  exact Eq.mp (congrArg (DefaultsCovered plan.packet.registry.constructors plan.packet.context.interpretation) agree) covered.2

theorem body_equation (translated : compileBody plan body = some expression) :
    BodyHolds plan target model body ↔
      Equivalent (model target).1 (value (bodyVariables plan model body) .actual expression) := by
  simp [BodyHolds,bodySchema,translated,Schema.Holds,Equation.Holds]

theorem positional_default (plan : Plan roles) (model : Assignment)
    (index : Fin (roles plan.input.occurrence.demand.role).arity) :
    BodyHolds plan target model (.default role name (.var index.val)) ↔
      Equivalent (model target).1 (model (plan.input.center index)).1 := by
  simp [BodyHolds,bodySchema,compileBody,translateDefault,Schema.Holds,Equation.Holds,
    value,bodyVariables,defaultVariables,index.isLt]

theorem restrict (subset : requests before root ⊆ requests after root)
    (valid : ClassEffects after root plan model) : ClassEffects before root plan model :=
  ⟨fun output member body found => valid.1 output (subset member) body found,
    fun a one b two named => valid.2 a (subset one) b (subset two) named⟩

theorem ready_restrict (subset : requests before root ⊆ requests after root)
    (ready : Ready after root plan) : Ready before root plan :=
  fun output member => ready output (subset member)

theorem actual_variable (plan : Plan roles) (model : Assignment) (name : Nat) :
    variables plan model .actual name = (model (plan.binder name)).1 := by
  unfold variables
  by_cases member : name ∈ plan.packet.declaration.outputNames <;> simp [member]

end Yulang.GeneralNominalCenteredHeadMatEffects
