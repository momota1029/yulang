import Yulang.GeneralNominalCenteredHeadMatPlans

set_option backward.isDefEq.respectTransparency false

/-! Input support excludes cached context models and named output equations.
Output support uses the total equation compiler. The full packet meaning is
exactly the prospective materialization meaning from the preceding turn. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepPackets
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatEffects (variables)
open GeneralNominalCenteredHeadMatPlans (emittedSchema childSchema)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : Assignment}

def Inputs (plan : Plan roles) (model : Assignment) : Prop :=
  GeneralNominalPacketSupport.Ordinary plan.packet model ∧
  GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state
    (GeneralNominalPacketSupport.report plan.packet) model ∧
  plan.input.Holds model ∧
  (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture plan.packet).inputs name)
      (model (plan.binder name)).1) ∧
  plan.SchemaHolds plan.headSchema model ∧
  (∀ equation ∈ (emittedSchema plan).equations, equation.mode ≠ .actual →
    equation.Holds (variables plan model) model) ∧
  ∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
    (plan.childSite clause valid).Holds model ∧ (childSchema plan clause valid).Holds (variables plan model) model

def Outputs (plan : Plan roles) (model : Assignment) : Prop :=
  (emittedSchema plan).Holds (variables plan model) model

def Holds (plan : Plan roles) (model : Assignment) : Prop :=
  GeneralNominalState.Models plan.packet.context.state model ∧ Inputs plan model ∧ Outputs plan model

theorem models_iff : GeneralNominalCenteredHeadMatPlans.Models plan model ↔ Holds plan model := by
  constructor
  · rintro ⟨head,input,binders,heads,equations,children⟩
    have privateModels : GeneralNominalState.Models plan.packet.privateContext.state model := head.1
    obtain ⟨context,ordinary⟩ := (GeneralNominalPacketSupport.private_exact plan.packet model).mp privateModels
    exact ⟨context,⟨ordinary,head.2,input,binders,heads,fun equation member _ => equations equation member,children⟩,equations⟩
  · rintro ⟨context,⟨ordinary,projections,input,binders,heads,_,children⟩,equations⟩
    exact ⟨⟨(GeneralNominalPacketSupport.private_exact plan.packet model).mpr ⟨context,ordinary⟩,projections⟩,
      input,binders,heads,equations,children⟩

theorem private_models (valid : Holds plan model) :
    GeneralNominalState.Models plan.packet.privateContext.state model :=
  (GeneralNominalPacketSupport.private_exact plan.packet model).mpr ⟨valid.1,valid.2.1.1⟩

theorem head_equations (valid : Holds plan model) : GeneralNominalCenteredHeadOutputs.HeadEquations plan model :=
  ⟨valid.2.1.2.2.1,fun name member => valid.2.1.2.2.2.1 name (Or.inl member),valid.2.1.2.2.2.2.1⟩

theorem emitted_holds (valid : Holds plan model) (member : site ∈ plan.emitted) : site.Holds model := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  exact (valid.2.1.2.2.2.2.2.2 clause.val clause.property _).1

theorem output_equation (valid : Outputs plan model)
    (member : request ∈ GeneralNominalCenteredHeadMatSchemas.requests plan.packet.context.state plan.packet.registry
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bindings)
    (translated : GeneralNominalCenteredHeadMatExpressions.translate plan.packet.registry.constructors
      plan.packet.context.interpretation request.pattern = some expression) :
    CommonNominalFullCarrier.Equivalent (model request.target).1
      (GeneralNominalCenteredHeadMatExpressions.value (variables plan model) request.mode expression) :=
  GeneralNominalCenteredHeadMatSchemas.generated_equation valid member translated

theorem shared_center (valid : Inputs plan model)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture plan.packet).inputs name)
      (model (plan.binder name)).1 := valid.2.2.2.1 name needed

end Yulang.GeneralNominalCenteredHeadMatStepPackets
