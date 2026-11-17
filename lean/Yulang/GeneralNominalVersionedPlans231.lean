import Yulang.GeneralNominalVersionedFrame231
import Yulang.GeneralNominalVersionedCapture231
import Yulang.GeneralNominalCenteredHeadMatStepPackets
set_option backward.isDefEq.respectTransparency false

/-! Prospective total packet semantics for I44. Data are the existing Plan,
but every capture consumer reads the same versioned allocation. This is not
yet the operational journal/Frame replacement and does not assert its laws. -/
namespace Yulang.GeneralNominalVersionedPlans231
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedFrame231 (capture binder childSite)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def Ordinary (packet : Packet roles) (model : Assignment) : Prop :=
  GeneralNominalAllocation.Compatible packet.bindings model ∧
  PresenceNormalForm.All CommonNominalFullCarrier.model model
    (GeneralNominalVersionedAllocation231.merges packet.context.state packet.registry
      packet.site.occurrence.identity packet.declaration packet.bindings) ∧
  PresenceNormalForm.All CommonNominalFullCarrier.model model
    (GeneralNominalRecursiveInspection.selfChecks packet.context.state (GeneralNominalPacketSupport.report packet))

def privateState (packet : Packet roles) : GeneralNominalState.State :=
  GeneralNominalState.extend
    (GeneralNominalVersionedAllocation231.propagate packet.context.state packet.registry
      packet.site.occurrence.identity packet.declaration packet.bindings)
    [] (GeneralNominalRecursiveInspection.selfChecks packet.context.state (GeneralNominalPacketSupport.report packet))

theorem private_models_iff (packet : Packet roles) (model : Assignment) :
    GeneralNominalState.Models (privateState packet) model ↔
      GeneralNominalState.Models packet.context.state model ∧ Ordinary packet model := by
  unfold privateState Ordinary
  rw [GeneralNominalState.extend_models,GeneralNominalVersionedAllocation231.propagate_models]
  simp only [and_assoc]

def HeadModels (packet : Packet roles) (model : Assignment) : Prop :=
  GeneralNominalState.Models (privateState packet) model ∧
  GeneralNominalRecursiveInspection.ProjectionModels packet.context.state (GeneralNominalPacketSupport.report packet) model

def SchemaHolds (plan : Plan roles) (schema : GeneralNominalMaterialization.Schema) (model : Assignment) : Prop :=
  (∀ test ∈ schema.tests, GeneralNominalOriginTerms.Head model test.1 test.2) ∧
  (∀ entry ∈ schema.variables,
    if entry.mode = .actual then
      GeneralNominalOriginTerms.Same model entry.origin (.source (binder plan entry.name))
    else (∃ actual, GeneralNominalRecursiveInspection.Observes model entry.origin actual) ∧
      ∀ actual, GeneralNominalRecursiveInspection.Observes model entry.origin actual →
        GeneralNominalMaterialization.VariableHolds plan.packet.declaration (capture plan.packet)
          model entry.name entry.mode actual)

def variables (plan : Plan roles) (model : Assignment) (mode : GeneralNominalMaterialization.Mode) (name : Nat) : Ty :=
  if name ∈ plan.packet.declaration.outputNames then (model (binder plan name)).1
  else match mode with
    | .actual => (model (binder plan name)).1
    | .lower => (model ((capture plan.packet).inputs name).1).1
    | .upper => (model ((capture plan.packet).inputs name).2).1

theorem actual_variables (plan : Plan roles) (model : Assignment) (name : Nat) :
    variables plan model .actual name = GeneralNominalCenteredHeadMatEffects.variables plan model .actual name := by
  simp only [variables,GeneralNominalCenteredHeadMatEffects.variables,GeneralNominalVersionedFrame231.binder_eq]

def emittedRequests (packet : Packet roles) : List GeneralNominalMaterialization.Request :=
  GeneralNominalMaterialization.rootRequests packet.declaration packet.site.occurrence ++
    (GeneralCanonicalChildOrder.canonicalEmit packet.site.occurrence.identity packet.declaration packet.checked
      (capture packet) ((GeneralNominalVersionedFrame231.frame packet).allocation packet.declaration.id)).flatMap
        GeneralNominalCenteredHeadMatSchemas.emissionRequests

def emittedSchema (plan : Plan roles) : GeneralNominalCenteredHeadMatSchemas.Schema :=
  GeneralNominalCenteredHeadMatSchemas.generated plan.packet.registry.constructors
    plan.packet.context.interpretation (emittedRequests plan.packet)

def childRequests (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) :
    List GeneralNominalMaterialization.Request :=
  List.ofFn fun index : Fin (roles clause.role).arity =>
    ⟨clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt),
      (childSite plan clause valid).center index,.actual⟩

def childSchema (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) :
    GeneralNominalCenteredHeadMatSchemas.Schema :=
  GeneralNominalCenteredHeadMatSchemas.generated plan.packet.registry.constructors
    plan.packet.context.interpretation (childRequests plan clause valid)

theorem childRequests_eq (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) :
    childRequests plan clause valid = plan.childRequests clause valid := by
  unfold childRequests Plan.childRequests
  congr 1
  funext index
  rw [GeneralNominalVersionedFrame231.childSite_center_eq]

theorem childSchema_eq (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) :
    childSchema plan clause valid = GeneralNominalCenteredHeadMatPlans.childSchema plan clause valid := by
  unfold childSchema GeneralNominalCenteredHeadMatPlans.childSchema
  rw [childRequests_eq]

def Inputs (plan : Plan roles) (model : Assignment) : Prop :=
  Ordinary plan.packet model ∧
  GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) model ∧
  plan.input.Holds model ∧
  (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
    GeneralNominalCaptureMerges.Fits model ((capture plan.packet).inputs name) (model (binder plan name)).1) ∧
  SchemaHolds plan plan.headSchema model ∧
  (∀ equation ∈ (emittedSchema plan).equations, equation.mode ≠ .actual →
    equation.Holds (variables plan model) model) ∧
  ∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
    (childSite plan clause valid).Holds model ∧ (childSchema plan clause valid).Holds (variables plan model) model

def Outputs (plan : Plan roles) (model : Assignment) : Prop :=
  (emittedSchema plan).Holds (variables plan model) model

def Holds (plan : Plan roles) (model : Assignment) : Prop :=
  GeneralNominalState.Models plan.packet.context.state model ∧ Inputs plan model ∧ Outputs plan model

variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : Assignment}

theorem head_models (valid : Holds plan model) : HeadModels plan.packet model :=
  ⟨(private_models_iff ..).mpr ⟨valid.1,valid.2.1.1⟩,valid.2.1.2.1⟩

theorem shared_center (valid : Inputs plan model)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    GeneralNominalCaptureMerges.Fits model ((capture plan.packet).inputs name) (model (binder plan name)).1 :=
  valid.2.2.2.1 name needed

theorem emitted_equation (valid : Outputs plan model) (member : equation ∈ (emittedSchema plan).equations) :
    equation.Holds (variables plan model) model := valid equation member

end Yulang.GeneralNominalVersionedPlans231
