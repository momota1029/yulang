import Yulang.GeneralNominalCenteredHeadMatEffects
import Yulang.GeneralNominalCenteredHeadWFBoundary

set_option backward.isDefEq.respectTransparency false

/-! Prospective packet equations for the total materializer. These replace the
old named/input schemas; they are not conjoined with the old packet equations.
The operational journal still needs to consume this interface. -/
namespace Yulang.GeneralNominalCenteredHeadMatPlans
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadWFSource GeneralNominalCenteredHeadMatEffects
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Observes Origin)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}

def emittedSchema (plan : Plan roles) : GeneralNominalCenteredHeadMatSchemas.Schema :=
  GeneralNominalCenteredHeadMatSchemas.generated plan.packet.registry.constructors plan.packet.context.interpretation
    (GeneralNominalCenteredHeadMatSchemas.requests plan.packet.context.state plan.packet.registry plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked plan.packet.bindings)

def childSchema (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) : GeneralNominalCenteredHeadMatSchemas.Schema :=
  GeneralNominalCenteredHeadMatSchemas.generated plan.packet.registry.constructors plan.packet.context.interpretation (plan.childRequests clause valid)

def Models (plan : Plan roles) (model : Assignment) : Prop :=
  GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context plan.packet.site.occurrence
    plan.packet.declaration plan.packet.bounds model ∧
  plan.input.Holds model ∧
  (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture plan.packet).inputs name)
      (model (plan.binder name)).1) ∧
  plan.SchemaHolds plan.headSchema model ∧
  (emittedSchema plan).Holds (variables plan model) model ∧
  ∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
    (plan.childSite clause valid).Holds model ∧ (childSchema plan clause valid).Holds (variables plan model) model

variable {plan : Plan roles} {model : Assignment}

theorem emitted_complete
    (covered : DeclarationCovered plan.packet.registry.constructors plan.packet.context.interpretation plan.packet.declaration) :
    (emittedSchema plan).unknown = false :=
  GeneralNominalCenteredHeadMatSchemas.emitted_schema_complete covered plan.packet.checked

theorem child_complete
    (covered : DeclarationCovered plan.packet.registry.constructors plan.packet.context.interpretation plan.packet.declaration)
    (member : clause ∈ plan.packet.declaration.requirements) (valid : clause.Signature roles) :
    (childSchema plan clause valid).unknown = false := by
  apply GeneralNominalCenteredHeadMatSchemas.generated_complete
  intro request present
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
  exact GeneralNominalCenteredHeadMatSchemas.patterns_member (covered.2.1 clause member).1
    (List.getElem_mem (l := clause.arguments) (n := index.val) (by rw [valid.1]; exact index.isLt))

theorem reachable_frame_coverage
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan) :
    Coverage plan.packet.registry plan.packet.context.interpretation := by
  rw [frame.registry_eq,frame.context_eq]
  exact GeneralNominalCenteredHeadWFBoundary.reachable_coverage reachable

theorem reachable_emitted_complete
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan) :
    (emittedSchema plan).unknown = false := by
  apply emitted_complete
  exact (reachable_frame_coverage reachable frame).1 _ (frame.registry_eq.symm ▸ frame.visible)

theorem reachable_child_complete
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (member : clause ∈ plan.packet.declaration.requirements) (valid : clause.Signature roles) :
    (childSchema plan clause valid).unknown = false :=
  child_complete ((reachable_frame_coverage reachable frame).1 _ (frame.registry_eq.symm ▸ frame.visible)) member valid

theorem binder_readback (valid : Models plan model)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture plan.packet).inputs name)
      (model (plan.binder name)).1 := valid.2.2.1 name needed

theorem capture_agreement (valid : Models plan model) (entry : GeneralNominalMaterialization.Use) (member : entry ∈ plan.headSchema.variables)
    (same : entry.name = name) (actual : entry.mode = .actual) :
    GeneralNominalOriginTerms.Same model entry.origin (.source (plan.binder name)) := by
  have agreement := valid.2.2.2.1.2 entry member
  simpa only [actual,ite_true,same] using agreement

theorem generation_certificate (plan : Plan roles) :
    ∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
    ∀ model, Models plan model →
      (∃ actual, Observes model (.source (plan.binder name)) actual) ∧
      ∀ actual, Observes model (.source (plan.binder name)) actual →
        GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture plan.packet).inputs name) actual := by
  intro name needed model valid
  refine ⟨⟨_,.source _⟩,?_⟩
  intro actual seen
  cases seen
  exact binder_readback valid needed

end Yulang.GeneralNominalCenteredHeadMatPlans
