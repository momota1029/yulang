import Yulang.GeneralNominalVersionedAllocation231
import Yulang.GeneralNominalCenteredAllocation

/-! I44 emission and center adapter. Only aggregate endpoints are versioned.
Actual centers, output allocation, and child identities remain unchanged.
This layer is not an operational boundary or an EvidenceNode theorem. -/
namespace Yulang.GeneralNominalVersionedFrame231
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalAllocation (occurrences)

def frame (packet : Packet roles) : GeneralDictionaryEmissionPlans.Frame roles where
  capture := fun key => GeneralNominalVersionedAllocation231.capture packet.context.state
    packet.registry packet.site.occurrence.identity key packet.bindings
  allocation := fun key => GeneralNominalAllocation.allocation packet.context.state packet.registry
    packet.site.occurrence.identity key
  identity := fun invocation key clause => GeneralNominalAllocation.source packet.context.state packet.registry
    packet.site.occurrence.identity (GeneralNominalAllocation.origin invocation key 6 clause 0)

def capture (packet : Packet roles) : GeneralDeclarationDemands.Capture :=
  (frame packet).capture packet.declaration.id

def binder (plan : Plan roles) (name : Nat) : Nat :=
  if name ∈ plan.packet.declaration.outputNames then (capture plan.packet).outputs name
  else if ((capture plan.packet).inputs name).1 = ((capture plan.packet).inputs name).2 then
    ((capture plan.packet).inputs name).1
  else fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id 8 name 0

theorem capture_outputs (packet : Packet roles) (name : Nat) :
    (capture packet).outputs name = (GeneralNominalPacketSupport.capture packet).outputs name := rfl

theorem binder_eq (plan : Plan roles) (name : Nat) : binder plan name = plan.binder name := by
  unfold binder Plan.binder
  by_cases output : name ∈ plan.packet.declaration.outputNames
  · simp only [output,ite_true,capture_outputs]
  · simp only [output,ite_false]
    unfold capture frame GeneralNominalVersionedAllocation231.capture GeneralNominalPacketSupport.capture
      GeneralNominalAllocation.capture
    cases found : occurrences plan.packet.bindings name with
    | nil =>
      have newer := GeneralNominalAggregateVersion231.distinct_purpose plan.packet.context.state.seed
        plan.packet.site.occurrence.identity plan.packet.declaration.id 0 1 name
        plan.packet.bindings plan.packet.bindings (by decide)
      have older := GeneralNominalCenteredAllocation.fresh_namespaces
        (seed := plan.packet.context.state.seed) (invocation := plan.packet.site.occurrence.identity)
        (declaration := plan.packet.declaration.id) (owner := name) (position := 0)
        (next := plan.packet.site.occurrence.identity) (nextDeclaration := plan.packet.declaration.id)
        (nextOwner := name) (nextPosition := 0) (by decide : (0:Nat) ≠ 1)
      change GeneralNominalAllocation.source plan.packet.context.state plan.packet.registry
          plan.packet.site.occurrence.identity (GeneralNominalAllocation.origin plan.packet.site.occurrence.identity plan.packet.declaration.id 0 name 0) ≠
          GeneralNominalAllocation.source plan.packet.context.state plan.packet.registry
          plan.packet.site.occurrence.identity (GeneralNominalAllocation.origin plan.packet.site.occurrence.identity plan.packet.declaration.id 1 name 0) at older
      simp only [found,newer,older,ite_false]
    | cons bounds rest =>
      cases rest with
      | nil => simp only [found]
      | cons next tail =>
        have newer := GeneralNominalAggregateVersion231.distinct_purpose plan.packet.context.state.seed
          plan.packet.site.occurrence.identity plan.packet.declaration.id 0 1 name
          plan.packet.bindings plan.packet.bindings (by decide)
        have older := GeneralNominalCenteredAllocation.fresh_namespaces
          (seed := plan.packet.context.state.seed) (invocation := plan.packet.site.occurrence.identity)
          (declaration := plan.packet.declaration.id) (owner := name) (position := 0)
          (next := plan.packet.site.occurrence.identity) (nextDeclaration := plan.packet.declaration.id)
          (nextOwner := name) (nextPosition := 0) (by decide : (0:Nat) ≠ 1)
        change GeneralNominalAllocation.source plan.packet.context.state plan.packet.registry
            plan.packet.site.occurrence.identity (GeneralNominalAllocation.origin plan.packet.site.occurrence.identity plan.packet.declaration.id 0 name 0) ≠
            GeneralNominalAllocation.source plan.packet.context.state plan.packet.registry
            plan.packet.site.occurrence.identity (GeneralNominalAllocation.origin plan.packet.site.occurrence.identity plan.packet.declaration.id 1 name 0) at older
        simp only [found,newer,older,ite_false]

def clauseChild (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) : Occurrence roles :=
  GeneralDictionaryEmissionPlans.occurrence (frame packet)
    (GeneralDeclarationDemands.emit packet.site.occurrence.identity packet.declaration clause valid
      (capture packet) ((frame packet).allocation packet.declaration.id clause))

def children (packet : Packet roles) : List (Occurrence roles) :=
  GeneralDictionaryEmissionPlans.children (frame packet) packet.site.occurrence packet.declaration packet.checked

theorem allocation_eq (packet : Packet roles) :
    (frame packet).allocation = (GeneralNominalFeedbackSites.frame packet).allocation := rfl

theorem identity_eq (packet : Packet roles) :
    (frame packet).identity = (GeneralNominalFeedbackSites.frame packet).identity := rfl

theorem child_identity (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) :
    (clauseChild packet clause valid).identity =
      (GeneralNominalFeedbackSites.clauseChild packet clause valid).identity := rfl

theorem child_role (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) :
    (clauseChild packet clause valid).demand.role = clause.role := rfl

theorem output_target_eq (packet : Packet roles) (allocate : Nat → Nat) (equation : Equation) :
    GeneralDeclarationDemands.outputTarget packet.declaration (capture packet) allocate equation =
      GeneralDeclarationDemands.outputTarget packet.declaration (GeneralNominalPacketSupport.capture packet) allocate equation := by
  unfold GeneralDeclarationDemands.outputTarget
  cases GeneralDeclarationPatterns.normalize equation.rhs <;> rfl

theorem child_outputs_eq (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) :
    (clauseChild packet clause valid).demand.outputs =
      (GeneralNominalFeedbackSites.clauseChild packet clause valid).demand.outputs := by
  change clause.outputs.map _ = clause.outputs.map _
  apply List.map_congr_left
  intro equation _
  exact congrArg (fun target => (⟨equation.name,target⟩ : GeneralSourceState.Output))
    (output_target_eq packet _ equation)

theorem children_identity_eq (packet : Packet roles) :
    (children packet).map Occurrence.identity = packet.children.map Occurrence.identity := by
  simp only [children,GeneralNominalSaturationState.Packet.children,GeneralNominalAllocation.children,
    GeneralDictionaryEmissionPlans.children,GeneralCanonicalChildOrder.canonicalEmit,
    GeneralDeclarationDemands.emitAll,List.map_map]
  rfl

theorem children_role_eq (packet : Packet roles) :
    (children packet).map (fun child => child.demand.role) = packet.children.map (fun child => child.demand.role) := by
  simp only [children,GeneralNominalSaturationState.Packet.children,GeneralNominalAllocation.children,
    GeneralDictionaryEmissionPlans.children,GeneralCanonicalChildOrder.canonicalEmit,
    GeneralDeclarationDemands.emitAll,List.map_map]
  rfl

theorem children_length_eq (packet : Packet roles) : (children packet).length = packet.children.length := by
  have same := congrArg List.length (children_identity_eq packet)
  simpa only [List.length_map] using same

def emittedCenter (plan : Plan roles) (clause position : Nat)
    (pattern : GeneralDeclarationPatterns.Pattern) : Nat :=
  match GeneralDeclarationPatterns.normalize pattern with
  | .var name => binder plan name
  | _ => fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity
      plan.packet.declaration.id 9 clause position

theorem emittedCenter_eq (plan : Plan roles) (clause position : Nat)
    (pattern : GeneralDeclarationPatterns.Pattern) :
    emittedCenter plan clause position pattern = plan.emittedCenter clause position pattern := by
  unfold emittedCenter Plan.emittedCenter
  cases GeneralDeclarationPatterns.normalize pattern <;> first | exact binder_eq _ _ | rfl

def childSite (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) : Site roles where
  occurrence := clauseChild plan.packet clause valid
  center := fun index => emittedCenter plan clause.id index.val
    (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt))

theorem childSite_center_eq (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles)
    (index : Fin (roles clause.role).arity) :
    (childSite plan clause valid).center index = (plan.childSite clause valid).center index :=
  emittedCenter_eq _ _ _ _

theorem childSite_identity_eq (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) :
    (childSite plan clause valid).occurrence.identity = (plan.childSite clause valid).occurrence.identity := rfl


end Yulang.GeneralNominalVersionedFrame231
