import Yulang.GeneralDictionaryDefaultBinderShape210

/-! Entire emitted total-output semantics for terminal declarations is independent
of inspection reports once actual binder names agree. This is not input-packet
replay; projection, ordinary and head-schema obligations remain separate. -/
namespace Yulang.GeneralDictionaryDefaultTerminalOutputs210
open GeneralDeclarations GeneralNominalCenters GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadMatSchemas GeneralNominalCenteredHeadMatPlans
open GeneralNominalCenteredHeadMatStepPackets
variable {roles : Roles.RoleDecls} {first last : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 theorem generated_actual (requests : List GeneralNominalMaterialization.Request)
    (actual : ∀ request ∈ requests, request.mode = .actual) :
    ∀ equation ∈ (generated catalogue interpretation requests).equations, equation.mode = .actual := by
  induction requests with
  | nil => intro equation member; cases member
  | cons head tail ih =>
    intro equation member
    rcases List.mem_append.mp member with member | member
    · unfold materialize at member
      split at member
      · cases List.mem_singleton.mp member
        exact actual head (by simp)
      · cases member
    · exact ih (fun request member => actual request (List.mem_cons_of_mem _ member)) equation member

 theorem terminal_requests (plan : Plan roles) (terminal : plan.packet.declaration.requirements = []) :
    requests plan.packet.context.state plan.packet.registry plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked plan.packet.bindings =
      GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence := by
  simp [requests,GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,terminal]

 theorem terminal_actual (plan : Plan roles) (terminal : plan.packet.declaration.requirements = []) :
    ∀ equation ∈ (emittedSchema plan).equations, equation.mode = .actual := by
  unfold emittedSchema
  rw [terminal_requests plan terminal]
  apply generated_actual
  intro request member
  unfold GeneralNominalMaterialization.rootRequests at member
  obtain ⟨output,_,member⟩ := List.mem_flatMap.mp member
  obtain ⟨equation,_,rfl⟩ := List.mem_map.mp member
  rfl

 theorem outputs_iff
    (declaration : first.packet.declaration = last.packet.declaration)
    (occurrence : first.packet.site.occurrence = last.packet.site.occurrence)
    (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (terminal : first.packet.declaration.requirements = [])
    (names : ∀ name, first.binder name = last.binder name) :
    Outputs first model ↔ Outputs last model := by
  have terminal' : last.packet.declaration.requirements = [] := declaration ▸ terminal
  have same : emittedSchema first = emittedSchema last := by
    unfold emittedSchema
    rw [terminal_requests first terminal,terminal_requests last terminal',declaration,occurrence,constructors,interpretation]
  have equation (entry : GeneralNominalCenteredHeadMatSchemas.Equation) (member : entry ∈ (emittedSchema first).equations) :
      entry.Holds (variables first model) model ↔ entry.Holds (variables last model) model := by
    unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
    rw [terminal_actual first terminal entry member]
    have equal : (fun name => variables first model .actual name) =
        (fun name => variables last model .actual name) := by
      funext name
      simp only [GeneralDictionaryDefaultBodyTransport209.actual_variables,names name]
      rfl
    rw [← GeneralDictionaryDefaultBodyTransport209.actual_only,
      ← GeneralDictionaryDefaultBodyTransport209.actual_only (environment := variables last model),equal]
  constructor
  · intro valid entry member
    exact (equation entry (same.symm ▸ member)).mp (valid entry (same.symm ▸ member))
  · intro valid entry member
    exact (equation entry member).mpr (valid entry (same ▸ member))
end Yulang.GeneralDictionaryDefaultTerminalOutputs210
