import Yulang.GeneralDictionaryDefaultActualHead210
import Yulang.GeneralDictionaryDefaultTerminalReduction212

namespace Yulang.GeneralDictionaryDefaultSemanticTerminal213
open GeneralNominalCenters GeneralNominalCenteredHeadMatStepPackets
open GeneralNominalCenteredHeadMatSchemas GeneralNominalCenteredHeadMatPlans
open GeneralNominalCenteredHeadMatEffects GeneralDictionaryDefaultExpression209
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {first last : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 theorem same_source (equal : Equivalent (model a).1 (model b).1) :
    GeneralNominalOriginTerms.Same model origin (.source a) ↔
      GeneralNominalOriginTerms.Same model origin (.source b) := by
  constructor
  · rintro ⟨seen,_,consistent⟩
    refine ⟨seen,⟨(model b).1,.source _⟩,?_⟩
    intro x y hx hy
    cases hy
    exact equivalent_trans (consistent x _ hx (.source _)) equal
  · rintro ⟨seen,_,consistent⟩
    refine ⟨seen,⟨(model a).1,.source _⟩,?_⟩
    intro x y hx hy
    cases hy
    exact equivalent_trans (consistent x _ hx (.source _)) ⟨equal.2,equal.1⟩

 theorem head_holds
    (queries : GeneralNominalInspection.queries first.packet.context.state first.packet.context.interpretation
      first.packet.declaration = GeneralNominalInspection.queries last.packet.context.state
        last.packet.context.interpretation last.packet.declaration)
    (input : first.input = last.input)
    (names : ∀ name, Equivalent (model (first.binder name)).1 (model (last.binder name)).1) :
    first.SchemaHolds first.headSchema model ↔ last.SchemaHolds last.headSchema model := by
  have same := GeneralDictionaryDefaultActualHead210.head_schema queries input
  have actual : ∀ entry ∈ first.headSchema.variables, entry.mode = .actual :=
    GeneralDictionaryActualSchema.schemas_actual _ _ _
  constructor
  · intro before
    refine ⟨same ▸ before.1,?_⟩
    intro entry member
    have member' : entry ∈ first.headSchema.variables := same.symm ▸ member
    have mode := actual entry member'
    have result := before.2 entry member'
    simp only [mode,ite_true] at result ⊢
    exact (same_source (names entry.name)).mp result
  · intro after
    refine ⟨same.symm ▸ after.1,?_⟩
    intro entry member
    have mode := actual entry member
    have result := after.2 entry (same ▸ member)
    simp only [mode,ite_true] at result ⊢
    exact (same_source (names entry.name)).mpr result

 theorem outputs_iff
    (declaration : first.packet.declaration = last.packet.declaration)
    (occurrence : first.packet.site.occurrence = last.packet.site.occurrence)
    (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (terminal : first.packet.declaration.requirements = [])
    (names : ∀ name, Equivalent (model (first.binder name)).1 (model (last.binder name)).1) :
    Outputs first model ↔ Outputs last model := by
  have terminal' : last.packet.declaration.requirements = [] := declaration ▸ terminal
  have same : emittedSchema first = emittedSchema last := by
    unfold emittedSchema
    rw [GeneralDictionaryDefaultTerminalOutputs210.terminal_requests first terminal,
      GeneralDictionaryDefaultTerminalOutputs210.terminal_requests last terminal',declaration,occurrence,constructors,interpretation]
  have equation (entry : GeneralNominalCenteredHeadMatSchemas.Equation) (member : entry ∈ (emittedSchema first).equations) :
      entry.Holds (variables first model) model ↔ entry.Holds (variables last model) model := by
    unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
    rw [GeneralDictionaryDefaultTerminalOutputs210.terminal_actual first terminal entry member]
    have equal := GeneralDictionaryDefaultBodyTransport209.actual_equivalent entry.expression
      (one := variables first model) (two := variables last model)
      (fun name _ => by simpa only [GeneralDictionaryDefaultBodyTransport209.actual_variables] using names name)
    exact ⟨fun valid => equivalent_trans valid equal,
      fun valid => equivalent_trans valid ⟨equal.2,equal.1⟩⟩
  constructor
  · intro valid entry member
    exact (equation entry (same.symm ▸ member)).mp (valid entry (same.symm ▸ member))
  · intro valid entry member
    exact (equation entry member).mpr (valid entry (same ▸ member))

 theorem terminal_replay
    (declaration : first.packet.declaration = last.packet.declaration)
    (occurrence : first.packet.site.occurrence = last.packet.site.occurrence)
    (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (queries : GeneralNominalInspection.queries first.packet.context.state first.packet.context.interpretation
      first.packet.declaration = GeneralNominalInspection.queries last.packet.context.state
        last.packet.context.interpretation last.packet.declaration)
    (input : first.input = last.input)
    (names : ∀ name, Equivalent (model (first.binder name)).1 (model (last.binder name)).1)
    (terminal : first.packet.declaration.requirements = [])
    (old : Holds first model)
    (current : GeneralNominalState.Models last.packet.context.state model)
    (ordinary : GeneralNominalPacketSupport.Ordinary last.packet model)
    (projections : GeneralNominalRecursiveInspection.ProjectionModels last.packet.context.state
      (GeneralNominalPacketSupport.report last.packet) model)
    (fits : ∀ name, name ∈ last.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed last.packet name →
      GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture last.packet).inputs name)
        (model (last.binder name)).1) : Holds last model := by
  have terminal' : last.packet.declaration.requirements = [] := declaration ▸ terminal
  have outputs := (outputs_iff declaration occurrence constructors interpretation terminal names).mp old.2.2
  refine ⟨current,⟨ordinary,projections,input ▸ old.2.1.2.2.1,fits,
    (head_holds queries input names).mp old.2.1.2.2.2.2.1,?_,?_⟩,outputs⟩
  · intro equation member _
    exact outputs equation member
  · intro clause member
    rw [terminal'] at member
    cases member
end Yulang.GeneralDictionaryDefaultSemanticTerminal213
