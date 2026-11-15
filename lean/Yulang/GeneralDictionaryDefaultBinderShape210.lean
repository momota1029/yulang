import Yulang.GeneralDictionaryDefaultBodyTransport209
import Yulang.GeneralNominalBinderIdentity181

/-! Total output expressions do not require erased-report equality. When a
capture remains nonpoint its actual purpose-eight name is persistent; for point
captures the endpoint name must persist. This covers descriptor changes that
alter capture multiplicity without changing that classification. -/
namespace Yulang.GeneralDictionaryDefaultBinderShape210
open GeneralNominalCenters GeneralNominalCenteredHeadMatEffects
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {first last : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 def InputShape (first last : Plan roles) (name : Nat) : Prop :=
  let a := (GeneralNominalPacketSupport.capture first.packet).inputs name
  let b := (GeneralNominalPacketSupport.capture last.packet).inputs name
  (a.1 = a.2 ∧ b.1 = b.2 ∧ a.1 = b.1) ∨ (a.1 ≠ a.2 ∧ b.1 ≠ b.2)

 theorem output_name
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (output : name ∈ first.packet.declaration.outputNames) : first.binder name = last.binder name := by
  have output' : name ∈ last.packet.declaration.outputNames := declaration ▸ output
  simp only [Plan.binder,output',ite_true,GeneralNominalPacketSupport.capture,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.source,seed,identity,declaration]

 theorem input_name
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (input : name ∉ first.packet.declaration.outputNames)
    (shape : InputShape first last name) : first.binder name = last.binder name := by
  have input' : name ∉ last.packet.declaration.outputNames := declaration ▸ input
  rcases shape with ⟨point,point',same⟩ | ⟨nonpoint,nonpoint'⟩
  · simpa only [Plan.binder,input,input',ite_false,point,point',ite_true] using same
  · rw [GeneralNominalBinderIdentity181.binder_fresh first name input nonpoint,
      GeneralNominalBinderIdentity181.binder_fresh last name input' nonpoint',seed,identity,declaration]

 theorem names
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (shape : ∀ name, name ∉ first.packet.declaration.outputNames → InputShape first last name) :
    ∀ name, first.binder name = last.binder name := by
  intro name
  by_cases output : name ∈ first.packet.declaration.outputNames
  · exact output_name seed identity declaration output
  · exact input_name seed identity declaration output (shape name output)

 theorem body_iff
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (input : first.input = last.input)
    (shape : ∀ name, name ∉ first.packet.declaration.outputNames → InputShape first last name) :
    BodyHolds first target model body ↔ BodyHolds last target model body := by
  apply GeneralDictionaryDefaultBodyTransport209.body_transport constructors interpretation
  · intro name
    rw [names seed identity declaration shape name]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro index
    rw [input]
    exact ⟨subtype_refl _,subtype_refl _⟩
end Yulang.GeneralDictionaryDefaultBinderShape210
