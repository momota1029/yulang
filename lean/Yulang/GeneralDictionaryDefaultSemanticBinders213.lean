import Yulang.GeneralDictionaryDefaultSemanticTerminal213

/-! A current point capture absorbs an old actual name semantically. The other
case preserves the allocation name. No agreement of capture multiplicities,
reports, descriptor trees, or source endpoint names is required. -/
namespace Yulang.GeneralDictionaryDefaultSemanticBinders213
open GeneralNominalCenters GeneralNominalCaptureMerges
open CommonNominalFullCarrier GeneralDictionaryDefaultExpression209
variable {roles : Roles.RoleDecls} {first last : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 def RefinedShape (first last : Plan roles) (name : Nat) : Prop :=
  let a := (GeneralNominalPacketSupport.capture first.packet).inputs name
  let b := (GeneralNominalPacketSupport.capture last.packet).inputs name
  b.1 = b.2 ∨ (a.1 ≠ a.2 ∧ b.1 ≠ b.2)

 theorem point_binder (plan : Plan roles) (input : name ∉ plan.packet.declaration.outputNames)
    (point : ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2) :
    plan.binder name = ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 := by
  simp only [Plan.binder,input,ite_false,point,ite_true]

 theorem input_equivalent
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (input : name ∉ first.packet.declaration.outputNames)
    (shape : RefinedShape first last name)
    (fit : Fits model ((GeneralNominalPacketSupport.capture last.packet).inputs name)
      (model (first.binder name)).1) :
    Equivalent (model (first.binder name)).1 (model (last.binder name)).1 := by
  have input' : name ∉ last.packet.declaration.outputNames := declaration ▸ input
  rcases shape with point | ⟨oldNonpoint,newNonpoint⟩
  · rw [point_binder last input' point]
    refine ⟨?_,fit.1⟩
    exact Eq.mp (congrArg (fun n => Subtype (model (first.binder name)).1 (model n).1) point.symm) fit.2
  · have equal := GeneralDictionaryDefaultBinderShape210.input_name seed identity declaration input
      (Or.inr ⟨oldNonpoint,newNonpoint⟩)
    rw [equal]; exact equivalent_refl _

 theorem names
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (shape : ∀ name, name ∉ first.packet.declaration.outputNames → RefinedShape first last name)
    (fit : ∀ name, name ∉ first.packet.declaration.outputNames →
      ((GeneralNominalPacketSupport.capture last.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture last.packet).inputs name).2 →
      Fits model ((GeneralNominalPacketSupport.capture last.packet).inputs name) (model (first.binder name)).1) :
    ∀ name, Equivalent (model (first.binder name)).1 (model (last.binder name)).1 := by
  intro name
  by_cases output : name ∈ first.packet.declaration.outputNames
  · rw [GeneralDictionaryDefaultBinderShape210.output_name seed identity declaration output]
    exact equivalent_refl _
  · rcases shape name output with point | nonpoint
    · exact input_equivalent seed identity declaration output (Or.inl point) (fit name output point)
    · have equal := GeneralDictionaryDefaultBinderShape210.input_name seed identity declaration output
        (Or.inr nonpoint)
      rw [equal]; exact equivalent_refl _
end Yulang.GeneralDictionaryDefaultSemanticBinders213
