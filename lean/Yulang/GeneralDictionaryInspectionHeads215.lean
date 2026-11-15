import Yulang.GeneralDictionaryDefaultNominalFallback215

/-! Coarse observable constructor tags survive subtyping. This includes mixed
nominal type/row parameters and distinguishes all scalar constructors. -/
namespace Yulang.GeneralDictionaryInspectionHeads215
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralNominalFiniteHeadInversion
open GeneralNominalCommonBridge (Assignment)
variable {state : GeneralNominalState.State} {model : Assignment}

def Tagged (value : Ty) (tag : CommonNominalFullDemand.Head) : Prop :=
  ∀ env : CommonNominalFullDemand.Environment Row,
    CommonNominalFullDemand.ProbeAt Common.rowLe 0 env (observeTy 0 value) (.role 0) ↔ tag ∈ env.roles 0

theorem tag_subtype (one : Tagged first a) (two : Tagged last b) (below : Subtype first last) : a = b := by
  let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => [b]⟩
  have accepted := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 env (.role 0)
    ((two env).mpr (List.mem_singleton_self _))
  exact List.mem_singleton.mp ((one env).mp accepted)

theorem tagged_equivalent (same : Equivalent first last) (known : Tagged last tag) : Tagged first tag := by
  intro env
  constructor
  · intro held
    exact (known env).mp ((CommonNominalFullDemand.producerLe_iff_probe _ _).mp (same.2 0) 0 env (.role 0) held)
  · intro held
    exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (same.1 0) 0 env (.role 0) ((known env).mpr held)

theorem tagged_scalar (base : Inference.Base) : Tagged (.base base) (.base base) := by intro env; rfl

theorem tagged_nominal (name : Nat) (arguments : List Argument) : Tagged (nominal name arguments) (.nominal name arguments.length) := by
  intro env
  simp only [observe_nominal]
  change _ ∈ env.roles 0 ↔ _
  simp only [List.length_map]

theorem tagged_shape (shape : GeneralNormalizedObservation.Shape) (values : List Ty)
    (length : values.length = shape.arity) : Tagged (shapeValue shape values) (head (.structural shape)) := by
  intro env
  cases shape with
  | pair | variant | exactEmpty => rfl
  | record labels =>
    rw [GeneralNominalRecordInversion.record_shape labels values length]
    exact record_role _ env

theorem tagged_test (test : Test) (held : test.Holds value) : Tagged value (head test) := by
  cases test with
  | scalar base => exact tagged_equivalent held (tagged_scalar base)
  | nominal name count =>
      obtain ⟨args,length,equal⟩ := held
      exact tagged_equivalent equal (length ▸ tagged_nominal name args)
  | structural shape =>
      obtain ⟨values,length,equal⟩ := held
      exact tagged_equivalent equal (tagged_shape shape values length)

theorem scalar_slot (valid : GeneralNominalState.Models state model)
    (recorded : state.view.heads slot = .scalar base) :
    Tagged (model (state.base.source slot)).1 (.base base) := by
  apply tagged_equivalent (GeneralNominalState.normalized_models state model valid slot (.base base) (by rw [recorded]; rfl))
  exact tagged_scalar base

theorem nominal_slot (valid : GeneralNominalState.Models state model)
    (recorded : state.nominals slot = some descriptor) :
    Tagged (model (state.base.source slot)).1 (.nominal descriptor.declaration.name descriptor.arguments.length) := by
  obtain ⟨arguments,fits,equal⟩ := valid.2.1 slot descriptor recorded
  have length := GeneralNominalLinearMaterializationFacts.fitsAll_length _ _ _ _ fits
  exact tagged_equivalent equal (length ▸ tagged_nominal descriptor.declaration.name arguments)

theorem structural_slot (valid : GeneralNominalState.Models state model)
    (recorded : state.view.heads slot = .structural kind children) :
    Tagged (model (state.base.source slot)).1 (head (.structural (state.view.shapes kind))) := by
  apply tagged_equivalent (GeneralNominalFiniteBracket.structural_slot state model valid slot kind children recorded rfl)
  exact build_role _ _

theorem lower_tag (bounded : GeneralDictionaryDefaultNominalProjection215.Bounded state model bounds origin)
    (tested : GeneralNominalOriginTerms.Head model origin test)
    (known : Tagged (model (state.base.source bounds.1)).1 tag) : tag = head test := by
  obtain ⟨value,seen⟩ := bounded.1
  exact tag_subtype known (tagged_test test (tested.2 value seen)) (bounded.2 value seen).1

theorem upper_tag (bounded : GeneralDictionaryDefaultNominalProjection215.Bounded state model bounds origin)
    (tested : GeneralNominalOriginTerms.Head model origin test)
    (known : Tagged (model (state.base.source bounds.2)).1 tag) : head test = tag := by
  obtain ⟨value,seen⟩ := bounded.1
  exact tag_subtype (tagged_test test (tested.2 value seen)) known (bounded.2 value seen).2

end Yulang.GeneralDictionaryInspectionHeads215
