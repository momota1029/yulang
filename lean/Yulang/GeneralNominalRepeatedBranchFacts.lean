import Yulang.GeneralNominalRepeatedCaptureFacts

/-! Exact same-assignment branch residual for one binder repeated in two nominal
positions. The four cross inequalities and inspection self checks are derived;
allocated merge equations and generated materialization remain explicit. -/
namespace Yulang.GeneralNominalRepeatedBranchFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalBinaryCaptureFacts GeneralNominalRepeatedCaptureFacts
open GeneralDeclarations CommonNominalFullCarrier

theorem compatible_of_same (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) (binder : Nat)
    (left right : GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (same : SameParameters model (state.base.source slot) descriptor.declaration.name) :
    GeneralNominalAllocation.Compatible
      (bindings state (captured state slot descriptor.declaration.name binder binder left right)) model := by
  have arg0 := nominal_argument_bounds state model models slot descriptor recorded 0 left (by rw [parameters]; rfl)
  have arg1 := nominal_argument_bounds state model models slot descriptor recorded 1 right (by rw [parameters]; rfl)
  obtain ⟨x,hx⟩ := arg0.1
  obtain ⟨y,hy⟩ := arg1.1
  have one := arg0.2 x hx
  have two := arg1.2 y hy
  have equal := same x y hx hy
  intro a ha b hb _
  simp only [bindings,captured,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact subtype_trans one.1 one.2
  · exact subtype_trans one.1 (subtype_trans equal.1 two.2)
  · exact subtype_trans two.1 (subtype_trans equal.2 one.2)
  · exact subtype_trans two.1 two.2

theorem private_models_of_merges (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) (binder : Nat)
    (left right : GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name [.variables [binder],.variables [binder]]])
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models context.state model)
    (same : SameParameters model (context.state.base.source slot) descriptor.declaration.name)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges context.state registry root.identity declaration
        (bindings context.state (report context declaration [(slot,slot)])))) :
    GeneralNominalState.Models (privateState registry context root declaration [(slot,slot)]) model := by
  have calculated := report_exact context declaration slot descriptor recorded binder binder left right parameters query
  have arg0 := nominal_argument_bounds context.state model models slot descriptor recorded 0 left (by rw [parameters]; rfl)
  have arg1 := nominal_argument_bounds context.state model models slot descriptor recorded 1 right (by rw [parameters]; rfl)
  obtain ⟨x,hx⟩ := arg0.1
  obtain ⟨y,hy⟩ := arg1.1
  have one := arg0.2 x hx
  have two := arg1.2 y hy
  unfold privateState
  rw [calculated] at merges ⊢
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨models,?_,merges⟩,?_⟩
  · exact compatible_of_same context.state model models slot descriptor recorded binder left right parameters same
  · exact self_models context.state slot descriptor.declaration.name binder binder left right model
      (subtype_trans one.1 one.2) (subtype_trans two.1 two.2)

/-- Complete decomposition for the repeated two-position head: current source
models plus observed equality, allocation equations, and materialized requests.
No distinctness of interval endpoints or point-valued interval is assumed. -/
theorem branch_models_iff_residual (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) (binder : Nat)
    (left right : GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name [.variables [binder],.variables [binder]]])
    (model : GeneralNominalCommonBridge.Assignment) :
    BranchModels registry context root declaration checked [(slot,slot)] model ↔
      GeneralNominalState.Models context.state model ∧
      SameParameters model (context.state.base.source slot) descriptor.declaration.name ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.merges context.state registry root.identity declaration
          (bindings context.state (report context declaration [(slot,slot)]))) ∧
      GeneralNominalMaterialization.Models context.state declaration
        (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
          (bindings context.state (report context declaration [(slot,slot)])))
        (report context declaration [(slot,slot)])
        (generated registry context root declaration checked [(slot,slot)]) model := by
  have calculated := report_exact context declaration slot descriptor recorded binder binder left right parameters query
  constructor
  · intro branch
    have original := (branch_interval_sound registry context root declaration checked [(slot,slot)] model branch).1
    have projection := branch.2.1
    rw [calculated] at projection
    have propagated := ((GeneralNominalState.extend_models ..).mp branch.1).1
    exact ⟨original,projection_requires_same context.state model slot descriptor.declaration.name binder left right projection,
      ((GeneralNominalAllocation.propagate_models ..).mp propagated).2.2,branch.2.2⟩
  · rintro ⟨original,same,merges,materialized⟩
    refine ⟨private_models_of_merges context registry root declaration slot descriptor recorded binder left right parameters query model original same merges,?_,materialized⟩
    rw [calculated]
    exact projection_of_same context.state model original slot descriptor recorded binder left right parameters same
end Yulang.GeneralNominalRepeatedBranchFacts
