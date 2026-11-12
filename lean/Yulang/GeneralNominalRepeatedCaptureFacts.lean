import Yulang.GeneralNominalBinaryCaptureFacts

/-! Exact residual for a repeated binder in two nominal positions. Ordinary
state Models supplies each interval separately. The remaining projection
condition is equality of the actual nominal observations, not merely overlap
of their intervals or existence of another branch model. -/
namespace Yulang.GeneralNominalRepeatedCaptureFacts
open GeneralNominalRecursiveInspection GeneralNominalBinaryCaptureFacts
open CommonNominalFullCarrier

/-- Both observations use the same assignment. -/
def SameParameters (model : GeneralNominalCommonBridge.Assignment)
    (source name : Nat) : Prop :=
  ∀ x y, Observes model (.nominal (.source source) name 0) x →
    Observes model (.nominal (.source source) name 1) y → Equivalent x y

theorem projection_requires_same (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (slot : Fin state.base.slots)
    (name binder : Nat) (left right : GeneralNominalInspection.Bounds state)
    (valid : ProjectionModels state (captured state slot name binder binder left right) model) :
    SameParameters model (state.base.source slot) name := by
  intro x y one two
  exact valid.2.2.2 ⟨binder,left,some (.nominal (.source (state.base.source slot)) name 0)⟩
    (by simp [captured]) ⟨binder,right,some (.nominal (.source (state.base.source slot)) name 1)⟩
    (by simp [captured]) rfl _ _ rfl rfl x y one two

theorem projection_of_same (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) (binder : Nat)
    (left right : GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (same : SameParameters model (state.base.source slot) descriptor.declaration.name) :
    ProjectionModels state (captured state slot descriptor.declaration.name binder binder left right) model := by
  have arg0 := nominal_argument_bounds state model models slot descriptor recorded 0 left (by rw [parameters]; rfl)
  have arg1 := nominal_argument_bounds state model models slot descriptor recorded 1 right (by rw [parameters]; rfl)
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    simp only [captured,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact arg0
    · exact arg1
  · intro test member; cases member
  · intro a ha b hb _ ref origin actual seen
    simp only [captured,List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · cases Option.some.inj origin; exact arg0.2 actual seen
    · cases Option.some.inj origin
      obtain ⟨other,observed⟩ := arg1.1
      have equal := same actual other seen observed
      have fits := arg1.2 other observed
      exact ⟨subtype_trans fits.1 equal.2,subtype_trans equal.1 fits.2⟩
    · cases Option.some.inj origin
      obtain ⟨other,observed⟩ := arg0.1
      have equal := same other actual observed seen
      have fits := arg0.2 other observed
      exact ⟨subtype_trans fits.1 equal.1,subtype_trans equal.2 fits.2⟩
    · cases Option.some.inj origin; exact arg1.2 actual seen
  · intro a ha b hb _ x y hx hy u v hu hv
    simp only [captured,List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · cases Option.some.inj hx; cases Option.some.inj hy
      exact nominal_observation_unique model (.argument (.source (state.base.source slot)) descriptor.declaration.name 0) u v hu hv
    · cases Option.some.inj hx; cases Option.some.inj hy
      exact same u v hu hv
    · cases Option.some.inj hx; cases Option.some.inj hy
      have equal := same v u hv hu
      exact ⟨equal.2,equal.1⟩
    · cases Option.some.inj hx; cases Option.some.inj hy
      exact nominal_observation_unique model (.argument (.source (state.base.source slot)) descriptor.declaration.name 1) u v hu hv

/-- The repeated-name projection obligation is exactly the same-model equality
of these two observations. Bounds need not be point intervals. -/
theorem projection_iff_same (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) (binder : Nat)
    (left right : GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = [.type left,.type right]) :
    ProjectionModels state (captured state slot descriptor.declaration.name binder binder left right) model ↔
      SameParameters model (state.base.source slot) descriptor.declaration.name :=
  ⟨projection_requires_same state model slot descriptor.declaration.name binder left right,
   projection_of_same state model models slot descriptor recorded binder left right parameters⟩

end Yulang.GeneralNominalRepeatedCaptureFacts
