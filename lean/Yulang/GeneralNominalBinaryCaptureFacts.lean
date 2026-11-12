import Yulang.GeneralNominalUnaryCaptureFacts

/-! Two distinct input binders under a nominal head. All interval endpoints and
source denotations are arbitrary. These are current-model consequences, not
assumed branch consistency, and do not discharge generated output equations. -/
namespace Yulang.GeneralNominalBinaryCaptureFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations CommonNominalFullCarrier

def captured (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (name first second : Nat) (left right : GeneralNominalInspection.Bounds state) : Report state where
  captures := [⟨first,left,some (.nominal (.source (state.base.source slot)) name 0)⟩,
    ⟨second,right,some (.nominal (.source (state.base.source slot)) name 1)⟩]
  inspected := [(slot,slot)]
  checked := [(slot,slot),(slot,slot),left,right]
  anchors := [(.nominal (.source (state.base.source slot)) name 0,left),
    (.nominal (.source (state.base.source slot)) name 1,right)]

theorem report_exact (context : Context) (declaration : Declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) (first second : Nat)
    (left right : GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name [.variables [first],.variables [second]]]) :
    report context declaration [(slot,slot)] = captured context.state slot descriptor.declaration.name first second left right := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,recorded,typeArguments,parameters,Report.visit,Report.append,captured]

theorem projection_models (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals slot = some descriptor)
    (first second : Nat) (distinct : first ≠ second)
    (left right : GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = [.type left,.type right]) :
    ProjectionModels state (captured state slot descriptor.declaration.name first second left right) model := by
  have arg0 := nominal_argument_bounds state model models slot descriptor recorded 0 left (by rw [parameters]; rfl)
  have arg1 := nominal_argument_bounds state model models slot descriptor recorded 1 right (by rw [parameters]; rfl)
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    simp only [captured,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact arg0
    · exact arg1
  · intro test member; cases member
  · intro a ha b hb same ref origin actual seen
    simp only [captured,List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · cases Option.some.inj origin; exact arg0.2 actual seen
    · exact False.elim (distinct same)
    · exact False.elim (distinct same.symm)
    · cases Option.some.inj origin; exact arg1.2 actual seen
  · intro a ha b hb same x y hx hy u v hu hv
    simp only [captured,List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · cases Option.some.inj hx; cases Option.some.inj hy
      exact nominal_observation_unique model (.argument (.source (state.base.source slot)) descriptor.declaration.name 0) u v hu hv
    · exact False.elim (distinct same)
    · exact False.elim (distinct same.symm)
    · cases Option.some.inj hx; cases Option.some.inj hy
      exact nominal_observation_unique model (.argument (.source (state.base.source slot)) descriptor.declaration.name 1) u v hu hv

theorem propagated_models (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (first second : Nat) (distinct : first ≠ second)
    (names : declaration.inputNames = [first,second])
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (left right : GeneralNominalInspection.Bounds state)
    (leftValid : Subtype (model (state.base.source left.1)).1 (model (state.base.source left.2)).1)
    (rightValid : Subtype (model (state.base.source right.1)).1 (model (state.base.source right.2)).1) :
    GeneralNominalState.Models (GeneralNominalAllocation.propagate state registry invocation declaration
      [(first,(state.base.source left.1,state.base.source left.2)),
       (second,(state.base.source right.1,state.base.source right.2))]) model := by
  apply (GeneralNominalAllocation.propagate_models ..).mpr
  refine ⟨models,?_,?_⟩
  · intro a ha b hb same
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact leftValid
    · exact False.elim (distinct same)
    · exact False.elim (distinct same.symm)
    · exact rightValid
  · simp [GeneralNominalAllocation.merges,names,GeneralNominalAllocation.occurrences,distinct,Ne.symm distinct]

theorem self_models (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (name first second : Nat) (left right : GeneralNominalInspection.Bounds state)
    (model : GeneralNominalCommonBridge.Assignment)
    (leftValid : Subtype (model (state.base.source left.1)).1 (model (state.base.source left.2)).1)
    (rightValid : Subtype (model (state.base.source right.1)).1 (model (state.base.source right.2)).1) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (selfChecks state (captured state slot name first second left right)) := by
  intro atom member
  simp only [selfChecks,captured,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact subtype_refl _
  · exact subtype_refl _
  · exact leftValid
  · exact rightValid

theorem private_models (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor)
    (first second : Nat) (distinct : first ≠ second) (names : declaration.inputNames = [first,second])
    (left right : GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name [.variables [first],.variables [second]]])
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models context.state model) :
    GeneralNominalState.Models (privateState registry context root declaration [(slot,slot)]) model ∧
      ProjectionModels context.state (report context declaration [(slot,slot)]) model := by
  have calculated := report_exact context declaration slot descriptor recorded first second left right parameters query
  have arg0 := nominal_argument_bounds context.state model models slot descriptor recorded 0 left (by rw [parameters]; rfl)
  have arg1 := nominal_argument_bounds context.state model models slot descriptor recorded 1 right (by rw [parameters]; rfl)
  obtain ⟨x,hx⟩ := arg0.1
  obtain ⟨y,hy⟩ := arg1.1
  have fit0 := arg0.2 x hx
  have fit1 := arg1.2 y hy
  have valid0 := subtype_trans fit0.1 fit0.2
  have valid1 := subtype_trans fit1.1 fit1.2
  constructor
  · unfold privateState
    rw [calculated]
    apply (GeneralNominalState.extend_models ..).mpr
    exact ⟨propagated_models context.state registry root.identity declaration first second distinct names model models left right valid0 valid1,
      self_models context.state slot descriptor.declaration.name first second left right model valid0 valid1⟩
  · rw [calculated]
    exact projection_models context.state model models slot descriptor recorded first second distinct left right parameters
end Yulang.GeneralNominalBinaryCaptureFacts
