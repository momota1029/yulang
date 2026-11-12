import Yulang.GeneralNominalRecursiveCandidates

/-! General facts for one variable argument of a nominal head. The descriptor
bounds are arbitrary, including different source identities and denotations.
These lemmas use the general recursive inspector and candidate model. -/
namespace Yulang.GeneralNominalUnaryCaptureFacts

open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates
open GeneralDeclarations
open CommonNominalFullCarrier

def captured (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (name binder : Nat) (bounds : GeneralNominalInspection.Bounds state) : Report state where
  captures := [⟨binder,bounds,some (.nominal (.source (state.base.source slot)) name 0)⟩]
  inspected := [(slot,slot)]
  checked := [(slot,slot),(slot,slot),bounds]
  anchors := [(.nominal (.source (state.base.source slot)) name 0,bounds)]

theorem report_exact (context : Context) (declaration : Declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor)
    (binder : Nat) (bounds : GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = [.type bounds])
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name [.variables [binder]]]) :
    report context declaration [(slot,slot)] = captured context.state slot descriptor.declaration.name binder bounds := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,recorded,typeArguments,parameters,Report.visit,Report.append,captured]

theorem projection_models (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals slot = some descriptor)
    (binder : Nat) (bounds : GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = [.type bounds]) :
    ProjectionModels state (captured state slot descriptor.declaration.name binder bounds) model := by
  have argument := nominal_argument_bounds state model models slot descriptor recorded 0 bounds (by rw [parameters]; rfl)
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    have same := List.mem_singleton.mp member; subst anchor
    exact argument
  · intro test member; cases member
  · intro first one last two _ ref origin actual seen
    have a := List.mem_singleton.mp one; have b := List.mem_singleton.mp two
    subst first; subst last
    have equal := Option.some.inj origin
    subst ref
    exact argument.2 actual seen
  · intro first one last two _ a b ha hb x y hx hy
    have firstEq := List.mem_singleton.mp one; have lastEq := List.mem_singleton.mp two
    subst first; subst last
    have ae := Option.some.inj ha; have be := Option.some.inj hb
    subst a; subst b
    exact nominal_observation_unique model
      (.argument (.source (state.base.source slot)) descriptor.declaration.name 0) x y hx hy

theorem propagated_models (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (binder : Nat) (names : declaration.inputNames = [binder])
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (bounds : GeneralNominalInspection.Bounds state)
    (consistent : Subtype (model (state.base.source bounds.1)).1 (model (state.base.source bounds.2)).1) :
    GeneralNominalState.Models (GeneralNominalAllocation.propagate state registry invocation declaration
      [(binder,(state.base.source bounds.1,state.base.source bounds.2))]) model := by
  apply (GeneralNominalAllocation.propagate_models ..).mpr
  refine ⟨models,?_,?_⟩
  · intro first one last two _
    have a := List.mem_singleton.mp one; have b := List.mem_singleton.mp two
    subst first; subst last; exact consistent
  · simp [GeneralNominalAllocation.merges,names,GeneralNominalAllocation.occurrences]

theorem self_models (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (name binder : Nat) (bounds : GeneralNominalInspection.Bounds state)
    (model : GeneralNominalCommonBridge.Assignment)
    (consistent : Subtype (model (state.base.source bounds.1)).1 (model (state.base.source bounds.2)).1) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (selfChecks state (captured state slot name binder bounds)) := by
  intro atom member
  simp only [selfChecks,captured,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact subtype_refl _
  · exact subtype_refl _
  · exact consistent

theorem initial_fresh (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (bounded : (GeneralNominalState.sources state).foldr max 0 ≤ state.seed) :
    GeneralNominalAllocation.Fresh state registry invocation := by
  intro key _ collision
  have below := Nat.le_trans (GeneralNominalAllocation.member_le_max _ _ collision) bounded
  exact False.elim (GeneralNominalAllocation.source_initial_fresh state registry invocation key _ below rfl)

theorem private_models (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor)
    (binder : Nat) (names : declaration.inputNames = [binder])
    (bounds : GeneralNominalInspection.Bounds context.state) (parameters : descriptor.arguments = [.type bounds])
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name [.variables [binder]]])
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models context.state model) :
    GeneralNominalState.Models (privateState registry context root declaration [(slot,slot)]) model ∧
      ProjectionModels context.state (report context declaration [(slot,slot)]) model := by
  have calculated := report_exact context declaration slot descriptor recorded binder bounds parameters query
  have argument := nominal_argument_bounds context.state model models slot descriptor recorded 0 bounds (by rw [parameters]; rfl)
  obtain ⟨actual,seen⟩ := argument.1
  have fit := argument.2 actual seen
  have consistent := subtype_trans fit.1 fit.2
  constructor
  · unfold privateState
    rw [calculated]
    apply (GeneralNominalState.extend_models ..).mpr
    exact ⟨propagated_models context.state registry root.identity declaration binder names model models bounds consistent,
      self_models context.state slot descriptor.declaration.name binder bounds model consistent⟩
  · rw [calculated]
    exact projection_models context.state model models slot descriptor recorded binder bounds parameters

end Yulang.GeneralNominalUnaryCaptureFacts
