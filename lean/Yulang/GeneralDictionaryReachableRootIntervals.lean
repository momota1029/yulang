import Yulang.GeneralDictionaryValueEvidence

/-! Initial-source interval inequalities survive the actual Value trace. This
is a property of the original root, not arbitrary newly emitted children. -/
namespace Yulang.GeneralDictionaryReachableRootIntervals
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport

theorem root_intervals (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model) (index) :
    CommonNominalFullCarrier.Subtype (model (root.demand.arguments index).1).1
      (model (root.demand.arguments index).2).1 := by
  obtain ⟨start,⟨context,initial,rfl⟩,path⟩ := reachable
  exact initial.intervals model
    ((GeneralNominalSaturationState.initial_models context root model).mp
      (GeneralNominalValueSteps.steps_models path model valid)) index

theorem locate_sources (state : GeneralSourceState.State) (inputs : List GeneralSourceState.Interval)
    (bounds : List (GeneralCandidateInspection.Bounds state))
    (located : GeneralCandidateBoundaryParts.locate state inputs = some bounds) :
    bounds.map (fun pair => (state.source pair.1,state.source pair.2)) = inputs := by
  induction inputs generalizing bounds with
  | nil => simpa [GeneralCandidateBoundaryParts.locate] using located.symm
  | cons pair rest ih =>
    cases hlower : GeneralDictionaryBinderLocations.sourceSlot state pair.1 with
    | none => simp [GeneralCandidateBoundaryParts.locate,List.mapM_cons,hlower] at located
    | some lower =>
      cases hupper : GeneralDictionaryBinderLocations.sourceSlot state pair.2 with
      | none => simp [GeneralCandidateBoundaryParts.locate,List.mapM_cons,hlower,hupper] at located
      | some upper =>
        have mapped : ((GeneralCandidateBoundaryParts.locate state rest).bind
            (fun tail => some ((lower,upper) :: tail))) = some bounds := by
          simpa only [GeneralCandidateBoundaryParts.locate,List.mapM_cons,hlower,hupper,
            Option.bind_some,pure,Bind.bind] using located
        cases htail : GeneralCandidateBoundaryParts.locate state rest with
        | none => simp [htail] at mapped
        | some tail =>
          have equal : (lower,upper) :: tail = bounds := by simpa [htail] using mapped
          subst bounds
          have lo := (GeneralDictionaryBinderLocations.sourceSlot_exact state pair.1 lower).mp hlower
          have hi := (GeneralDictionaryBinderLocations.sourceSlot_exact state pair.2 upper).mp hupper
          simp only [List.map_cons,lo,hi]
          exact congrArg (List.cons pair) (ih _ htail)
theorem located_intervals (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state))
    (located : GeneralNominalCandidates.arguments state.current.context root = some bounds)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model) :
    ∀ pair ∈ bounds, CommonNominalFullCarrier.Subtype
      (model (state.current.context.state.base.source pair.1)).1
      (model (state.current.context.state.base.source pair.2)).1 := by
  intro pair member
  have same := locate_sources state.current.context.state.base (List.ofFn root.demand.arguments) bounds located
  have present : (state.current.context.state.base.source pair.1,state.current.context.state.base.source pair.2) ∈
      List.ofFn root.demand.arguments := by
    rw [←same]
    exact List.mem_map.mpr ⟨pair,member,rfl⟩
  obtain ⟨index,equal⟩ := List.mem_ofFn.mp present
  have result := root_intervals registry root state reachable model valid index
  simpa only [equal] using result
end Yulang.GeneralDictionaryReachableRootIntervals
