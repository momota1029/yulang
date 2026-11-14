import Yulang.GeneralDictionaryCenteredPointReadback179
import Yulang.GeneralDictionaryReachableRootIntervals

/-! Fresh actual binder values for finite linear nominal point leaves.
No selected branch or stable journal is postulated here. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCenteredPointJoint179
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalSaturationState GeneralNominalCenteredSteps
open GeneralDictionaryLinearLeaf GeneralNominalLinearMaterializationFacts
open GeneralDictionaryCenteredPointReadback179
open CommonNominalFullCarrier
open GeneralNominalCenteredModelExtension

variable {roles : Roles.RoleDecls} (plan : Plan roles)
  (shape : LinearLeafShape plan.packet.context plan.packet.site.occurrence plan.packet.declaration)

theorem source_member (slot : Fin state.base.slots) :
    state.base.source slot ∈ GeneralNominalState.sources state := by
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_ofFn.mpr ⟨slot,rfl⟩)))

theorem capture_exact (located : plan.packet.bounds = [(shape.slot,shape.slot)]) (i : Fin shape.arity) :
    (GeneralNominalPacketSupport.capture plan.packet).inputs (shape.names i) =
      (plan.packet.context.state.base.source (shape.bounds i).1,
       plan.packet.context.state.base.source (shape.bounds i).2) := by
  have reportExact := GeneralNominalLinearCaptureFacts.report_exact plan.packet.context
    plan.packet.declaration shape.slot shape.descriptor shape.recorded shape.names shape.bounds
    shape.parameters shape.query
  unfold GeneralNominalPacketSupport.capture Packet.bindings
  rw [located,reportExact]
  simp only [bindings,GeneralNominalLinearCaptureFacts.captured,
    GeneralNominalLinearCaptureFacts.variablesReport,List.map_ofFn,Function.comp_def,
    GeneralNominalAllocation.capture]
  rw [GeneralNominalLinearCaptureFacts.occurrences_exact _ shape.names shape.distinct]

theorem binder_exact (located : plan.packet.bounds = [(shape.slot,shape.slot)]) (i : Fin shape.arity) :
    plan.binder (shape.names i) =
      if plan.packet.context.state.base.source (shape.bounds i).1 =
         plan.packet.context.state.base.source (shape.bounds i).2 then
        plan.packet.context.state.base.source (shape.bounds i).1
      else fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity
        plan.packet.declaration.id 8 (shape.names i) 0 := by
  simp only [Plan.binder]
  rw [no_output_binders _ plan.packet.checked shape.terminal]
  simp only [List.not_mem_nil,ite_false]
  rw [capture_exact plan shape located i]

/-- Extend only fresh centers; all original source values are retained exactly. -/
theorem readback_extension
    (located : plan.packet.bounds = [(shape.slot,shape.slot)])
    (below : ∀ name ∈ GeneralNominalState.sources plan.packet.context.state,
      name ≤ plan.packet.context.state.seed)
    (previous : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models plan.packet.context.state previous) :
    ∃ extended, GeneralNominalState.Models plan.packet.context.state extended ∧
      (∀ name ∈ GeneralNominalState.sources plan.packet.context.state, extended name = previous name) ∧
      Readback plan shape extended := by
  classical
  let state := plan.packet.context.state
  let lower := fun i : Fin shape.arity => state.base.source (shape.bounds i).1
  let upper := fun i : Fin shape.arity => state.base.source (shape.bounds i).2
  let origin := fun i : Fin shape.arity => Origin.nominal (.source (state.base.source shape.slot))
    shape.descriptor.declaration.name i.val
  have observed (i : Fin shape.arity) := nominal_argument_bounds
    state previous valid shape.slot shape.descriptor shape.recorded i.val (shape.bounds i)
    (by rw [shape.parameters]; simp [i.isLt])
  let actual := fun i : Fin shape.arity => Classical.choose (observed i).1
  have actual_seen (i : Fin shape.arity) : Observes previous (origin i) (actual i) :=
    Classical.choose_spec (observed i).1
  let values := fun i : Fin shape.arity => if lower i = upper i then (previous (lower i)).1 else actual i
  have center (i : Fin shape.arity) : plan.binder (shape.names i) =
      if lower i = upper i then lower i else
        fresh state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id 8 (shape.names i) 0 :=
    binder_exact plan shape located i
  have freshAbove (i : Fin shape.arity) : state.seed <
      fresh state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id 8 (shape.names i) 0 :=
    GeneralNominalIdentities.source_above_seed _ _
  have bounds (i : Fin shape.arity) : GeneralNominalCaptureMerges.Fits previous (lower i,upper i) (values i) := by
    dsimp only [values]
    split
    · rename_i point
      rw [point]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · exact (observed i).2 _ (actual_seen i)
  have readback (i : Fin shape.arity) : (∃ a, Observes previous (origin i) a) ∧
      ∀ a, Observes previous (origin i) a → Equivalent a (values i) := by
    refine ⟨⟨actual i,actual_seen i⟩,?_⟩
    intro a seen
    dsimp only [values]
    split
    · rename_i point
      have fit := (observed i).2 a seen
      change Subtype (previous (lower i)).1 a ∧ Subtype a (previous (upper i)).1 at fit
      rw [← point] at fit
      exact ⟨fit.2,fit.1⟩
    · exact nominal_observation_unique previous
        (.argument (.source (state.base.source shape.slot)) shape.descriptor.declaration.name i.val)
        a (actual i) seen (actual_seen i)
  have coherent (i j : Fin shape.arity) (same : plan.binder (shape.names i) = plan.binder (shape.names j)) :
      values i = values j := by
    rw [center i,center j] at same
    by_cases one : lower i = upper i <;> by_cases two : lower j = upper j
    · simpa only [values,one,two,ite_true] using congrArg (fun name => (previous name).1)
        (by simpa only [one,two,ite_true] using same : lower i = lower j)
    · simp only [one,two,ite_true,ite_false] at same
      have low := below (lower i) (source_member (shape.bounds i).1)
      change lower i ≤ state.seed at low
      have high := freshAbove j
      omega
    · simp only [one,two,ite_true,ite_false] at same
      have low := below (lower j) (source_member (shape.bounds j).1)
      change lower j ≤ state.seed at low
      have high := freshAbove i
      omega
    · simp only [one,two,ite_false] at same
      have keys := (GeneralNominalIdentities.source_identity state.seed _ _).mp same
      have names := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) keys
      have equal := shape.distinct names
      rw [equal]
  let arguments := fun i : Fin shape.arity =>
    (⟨⟨(lower i,upper i),plan.binder (shape.names i)⟩,origin i⟩ : NominalArgument)
  obtain ⟨extended,models,kept,holds⟩ := nested_extension state arguments previous valid values
    (fun i => ⟨source_member _,source_member _,source_member _⟩) bounds readback coherent
    (by
      intro i member
      have limit := below _ member
      change plan.binder (shape.names i) ≤ state.seed at limit
      change values i = (previous (plan.binder (shape.names i))).1
      rw [center i]
      by_cases point : lower i = upper i
      · simp [values,point]
      · have high := freshAbove i
        rw [center i] at limit
        simp only [point,ite_false] at limit
        omega)
  exact ⟨extended,models,kept,fun i => (holds i).2⟩


theorem input_bounds : List.ofFn plan.input.occurrence.demand.arguments =
    [(plan.packet.context.state.base.source shape.slot,plan.packet.context.state.base.source shape.slot)] := by
  rw [plan.input_exact]
  have recovered := GeneralDictionaryReachableRootIntervals.locate_sources plan.packet.context.state.base
    (List.ofFn plan.packet.site.occurrence.demand.arguments) [(shape.slot,shape.slot)] shape.located
  exact recovered.symm

include shape in
theorem point_input (named : plan.input.PointNames)
    (model : GeneralNominalCommonBridge.Assignment) : plan.input.Holds model := by
  intro index
  have member : plan.input.occurrence.demand.arguments index ∈
      List.ofFn plan.input.occurrence.demand.arguments := List.mem_ofFn.mpr ⟨index,rfl⟩
  rw [input_bounds plan shape] at member
  have endpoints := List.mem_singleton.mp member
  have point : (plan.input.occurrence.demand.arguments index).1 =
      (plan.input.occurrence.demand.arguments index).2 := by rw [endpoints]
  have center := named index point
  unfold GeneralNominalCaptureMerges.Fits
  rw [center,endpoints]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem centers_exact (named : plan.input.PointNames) :
    List.ofFn plan.input.center = [plan.packet.context.state.base.source shape.slot] := by
  have each (index) : plan.input.center index = (plan.input.occurrence.demand.arguments index).1 := by
    apply named
    have member : plan.input.occurrence.demand.arguments index ∈
      List.ofFn plan.input.occurrence.demand.arguments := List.mem_ofFn.mpr ⟨index,rfl⟩
    rw [input_bounds plan shape] at member
    rw [List.mem_singleton.mp member]
  calc
    List.ofFn plan.input.center = List.ofFn (fun index => (plan.input.occurrence.demand.arguments index).1) :=
      congrArg List.ofFn (funext each)
    _ = (List.ofFn plan.input.occurrence.demand.arguments).map Prod.fst := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [input_bounds plan shape]; rfl

/-- Common initial centered model for arbitrary finite linear nominal leaves.
Original source values are unchanged, including point-interval binders. -/
theorem joint_model
    (located : plan.packet.bounds = [(shape.slot,shape.slot)])
    (named : plan.input.PointNames)
    (below : ∀ name ∈ GeneralNominalState.sources plan.packet.context.state,
      name ≤ plan.packet.context.state.seed)
    (previous : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models plan.packet.context.state previous) :
    ∃ extended,
      Models (initialAt plan.packet.context plan.input) extended ∧ plan.Holds extended ∧
      ∀ name ∈ GeneralNominalState.sources plan.packet.context.state, extended name = previous name := by
  obtain ⟨extended,source,kept,readback⟩ := readback_extension plan shape located below previous valid
  have input := point_input plan shape named extended
  exact ⟨extended,(initialAt_models _ _ _).mpr ⟨source,input⟩,
    (holds_iff_readback plan shape located (centers_exact plan shape named) extended source input).mpr readback,kept⟩

end Yulang.GeneralDictionaryCenteredPointJoint179
