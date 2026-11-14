import Yulang.GeneralNominalInitialFrameUnique189
import Yulang.GeneralNominalOutputCoverage189
import Yulang.GeneralNominalHeadLeafPlan189

set_option backward.isDefEq.respectTransparency false

/-! At an actual initial frame the named-output rejection predicate has an exact
same-plan feasibility interpretation. The positive head baseline is derived.
This is semantic exactness, not a decision algorithm for output equations. -/
namespace Yulang.GeneralNominalInitialOutputExact189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : State roles} {key : Nat} {children : List (Occurrence roles)}

theorem conflict_iff (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (unique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (ready : EffectsReady state.core root candidate) :
    GeneralNominalCenteredHeadStepBoundary.OutputConflict registry state root key ↔
      ¬ ∃ model, Models state model ∧ HeadEquations candidate model ∧
        OutputEquations state.core root candidate model := by
  obtain ⟨model,valid,head,_,_⟩ := GeneralNominalHeadRecursiveExtension188.initial_extension checked source candidate frame
  have baseline : ∃ model, Models state model ∧ ChosenHead registry state.core root key model :=
    ⟨model,valid,⟨children,unique⟩,candidate,frame,ready,head⟩
  constructor
  · rintro ⟨_,absent⟩ ⟨model,valid,head,outputs⟩
    exact absent ⟨model,valid,⟨children,unique⟩,candidate,frame,ready,head,outputs⟩
  · intro absent
    refine ⟨baseline,?_⟩
    rintro ⟨model,valid,effects⟩
    have actual := GeneralNominalInitialFrameUnique189.effects_on_frame checked state source candidate frame effects
    exact absent ⟨model,valid,actual.2⟩

theorem no_output_conflict (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (empty : root.demand.outputs = []) :
    ¬ GeneralNominalCenteredHeadStepBoundary.OutputConflict registry state root key := by
  intro conflict
  obtain ⟨_,_,⟨children,unique⟩,_⟩ := conflict.1
  have requestsEmpty : requests state.core root = [] := by
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    rw [GeneralNominalHeadInitialEffects188.initial_requests,empty]
  have absent := (conflict_iff checked source unique candidate frame
    (GeneralNominalHeadInitialEffects188.empty_effects_ready requestsEmpty candidate)).mp conflict
  obtain ⟨model,valid,head,_,_⟩ := GeneralNominalHeadRecursiveExtension188.initial_extension checked source candidate frame
  exact absent ⟨model,valid,head,GeneralNominalHeadLeafPlan189.output_equations_empty candidate requestsEmpty model⟩

theorem selected_named_frame (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (coverage : ∀ output ∈ root.demand.outputs,
      ∃ equation ∈ candidate.packet.declaration.associated, equation.name = output.name)
    (translated : ∀ equation ∈ candidate.packet.declaration.associated,
      GeneralNominalHeadMatchMass.Complete (GeneralNominalInspection.translate
        candidate.packet.context.state.constructors candidate.packet.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs))) :
    ∃ model, Models state model ∧ HeadEquations candidate model ∧
      OutputEquations state.core root candidate model := by
  apply GeneralNominalInitialFrameUnique189.selected_frame_model checked state source selected candidate frame
  apply GeneralNominalOutputCoverage189.effects_ready state.core root candidate _ translated
  intro output member
  have requestEq : requests state.core root = root.demand.outputs := by
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,covered⟩ := source
    subst state
    exact GeneralNominalHeadInitialEffects188.initial_requests context
  exact coverage output (requestEq ▸ member)

end Yulang.GeneralNominalInitialOutputExact189
