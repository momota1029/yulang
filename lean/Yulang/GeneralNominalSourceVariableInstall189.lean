import Yulang.GeneralNominalSingleVariableModels189

/-! A source-level single-variable leaf head discharges the inspection-shape,
input-name and point-bound premises of named-output installation. The root may
request named outputs; explicit coverage and supported RHS translation remain. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalSourceVariableInstall189
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem source_shape (candidate : Plan roles) (head : candidate.packet.declaration.head = [.var name]) :
    GeneralNominalInspection.queries candidate.packet.context.state candidate.packet.context.interpretation
      candidate.packet.declaration = [.variables [name]] ∧ candidate.packet.declaration.inputNames = [name] := by
  constructor <;> simp [GeneralNominalInspection.queries,Declaration.normalHead,Declaration.inputNames,
    head,normalizeArgs,normalize,variablesArgs,Pattern.variables,GeneralNominalInspection.translate]

theorem initial_bounds (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (head : candidate.packet.declaration.head = [.var name]) :
    ∃ slot : Fin candidate.packet.context.state.base.slots, candidate.packet.bounds = [(slot,slot)] := by
  have arity : (roles root.demand.role).arity = 1 := by
    have signature := candidate.packet.checked.signature.1
    simpa only [head,List.length_singleton,frame.role_eq] using signature.symm
  have mapped := GeneralNominalPacketCaptureReadback.locate_sources
    candidate.packet.context.state.base (List.ofFn root.demand.arguments) candidate.packet.bounds frame.located
  have length : candidate.packet.bounds.length = 1 := by
    have sizes := congrArg List.length mapped
    simpa only [List.length_map,List.length_ofFn,arity] using sizes
  have singleton : ∃ interval, candidate.packet.bounds = [interval] := by
    cases h : candidate.packet.bounds with
    | nil => simp [h] at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first,rfl⟩
      | cons second tail => simp [h] at length
  obtain ⟨interval,equal⟩ := singleton
  have point := (GeneralNominalHeadPointBounds188.boundary_initial_point_bounds state source candidate frame 0 interval
    (by simp [equal])).1
  refine ⟨interval.1,?_⟩
  rw [equal]
  cases interval with
  | mk first last => simp only at point; subst last; rfl

theorem selected_installable (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (head : candidate.packet.declaration.head = [.var name])
    (leaf : candidate.packet.declaration.requirements = [])
    (coverage : ∀ output ∈ root.demand.outputs,
      ∃ equation ∈ candidate.packet.declaration.associated, equation.name = output.name)
    (translated : ∀ equation ∈ candidate.packet.declaration.associated,
      GeneralNominalHeadMatchMass.Complete (GeneralNominalInspection.translate
        candidate.packet.context.state.constructors candidate.packet.context.interpretation (normalize equation.rhs))) :
    ∃ support, GeneralNominalCenteredHeadStepKernel.Installable registry state candidate support := by
  obtain ⟨slot,bounds⟩ := initial_bounds source candidate frame head
  have shape := source_shape candidate head
  apply GeneralNominalSingleVariableModels189.selected_named_installable checked source selected candidate frame slot
    shape.1 bounds shape.2 leaf
  apply GeneralNominalOutputCoverage189.effects_ready state.core root candidate _ translated
  intro output member
  have requestEq : requests state.core root = root.demand.outputs := by
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,covered⟩ := source
    subst state
    exact GeneralNominalHeadInitialEffects188.initial_requests context
  exact coverage output (requestEq ▸ member)

/-- Source declarations, not caller-supplied query/bound evidence, describe
this fragment. The actual selected survivor supplies the plan and frame. -/
theorem selected_source_candidate (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (declarations : ∀ declaration ∈ registry.declarations, declaration.id = key →
      (∃ name, declaration.head = [.var name]) ∧ declaration.requirements = [] ∧
      (∀ output ∈ root.demand.outputs, ∃ equation ∈ declaration.associated, equation.name = output.name) ∧
      ∀ equation ∈ declaration.associated, GeneralNominalHeadMatchMass.Complete
        (GeneralNominalInspection.translate state.core.erased.current.context.state.constructors
          state.core.erased.current.context.interpretation (normalize equation.rhs))) :
    ∃ candidate support, Frame registry state.core root key candidate ∧
      candidate.packet.children = children ∧ GeneralNominalCenteredHeadStepKernel.Installable registry state candidate support := by
  have old := GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected
  have unique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children := by
    cases old with
    | selected _ unique _ => exact unique
  obtain ⟨candidate,frame,kids⟩ := GeneralNominalHeadInitialFrame188.initial_frame state source unique.1
  obtain ⟨⟨name,head⟩,leaf,coverage,translated⟩ := declarations candidate.packet.declaration frame.visible frame.key_eq
  have supported : ∀ equation ∈ candidate.packet.declaration.associated,
      GeneralNominalHeadMatchMass.Complete (GeneralNominalInspection.translate candidate.packet.context.state.constructors
        candidate.packet.context.interpretation (normalize equation.rhs)) := by
    rw [frame.context_eq]
    exact translated
  obtain ⟨support,enabled⟩ := selected_installable checked source selected candidate frame head leaf coverage supported
  exact ⟨candidate,support,frame,kids,enabled⟩

end Yulang.GeneralNominalSourceVariableInstall189
