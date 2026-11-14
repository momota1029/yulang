import Yulang.GeneralNominalHeadRecursiveExtension188
import Yulang.GeneralNominalRequestCompleteness

/-! Structural output translation coverage supplies actual EffectsReady without
assuming an output model. This permits named requests; unsupported translations
and missing associated equations remain explicit restrictions. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalOutputCoverage189
open GeneralNominalInspection (Query)
open GeneralNominalMaterialization
open GeneralNominalHeadMatchMass (Complete)
open GeneralNominalCenteredHeadOutputs
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters

mutual
 theorem schema_known (query : Query) (origin : GeneralNominalRecursiveInspection.Origin)
     (mode : Mode) (complete : Complete query) : (schema query origin mode).unknown = false := by
   cases query with
   | variables | scalar => simp only [schema]
   | deferred => simp only [Complete] at complete
   | node shape children =>
     simp only [Complete] at complete
     simp only [schema]
     exact schemas_known children _ mode 0 complete
   | nominal name children =>
     simp only [Complete] at complete
     simp only [schema]
     exact schemas_known children _ .actual 0 complete
   termination_by sizeOf query
 theorem schemas_known (queries : List Query) (origins : Nat → GeneralNominalRecursiveInspection.Origin)
     (mode : Mode) (offset : Nat) (complete : ∀ query ∈ queries, Complete query) :
     (schemas queries origins mode offset).unknown = false := by
   cases queries with
   | nil => simp [schemas]
   | cons first rest =>
     simp only [schemas,Schema.append]
     exact Bool.or_eq_false_iff.mpr ⟨schema_known first _ mode (complete first (by simp)),
       schemas_known rest origins mode (offset+1) (fun query member => complete query (List.mem_cons_of_mem _ member))⟩
   termination_by sizeOf queries
end

theorem generated_known (state : GeneralNominalState.State) (interpretation : GeneralNominalInspection.Interpretation)
    (requests : List Request)
    (complete : ∀ request ∈ requests, Complete
      (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern))) :
    (generated state interpretation requests).unknown = false := by
  induction requests with
  | nil => simp [generated]
  | cons first rest ih =>
    simp only [generated,List.map_cons,List.foldr_cons,Schema.append]
    exact Bool.or_eq_false_iff.mpr ⟨schema_known _ _ _ (complete first (by simp)),
      ih (fun request member => complete request (List.mem_cons_of_mem _ member))⟩

theorem generated_known_iff (state : GeneralNominalState.State) (interpretation : GeneralNominalInspection.Interpretation)
    (requests : List Request) :
    (generated state interpretation requests).unknown = false ↔
      ∀ request ∈ requests, Complete (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) :=
  ⟨GeneralNominalRequestCompleteness.generated_complete state interpretation requests,
    generated_known state interpretation requests⟩

theorem effects_ready (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (candidate : Plan roles)
    (coverage : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests state root,
      ∃ equation ∈ candidate.packet.declaration.associated, equation.name = output.name)
    (translated : ∀ equation ∈ candidate.packet.declaration.associated,
      Complete (GeneralNominalInspection.translate candidate.packet.context.state.constructors
        candidate.packet.context.interpretation (GeneralDeclarationPatterns.normalize equation.rhs))) :
    EffectsReady state root candidate := by
  refine ⟨coverage,generated_known _ _ _ ?_⟩
  intro request member
  obtain ⟨output,_,within⟩ := List.mem_flatMap.mp member
  obtain ⟨equation,found,rfl⟩ := List.mem_map.mp within
  exact translated equation (List.mem_of_find?_eq_some (Option.mem_toList.mp found))

/-- Initial selection with named output requests. The additional hypotheses
are visible equation coverage and finite query syntax, not positive models. -/
theorem selected_named_outputs
    {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state : GeneralNominalCenteredHeadStepEffects.State roles}
    {key : Nat} {children : List (Occurrence roles)}
    (checked : Checked registry)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (selected : GeneralNominalCenteredHeadWFBoundary.Local registry state root (.selected key children))
    (coverage : ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
      ∀ output ∈ root.demand.outputs, ∃ equation ∈ declaration.associated, equation.name = output.name)
    (translated : ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
      ∀ equation ∈ declaration.associated, Complete
        (GeneralNominalInspection.translate state.core.erased.current.context.state.constructors
          state.core.erased.current.context.interpretation (GeneralDeclarationPatterns.normalize equation.rhs))) :
    ∃ model, GeneralNominalCenteredHeadStepEffects.Models state model ∧
      ChosenClassEffects registry state.core root key model := by
  apply GeneralNominalHeadRecursiveExtension188.selected_effects checked source selected
  intro candidate frame
  apply effects_ready
  · intro output member
    have requestEq : GeneralNominalCenteredHeadOutputs.requests state.core root = root.demand.outputs := by
      obtain ⟨⟨context,labels,formed,point,ground,equal⟩,covered⟩ := source
      subst state
      exact GeneralNominalHeadInitialEffects188.initial_requests context
    rw [requestEq] at member
    exact coverage candidate.packet.declaration frame.visible frame.role_eq output member
  · intro equation member
    rw [frame.context_eq]
    exact translated candidate.packet.declaration frame.visible frame.role_eq equation member

end Yulang.GeneralNominalOutputCoverage189
