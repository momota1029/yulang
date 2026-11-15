import Yulang.GeneralDictionaryDefaultEvidence204

/-! Auditable boundaries for the default extension: unique provenance, exact
total equations, and conservation of the complete old explicit-body judgment. -/
namespace Yulang.GeneralDictionaryDefaultEvidence204Laws
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryDefaultEvidence204 GeneralDictionaryAssociatedProvenance
open GeneralNominalCenteredHeadMatEffects GeneralNominalCenteredHeadMatExpressions
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : Assignment}
variable {output : GeneralSourceState.Output} {body : Body} {expression : Expr}

/-- The checked declaration makes the provenance unique, so a witness cannot
switch to a convenient default or explicit body when checking the equation. -/
theorem output_body_unique (one : Supplies roles plan.packet.declaration output.name first)
    (two : Supplies roles plan.packet.declaration output.name last) : first = last :=
  supplies_unique roles plan.packet.declaration plan.packet.checked.identified.2.2.1 output.name first last one two

theorem output_equation (witness : OutputWitness plan model output)
    (supplied : Supplies roles plan.packet.declaration output.name body)
    (translated : compileBody plan body = some expression) :
    Equivalent (model output.target).1 (value (bodyVariables plan model body) .actual expression) := by
  obtain ⟨chosen,present,_,valid⟩ := witness
  have same := output_body_unique (output := output) present supplied
  subst chosen
  exact (body_equation translated).mp valid

theorem output_lookup (witness : OutputWitness plan model output) :
    ∃ body, lookup roles plan.packet.declaration output.name = some body ∧
      (∃ expression, compileBody plan body = some expression) ∧ BodyHolds plan output.target model body := by
  obtain ⟨body,supplied,compiled,valid⟩ := witness
  exact ⟨body,(lookup_exact roles plan.packet.declaration plan.packet.checked.identified.2.2.1 _ _).mpr supplied,compiled,valid⟩

/-- Restriction to explicitly supplied outputs recovers the legacy certificate
without changing children, declaration, source snapshot, or final assignment. -/
theorem explicit_conservative
    (source : Certificate registry state model root key children plan)
    (explicit : ∀ output ∈ root.demand.outputs, ∃ equation,
      Supplies roles plan.packet.declaration output.name (.explicit equation)) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.erased.current.context model root key children := by
  apply certificate_legacy source
  intro output member
  obtain ⟨equation,present⟩ := explicit output member
  cases present with
  | explicit equation visible named => exact ⟨equation,visible,named⟩

/-- Actual total class effects yield the new local output rule, retaining
lookup provenance and rejecting a failed translation rather than accepting its
empty equation list. -/
theorem output_of_class_effects
    (ready : Ready state root plan)
    (valid : ClassEffects state root plan model)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state root) :
    OutputWitness plan model output := by
  obtain ⟨body,found,complete⟩ := ready output member
  refine ⟨body,(lookup_exact roles plan.packet.declaration plan.packet.checked.identified.2.2.1 _ _).mp found,
    ?_,valid.1 output member body found⟩
  cases translated : compileBody plan body with
  | none => simp [bodySchema,translated] at complete
  | some expression => exact ⟨expression,rfl⟩

/-- An actual frame and its same-model semantic data supply the certificate.
The residual partial branch/completion assumptions are explicit; this is not
the unconditional selected-node theorem. -/
theorem certificate_of_frame
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state root key plan)
    (children_eq : children = plan.packet.children)
    (complete : (GeneralNominalRecursiveCandidates.generated plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds).unknown = false)
    (branch : GeneralNominalRecursiveCandidates.BranchModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds model)
    (centers : plan.input.Holds model)
    (ready : Ready state root plan) (valid : ClassEffects state root plan model) :
    Certificate registry state model root key children plan := by
  refine ⟨frame.registry_eq,frame.context_eq,frame.occurrence_eq,frame.key_eq,frame.visible,
    frame.role_eq,?_,?_,complete,children_eq,frame.prepared.1,branch,frame.center_recorded,centers,?_⟩
  · exact frame.located
  · have prepared : GeneralNominalCenteredHeadCandidates.Prepared registry plan.packet.context root plan.packet.declaration :=
      frame.context_eq.symm ▸ frame.prepared
    obtain ⟨_,_,_,bounds,located,finished,_⟩ := prepared
    have same : bounds = plan.packet.bounds := by
      apply Option.some.inj
      exact located.symm.trans frame.located
    subst bounds
    exact finished
  · intro output member
    apply output_of_class_effects ready valid
    exact GeneralNominalCenteredHeadOutputs.request_retained plan.packet.site frame.raw_recorded
      (by rw [frame.occurrence_eq]; exact .refl _)
      (frame.occurrence_eq.symm ▸ member)

end Yulang.GeneralDictionaryDefaultEvidence204Laws
