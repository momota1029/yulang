import Yulang.GeneralDictionaryJointMerge
import Yulang.GeneralDictionaryRecursiveEvidenceFacts

/-! A concrete associated-output facet derived from actual generated source
requests, without assuming a global AssociatedMeaning. This covers scalar
requests only, not variable or recursive associated-expression coherence. -/
namespace Yulang.GeneralDictionaryScalarMerge
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates
open GeneralNominalDemandMerging (Site outputAtoms)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

/-- Matching named scalar requests in two materialized branches force every
new merge equation at their common assignment. The declarations may differ;
the common scalar mapping is an explicit checked-request-schema premise. -/
theorem output_atoms_of_scalar_tests (registry : Registry) (state : State roles)
    (first last : Site roles) (leftDecl rightDecl : Declaration)
    (leftChecked : DeclarationChecked registry.constructors roles leftDecl)
    (rightChecked : DeclarationChecked registry.constructors roles rightDecl)
    (leftBounds rightBounds : List (GeneralNominalInspection.Bounds state.context.state))
    (model : Assignment)
    (left : BranchModels registry state.context first.occurrence leftDecl leftChecked leftBounds model)
    (right : BranchModels registry state.context last.occurrence rightDecl rightChecked rightBounds model)
    (scalars : Nat → Inference.Base)
    (leftTests : ∀ output ∈ first.occurrence.demand.outputs,
      (.source output.target,.scalar (scalars output.name)) ∈
        (generated registry state.context first.occurrence leftDecl leftChecked leftBounds).tests)
    (rightTests : ∀ output ∈ last.occurrence.demand.outputs,
      (.source output.target,.scalar (scalars output.name)) ∈
        (generated registry state.context last.occurrence rightDecl rightChecked rightBounds).tests) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model (outputAtoms first last) := by
  apply (GeneralNominalDemandMerging.output_atoms_exact first last model).mpr
  intro a ha b hb same
  have one := GeneralDictionaryRecursiveEvidence.generated_scalar_equation registry state.context
    first.occurrence leftDecl leftChecked leftBounds model left a.target (scalars a.name) (leftTests a ha)
  have two := GeneralDictionaryRecursiveEvidence.generated_scalar_equation registry state.context
    last.occurrence rightDecl rightChecked rightBounds model right b.target (scalars b.name) (rightTests b hb)
  rw [← same] at two
  exact ⟨CommonNominalFullCarrier.subtype_trans one.1 two.2,
    CommonNominalFullCarrier.subtype_trans two.1 one.2⟩

/-- The scalar bridge transports an arbitrary COMPLETE recursive dictionary,
not merely the output facet, through the existing merge transformer. -/
theorem evidence_merge_of_scalar_tests (registry : Registry) (state : State roles)
    (first last : Site roles) (leftDecl rightDecl : Declaration)
    (leftChecked : DeclarationChecked registry.constructors roles leftDecl)
    (rightChecked : DeclarationChecked registry.constructors roles rightDecl)
    (leftBounds rightBounds : List (GeneralNominalInspection.Bounds state.context.state))
    (model : Assignment)
    (left : BranchModels registry state.context first.occurrence leftDecl leftChecked leftBounds model)
    (right : BranchModels registry state.context last.occurrence rightDecl rightChecked rightBounds model)
    (scalars : Nat → Inference.Base)
    (leftTests : ∀ output ∈ first.occurrence.demand.outputs,
      (.source output.target,.scalar (scalars output.name)) ∈
        (generated registry state.context first.occurrence leftDecl leftChecked leftBounds).tests)
    (rightTests : ∀ output ∈ last.occurrence.demand.outputs,
      (.source output.target,.scalar (scalars output.name)) ∈
        (generated registry state.context last.occurrence rightDecl rightChecked rightBounds).tests)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (given : GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (merge state first last).context model root payload :=
  (GeneralDictionaryJointMerge.evidence_merge_iff registry state first last model root payload).mpr
    ⟨given,output_atoms_of_scalar_tests registry state first last leftDecl rightDecl leftChecked rightChecked
      leftBounds rightBounds model left right scalars leftTests rightTests⟩
end Yulang.GeneralDictionaryScalarMerge
