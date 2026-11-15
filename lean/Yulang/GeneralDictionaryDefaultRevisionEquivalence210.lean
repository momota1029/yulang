import Yulang.GeneralDictionaryDefaultRevisionEvidence210

set_option backward.isDefEq.respectTransparency false

/-! Structural dictionary evidence is invariant across a certified descriptor
revision. The inverse is a logical view change, not an authorized operational
step: it need not improve precision. -/
namespace Yulang.GeneralDictionaryDefaultRevisionEquivalence210
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultRevisionEvidence210 (Structural)
variable {roles : Roles.RoleDecls} {state : State roles}

 def inverse (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) :
    GeneralNominalReobservationSteps.Revision (change state revision.result).core.erased.current where
  entries := state.core.erased.current.context.state.nominals
  catalogue := state.core.erased.current.context.state.catalogue
  opaqueHeads := state.core.erased.current.context.state.bodies_opaque
  domain := fun slot => (revision.domain slot).symm

 theorem inverse_result (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) :
    change (change state revision.result) (inverse revision).result = state := by
  rfl

 theorem structural_iff (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) :
    Structural registry (change state revision.result).core.erased.current.context ↔
      Structural registry state.core.erased.current.context := Iff.rfl

 theorem instance_iff (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (shape : Structural registry state.core.erased.current.context)
    (before : Models state model) (after : Models (change state revision.result) model) :
    GeneralDictionaryTotalEvidence206.Instance registry (change state revision.result).core model focus key children ↔
      GeneralDictionaryTotalEvidence206.Instance registry state.core model focus key children := by
  constructor
  · intro source
    have result := GeneralDictionaryDefaultRevisionEvidence210.evidence_instance (inverse revision)
      ((structural_iff revision).mpr shape) ((inverse_result revision).symm ▸ before) source
    exact (inverse_result revision) ▸ result
  · exact GeneralDictionaryDefaultRevisionEvidence210.evidence_instance revision shape after

 theorem evidence_iff (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (shape : Structural registry state.core.erased.current.context)
    (before : Models state model) (after : Models (change state revision.result) model) :
    GeneralDictionaryTotalEvidence206.Evidence registry (change state revision.result).core model focus payload ↔
      GeneralDictionaryTotalEvidence206.Evidence registry state.core model focus payload := by
  constructor
  · intro source
    have result := GeneralDictionaryDefaultRevisionEvidence210.evidence (inverse revision)
      ((structural_iff revision).mpr shape) ((inverse_result revision).symm ▸ before) source
    exact (inverse_result revision) ▸ result
  · exact GeneralDictionaryDefaultRevisionEvidence210.evidence revision shape after

 theorem certified_evidence_iff
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Reobserve state revision)
    (shape : Structural registry state.core.erased.current.context)
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Evidence registry (change state revision.result).core model focus payload ↔
      GeneralDictionaryTotalEvidence206.Evidence registry state.core model focus payload :=
  evidence_iff revision shape valid ((GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate).mpr valid)

end Yulang.GeneralDictionaryDefaultRevisionEquivalence210
