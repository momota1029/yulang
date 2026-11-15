import Yulang.GeneralDictionaryDefaultRevisionEquivalence210

/-! Finite certified descriptor-refresh traces preserve complete structural
source dictionaries. Intermediate models and syntax are derived along the trace.
The relation contains no installation or merge and is not general reachability. -/
namespace Yulang.GeneralDictionaryDefaultRevisionTrace210
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultRevisionEvidence210 (Structural)
open GeneralDictionaryDefaultRevisionEquivalence210
variable {roles : Roles.RoleDecls}

inductive Trace : State roles → State roles → Prop where
  | refl (state) : Trace state state
  | next {first current} (prior : Trace first current)
      (revision : GeneralNominalReobservationSteps.Revision current.core.erased.current)
      (certificate : GeneralNominalCenteredHeadMatStepRefresh.Reobserve current revision) :
      Trace first (change current revision.result)

 theorem trans (first : Trace a b) (last : Trace b c) : Trace a c := by
  induction last with
  | refl => exact first
  | next _ revision certificate ih => exact .next ih revision certificate

 theorem models (trace : Trace first last) : Models last model ↔ Models first model := by
  induction trace with
  | refl => exact Iff.rfl
  | next _ _ certificate ih =>
    exact (GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate).trans ih

 theorem structural (trace : Trace first last) :
    Structural registry last.core.erased.current.context ↔
      Structural registry first.core.erased.current.context := by
  induction trace with
  | refl => exact Iff.rfl
  | next _ revision _ ih => exact (structural_iff revision).trans ih

 theorem instance_iff_trace (trace : Trace first last)
    (shape : Structural registry first.core.erased.current.context)
    (valid : Models first model) :
    GeneralDictionaryTotalEvidence206.Instance registry last.core model focus key children ↔
      GeneralDictionaryTotalEvidence206.Instance registry first.core model focus key children := by
  induction trace with
  | refl => exact Iff.rfl
  | next prior revision certificate ih =>
    have current := (models prior).mpr valid
    exact (instance_iff revision ((structural prior).mpr shape) current
      ((GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate).mpr current)).trans ih

 theorem evidence (trace : Trace first last)
    (shape : Structural registry first.core.erased.current.context)
    (valid : Models first model) :
    GeneralDictionaryTotalEvidence206.Evidence registry last.core model focus payload ↔
      GeneralDictionaryTotalEvidence206.Evidence registry first.core model focus payload := by
  induction trace with
  | refl => exact Iff.rfl
  | next prior revision certificate ih =>
    exact (certified_evidence_iff revision certificate ((structural prior).mpr shape)
      ((models prior).mpr valid)).trans ih
end Yulang.GeneralDictionaryDefaultRevisionTrace210
