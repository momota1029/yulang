import Yulang.GeneralDictionaryFiniteEqualityCompletion

/-! One real equality-complete endpoint preserves all Joint candidates and
recursive dictionaries. Classical existence is not an executable classifier;
no claim of full support Stable or V5 completion is made. -/
namespace Yulang.GeneralDictionaryFiniteEqualityObservations
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralDictionaryFiniteEqualityCompletion GeneralNominalJointCandidates
variable {roles : Roles.RoleDecls}

/-- The existential endpoint is chosen BEFORE all observation quantifiers.
No per-root, per-key, per-assignment or per-payload endpoint choice is allowed. -/
theorem complete_observations (registry : Registry) (root : Occurrence roles)
    (before : GeneralNominalSupport.Tracked roles) :
    ∃ after : GeneralNominalSupport.Tracked roles,
      B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after ∧
      EqualityComplete after.current ∧
      (∀ model, Models after.current model ↔ Models before.current model) ∧
      (∀ focus : Occurrence roles, ∀ key,
        Joint registry after.current focus key ↔ Joint registry before.current focus key) ∧
      (∀ model, Models before.current model → ∀ focus : Occurrence roles,
        ∀ payload : GeneralDictionaryReadback.Payload,
        GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model focus payload ↔
        GeneralDictionaryRecursiveEvidence.Evidence registry before.current.context model focus payload) := by
  obtain ⟨after,path,models,_,_,certificate,done⟩ := complete_sources registry root before
  exact ⟨after,path,done,models,
    fun focus key => certificate.joint registry focus key,
    fun model valid focus payload => certificate.evidence registry model valid focus payload⟩

/-- The SAME observationally equivalent completed endpoint remains reachable
from source formation. This does not assert any non-equality rule is disabled. -/
theorem complete_sourceformed_observations (registry : Registry) (root : Occurrence roles)
    (before : GeneralNominalSupport.Tracked roles)
    (formed : GeneralNominalSupportSteps.SourceFormed registry root before) :
    ∃ after : GeneralNominalSupport.Tracked roles,
      GeneralNominalSupportSteps.SourceFormed registry root after ∧
      B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after ∧
      EqualityComplete after.current ∧
      (∀ model, Models after.current model ↔ Models before.current model) ∧
      (∀ focus : Occurrence roles, ∀ key,
        Joint registry after.current focus key ↔ Joint registry before.current focus key) ∧
      (∀ model, Models before.current model → ∀ focus : Occurrence roles,
        ∀ payload : GeneralDictionaryReadback.Payload,
        GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model focus payload ↔
        GeneralDictionaryRecursiveEvidence.Evidence registry before.current.context model focus payload) := by
  obtain ⟨after,path,done,models,joint,evidence⟩ := complete_observations registry root before
  refine ⟨after,?_,path,done,models,joint,evidence⟩
  clear done models joint evidence
  induction path with
  | refl => exact formed
  | tail _ step ih => exact .update ih step
end Yulang.GeneralDictionaryFiniteEqualityObservations
