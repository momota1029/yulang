import Yulang.GeneralDictionaryCenteredScalar177
import Yulang.GeneralNominalCenteredAdministrativeProduction

/-! A current committed packet needs no new installation. The remaining
producer below is required only for novel current candidates, never for all
recorded packets. Its existence is deliberately not asserted. -/
namespace Yulang.GeneralDictionaryCenteredNovel177
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps GeneralDictionaryCenteredCandidate176
open GeneralNominalCenteredBoundary (Local Installable)
open GeneralDictionaryRecursiveEvidence (Instance Evidence)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalCenteredGroundBoundary (groundBoundary)

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {root focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}

/-- Stability closes the novel branch; the old branch does not use stability. -/
theorem committed_or_installable_instance {plan : Plan roles}
    (candidate : Candidate registry state focus key children plan)
    (stable : Stable registry state focus)
    (ready : GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet ∨
      Installable registry state plan)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    Instance registry state.erased.current.context model focus key children := by
  apply GeneralDictionaryCenteredScalar177.committed_candidate_instance candidate _ model valid
  rcases ready with committed | enabled
  · exact committed
  · exact GeneralDictionaryCenteredReady176.stable_committed stable plan candidate.occurrence_eq enabled

/-- No historical journal membership or stored-to-current context transport. -/
theorem committed_or_installable_evidence {plan : Plan roles}
    (candidate : Candidate registry state focus key children plan)
    (stable : Stable registry state focus)
    (ready : GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet ∨
      Installable registry state plan)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List Payload)
    (given : All₂ (Evidence registry state.erased.current.context model) children dictionaries) :
    Evidence registry state.erased.current.context model focus (.node key dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry state.erased.current.context model
    focus key children dictionaries (committed_or_installable_instance candidate stable ready model valid) given

/-- A sufficient open producer, only at novel selected current candidates.
It may choose a different current candidate than the initial inspection did. -/
def NovelInstallable (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (groundBoundary roles).Checked registry → ∀ state root,
  B4TargetV5.Reachable (groundBoundary roles) registry root state →
  (∃ model, Models state model) → ∀ focus key children,
  (focus = root ∨ (groundBoundary roles).Generated registry state root focus) →
  Stable registry state focus → Local registry state focus (.selected key children) →
  ∀ plan : Plan roles, Candidate registry state focus key children plan →
  ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet →
  ∃ other : Plan roles, other.packet.site.occurrence = focus ∧ Installable registry state other

theorem evidenceNode_of_novelInstallable (producer : NovelInstallable roles) :
    B4SkeletonV5.EvidenceNode (groundBoundary roles) := by
  classical
  intro registry checked state root reachable model valid focus key children dictionaries
    reached stable _ safe unique given
  have selected : Local registry state focus (.selected key children) :=
    (GeneralNominalCenteredBoundary.local_correspondence registry state focus _).mp
      (B4TargetV3.Local.selected safe unique)
  obtain ⟨plan,candidate⟩ := reachable_candidate reachable reached selected
  by_cases committed : GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet
  · exact committed_or_installable_evidence candidate stable (.inl committed) model valid dictionaries given
  · obtain ⟨other,same,enabled⟩ := producer registry checked state root reachable ⟨model,valid⟩
      focus key children reached stable selected plan candidate committed
    exact GeneralDictionaryCenteredReady176.selected_evidence stable selected other same enabled model valid dictionaries given

theorem novelInstallable_of_modeledSelectedInstallable
    (producer : GeneralDictionaryCenteredReady176.ModeledSelectedInstallable roles) :
    NovelInstallable roles := by
  intro registry checked state root reachable modeled focus key children reached stable selected _ _ _
  exact producer registry checked state root reachable modeled focus key children reached stable selected

/-- The same sufficient residual also supplies the administrative boundary's
EvidenceNode; no confluence or child-production field is claimed. -/
theorem administrative_evidenceNode_of_novelInstallable (producer : NovelInstallable roles) :
    B4SkeletonV5.EvidenceNode (GeneralNominalCenteredAdministrativeLocal.boundary roles) :=
  GeneralNominalCenteredAdministrativeProduction.evidenceNode_of_ground
    (evidenceNode_of_novelInstallable producer)

end Yulang.GeneralDictionaryCenteredNovel177
