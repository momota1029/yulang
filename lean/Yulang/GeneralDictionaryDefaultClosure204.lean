import Yulang.GeneralDictionaryDefaultBoundary204
import Yulang.GeneralDictionaryAllocProductionSplit202

namespace Yulang.GeneralDictionaryDefaultClosure204
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralDictionaryDefaultBoundary204
open GeneralDictionaryDefaultEvidence204
open GeneralNominalCenteredHeadMatStepJournal (State)

/-- Remaining same-model source-certificate bridge. There is no recursive child
Evidence premise here. It is exposed as an obligation, not asserted as a fact. -/
def SelectedCertificates (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state → ∀ model,
    (boundary roles).Models state model → ∀ focus key children,
    (focus = root ∨ (boundary roles).Generated value state root focus) →
    (boundary roles).Stable value state focus →
    (∀ child, child ∈ children → (boundary roles).Stable value state child) →
    B4TargetV7.Local (boundary roles) value state focus (.selected key children) →
    Instance (GeneralNominalCenteredHeadAllocEncoding.registry value) state.core model focus key children

theorem evidenceNode (source : SelectedCertificates roles) :
    B4SkeletonV7.EvidenceNode (boundary roles) := by
  intro value checked state root reachable model valid focus key children dictionaries reached stable childStable selected given
  exact evidence_node (source value checked state root reachable model valid focus key children reached stable childStable selected) given

/-- The historical/fresh split is unaffected by evidence replacement. -/
theorem generatedChildren (fresh : GeneralDictionaryAllocProductionSplit202.FreshCompletion roles) :
    B4SkeletonV7.GeneratedChildren (boundary roles) :=
  generated_iff.mpr (GeneralDictionaryAllocProductionSplit202.generatedChildren fresh)

/-- Two named missing bridges remain: all-model source certificates and fresh
installation. No global HeadBaseline or model-existence premise is introduced. -/
theorem composition (source : SelectedCertificates roles)
    (fresh : GeneralDictionaryAllocProductionSplit202.FreshCompletion roles) :
    B4TargetV7.Statement (boundary roles) (GeneralNominalCenteredHeadAllocV7Executor.executor roles) :=
  GeneralDictionaryDefaultBoundary204.composition (evidenceNode source) (generatedChildren fresh)

/-- On explicit-covered source instances, the new judgment implies the complete
legacy judgment. This lifts guard preservation through the whole dictionary. -/
theorem evidence_legacy_of_explicit
    (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (model : GeneralNominalCommonBridge.Assignment)
    (explicit : ∀ root key children plan,
      Certificate registry state model root key children plan →
      GeneralNominalMaterialization.RootDefined plan.packet.declaration root)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (given : Evidence registry state model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.erased.current.context model root payload := by
  obtain ⟨tree,readback,derived⟩ := given
  refine ⟨tree,readback,GeneralSourceDictionaries.evidence_mono _ _ ?_ derived⟩
  intro occurrence key children source
  obtain ⟨plan,certificate⟩ := source
  exact certificate_legacy certificate (explicit occurrence key children plan certificate)

end Yulang.GeneralDictionaryDefaultClosure204
