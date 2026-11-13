import Yulang.GeneralDictionaryActualStable173
import Yulang.GeneralNominalActualPhaseBoundary

/-! I-28: dictionary composition on actual, ground and point-source boundaries.
SelectedPackets is a named UNPROVED local-to-installation residual. Ground
termination is supplied by Astra's actual-inspection theorem, not assumed.
No where-accessibility, executable resolver, completeness or principality is
claimed. Classification-to-evidence is conditional soundness only. -/
namespace Yulang.GeneralDictionaryActualV5173
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalActualBoundary
open GeneralDictionaryActualStable173
open B4TargetV5
variable {roles : Roles.RoleDecls}

theorem ground_reachable
    (reachable : Reachable (groundBoundary roles) registry root state) :
    Reachable (boundary roles) registry root state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact ⟨_,⟨context,source,rfl⟩,path⟩

theorem phase_reachable
    (reachable : Reachable (GeneralNominalActualPhaseBoundary.boundary roles) registry root state) :
    Reachable (boundary roles) registry root state := by
  obtain ⟨start,⟨context,source,point,rfl⟩,path⟩ := reachable
  exact ⟨_,⟨context,source,rfl⟩,path⟩

theorem ground_evidenceNode (packets : SelectedPackets roles) :
    B4SkeletonV5.EvidenceNode (groundBoundary roles) := by
  intro registry checked state root reachable
  exact GeneralDictionaryActualStable173.evidenceNode packets registry checked state root
    (ground_reachable reachable)

theorem ground_generatedChildren (packets : SelectedPackets roles) :
    B4SkeletonV5.GeneratedChildren (groundBoundary roles) := by
  intro registry checked state root focus key children reachable
  exact GeneralDictionaryActualStable173.generatedChildren packets registry checked state root focus key children
    (ground_reachable reachable)

theorem phase_evidenceNode (packets : SelectedPackets roles) :
    B4SkeletonV5.EvidenceNode (GeneralNominalActualPhaseBoundary.boundary roles) := by
  intro registry checked state root reachable
  exact GeneralDictionaryActualStable173.evidenceNode packets registry checked state root
    (phase_reachable reachable)

theorem phase_generatedChildren (packets : SelectedPackets roles) :
    B4SkeletonV5.GeneratedChildren (GeneralNominalActualPhaseBoundary.boundary roles) := by
  intro registry checked state root focus key children reachable
  exact GeneralDictionaryActualStable173.generatedChildren packets registry checked state root focus key children
    (phase_reachable reachable)

/-- The entire finite classification tree has evidence in each SAME final model;
no independent child model is substituted. SelectedPackets remains explicit. -/
theorem halted_classified_evidence (packets : SelectedPackets roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state)
    (halted : ∀ next, ¬ Step registry root state next)
    (model : GeneralNominalCommonBridge.Assignment) (valid : (boundary roles).Models state model)
    (dictionary : CommonRoleOutermostResolver.Dictionary)
    (classified : B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary)) :
    (boundary roles).Evidence registry state model root dictionary := by
  have closed := closure registry checked state root reachable halted
  exact B4SkeletonV5.dictionary_evidence (boundary roles)
    (GeneralDictionaryActualStable173.evidenceNode packets)
    (GeneralDictionaryActualStable173.generatedChildren packets)
    registry checked state root reachable closed.1 closed.2 model valid dictionary root (Or.inl rfl) classified

/-- Actual termination for the ground initial-source restriction plus conditional
soundness of every selected final classification. This is NOT a total classifier
or the five-part B4 Statement: SelectedPackets and selected classification remain. -/
theorem ground_terminal_evidence (packets : SelectedPackets roles)
    (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (groundBoundary roles) registry root state) :
    ∃ final, B4Target.Steps (Step registry root) state final ∧
      (∀ next, ¬ Step registry root final next) ∧
      ∀ model, (groundBoundary roles).Models final model →
        ∀ dictionary, B4TargetV3.Classify (groundBoundary roles).toSourceBoundary registry final root (.selected dictionary) →
          (groundBoundary roles).Evidence registry final model root dictionary := by
  obtain ⟨final,path,halted,stable,children,models⟩ := ground_terminal registry checked state root reachable
  refine ⟨final,path,halted,?_⟩
  intro model valid dictionary classified
  exact halted_classified_evidence packets registry checked final root
    (reachable_steps (boundary roles) (ground_reachable reachable) path) halted model valid dictionary classified

end Yulang.GeneralDictionaryActualV5173
