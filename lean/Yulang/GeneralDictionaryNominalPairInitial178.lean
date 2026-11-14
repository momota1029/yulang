import Yulang.GeneralDictionaryNominalPairSourceSupport178
import Yulang.GeneralDictionaryCenteredNovel177

/-! Initial singleton nominal candidates need only joint centered consistency:
source head support, raw class jointness and installation closure are derived. -/
namespace Yulang.GeneralDictionaryNominalPairInitial178
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176 GeneralNominalRecursiveCandidates
open GeneralDictionaryNominalPair178

abbrev packet (registry : Registry) (context : Context) (input : Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context declaration) : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite input.occurrence,declaration,checked,[(shape.lower,shape.upper)]⟩
abbrev plan (registry : Registry) (context : Context) (input : Site roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context declaration) : Plan roles :=
  ⟨packet registry context input declaration checked shape,input,rfl⟩

variable {roles : Roles.RoleDecls}
variable (registry : Registry) (context : Context) (input : Site roles)
  (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
  (shape : Shape context declaration)
  (singleton : registry.declarations = [declaration])
  (candidate : Candidate registry (initialAt context input) input.occurrence declaration.id
    (packet registry context input declaration checked shape).children (plan registry context input declaration checked shape))

include candidate

include singleton in
 theorem value_guard : GeneralNominalValueSupport.PacketGuard (initialAt context input).erased
    (packet registry context input declaration checked shape) [] :=
  GeneralDictionaryNominalPairSourceSupport178.value_guard context input.occurrence declaration shape registry singleton
    checked _ rfl candidate.located

 theorem raw_joint : GeneralNominalJointCandidates.Joint registry (initialAt context input).erased.current
    input.occurrence declaration.id := by
  obtain ⟨model,branch⟩ := candidate.branch
  exact GeneralNominalJointCandidates.initial_joint registry context input.occurrence declaration
    candidate.visible checked candidate.role [(shape.lower,shape.upper)] candidate.located candidate.prepared model branch

 theorem raw_installable
    (selected : GeneralNominalCenteredBoundary.Local registry (initialAt context input) input.occurrence
      (.selected declaration.id (packet registry context input declaration checked shape).children)) :
    GeneralNominalFeedbackSteps.Installable registry (initialAt context input).erased.current
      (packet registry context input declaration checked shape) := by
  have old : GeneralNominalFeedbackK2.Local registry (initialAt context input).erased.current input.occurrence
      (.selected declaration.id (packet registry context input declaration checked shape).children) := by
    cases selected with
    | selected safe unique =>
      exact .selected ⟨safe.1,fun h => safe.2.1 (.inl h),fun h => safe.2.2.1 (.inl h),
        fun h => safe.2.2.2 (.inl h)⟩ unique
  refine ⟨?_,old,?_⟩
  · refine ⟨rfl,rfl,by simp [initialAt,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial],
      candidate.visible,candidate.role,candidate.located,candidate.prepared,
      GeneralNominalFeedbackK2.selected_legacy old,?_,?_,?_,
      raw_joint registry context input declaration checked shape candidate⟩
    · intro prior member; cases member
    · intro other member _
      have same : other = GeneralNominalDemandMerging.pointSite input.occurrence := List.mem_singleton.mp member
      subst other; exact .refl _
    · obtain ⟨model,branch⟩ := candidate.branch
      have source := (branch_interval_sound registry context input.occurrence declaration checked
        [(shape.lower,shape.upper)] model branch).1
      exact ⟨model,(GeneralNominalSaturationState.initial_models ..).mpr source,branch⟩
  · intro other member _
    have same : other = GeneralNominalDemandMerging.pointSite input.occurrence := List.mem_singleton.mp member
    subst other; exact .refl _

include singleton in
/-- Only the common centered model remains as a semantic premise. No raw
Installable, support, historical packet or source point-interval premise occurs. -/
 theorem installable_of_joint
    (selected : GeneralNominalCenteredBoundary.Local registry (initialAt context input) input.occurrence
      (.selected declaration.id (packet registry context input declaration checked shape).children))
    (joint : ∃ model, Models (initialAt context input) model ∧
      (plan registry context input declaration checked shape).Holds model) :
    GeneralNominalCenteredBoundary.Installable registry (initialAt context input)
      (plan registry context input declaration checked shape) :=
  ⟨raw_installable registry context input declaration checked shape candidate selected,[],
    (GeneralDictionaryCenteredGuard177.candidate_guard_iff candidate selected []).mpr
      ⟨value_guard registry context input declaration checked shape singleton candidate,joint⟩⟩

include singleton in
 theorem stable_instance_of_joint
    (selected : GeneralNominalCenteredBoundary.Local registry (initialAt context input) input.occurrence
      (.selected declaration.id (packet registry context input declaration checked shape).children))
    (joint : ∃ model, Models (initialAt context input) model ∧
      (plan registry context input declaration checked shape).Holds model)
    (stable : Stable registry (initialAt context input) input.occurrence)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models (initialAt context input) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry context model input.occurrence declaration.id
      (packet registry context input declaration checked shape).children :=
  GeneralDictionaryCenteredNovel177.committed_or_installable_instance candidate stable
    (.inr (installable_of_joint registry context input declaration checked shape singleton candidate selected joint)) model valid
end Yulang.GeneralDictionaryNominalPairInitial178
