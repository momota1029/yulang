import Yulang.GeneralDictionaryAgreedCompletion175
import Yulang.GeneralDictionaryAgreedFlexibleTrace175
import Yulang.GeneralDictionaryAgreedCertifiedEvidence175

/-! Whole dictionaries at halted endpoints of the larger nominal-only-view
refresh subrelation. A finite source trace produces the current packet invariant;
full actual closure supplies stability, never just closure of the subrelation.
Descriptor-changing revisions and arbitrary actual executor traces remain open. -/
namespace Yulang.GeneralDictionaryAgreedFlexibleCompletion175
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralNominalActualAgreedLocal
open GeneralNominalActualAgreedBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryAgreedFlexibleTrace175
variable {roles : Roles.RoleDecls} {defer : Bool} {gap : GapPredicate roles}
variable {registry : Registry} {state : Tracked roles} {root : Occurrence roles}

theorem halted_dictionary_evidence
    (checked : (boundary defer gap).Checked registry)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
    (model : Assignment) (valid : Models state.current model) (dictionary : Payload)
    (derived : B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary := by
  have formed := (trace_formed_recorded (.initial context source) (initial_recorded context) path).1
  have reachable : B4TargetV5.Reachable (boundary defer gap) registry root state :=
    GeneralNominalActualAgreedBoundary.reachable_iff_sourceFormed.mpr formed
  obtain ⟨rootStable,generatedStable⟩ := GeneralNominalActualAgreedBoundary.closure registry checked state root reachable halted
  exact GeneralDictionaryAgreedCompletion175.dictionary_evidence
    (initial_trace_recorded context source path) policy rootStable generatedStable model valid
    dictionary root (Or.inl rfl) derived

theorem halted_pending_dictionary_evidence
    (checked : (boundary true gap).Checked registry)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (model : Assignment) (valid : Models state.current model) (dictionary : Payload)
    (derived : B4TargetV3.Classify (boundary true gap).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  halted_dictionary_evidence checked context source path halted (fun _ => Or.inl rfl) model valid dictionary derived

/-- The same finite role table diagnostic can be consumed after flexible traces;
its certificate is not a termination proof for the saturation relation. -/
theorem halted_completed_evidence
    (checked : (boundary defer gap).Checked registry)
    (passed : GeneralDictionaryAgreedTable175.certifyTable registry = true)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
    (dictionary : Payload)
    (completed : B4TargetV3.Completed
      (GeneralDictionaryAgreedCertifiedEvidence175.diagnostic defer gap registry state root) (.selected dictionary))
    (model : Assignment) (valid : Models state.current model) :
    Evidence registry state.current.context model root dictionary := by
  have formed := (trace_formed_recorded (.initial context source) (initial_recorded context) path).1
  have reachable : B4TargetV5.Reachable (boundary defer gap) registry root state :=
    GeneralNominalActualAgreedBoundary.reachable_iff_sourceFormed.mpr formed
  exact halted_dictionary_evidence checked context source path halted policy model valid dictionary
    ((GeneralDictionaryAgreedCertifiedEvidence175.completed_iff checked passed reachable _).mp completed)

end Yulang.GeneralDictionaryAgreedFlexibleCompletion175
