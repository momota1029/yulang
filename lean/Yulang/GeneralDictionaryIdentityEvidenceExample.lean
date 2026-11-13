import Yulang.GeneralDictionarySharedSourceRetention
import Yulang.GeneralNominalIdentityExample

/-! Nonvacuity for the current-context identity bridge: an actual source-formed
Shared installation, a concrete current model, and its semantic dictionary. -/
namespace Yulang.GeneralDictionaryIdentityEvidenceExample
open GeneralNominalIdentityExample GeneralNominalSaturationState

theorem formed : GeneralNominalSharedSteps.SourceFormed registry root finish :=
  .update (.initial context source) actual_step

theorem current_model : Models finish.current (model .int) :=
  (GeneralNominalSharedSteps.install_models (state := start) (packet := packet)
    (support := []) rfl (model .int)).mpr ⟨(initial_models ..).mpr (source_models .int),branch⟩

theorem current_evidence (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current m) :
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context m root
      (.node declaration.id []) :=
  GeneralDictionarySharedSourceRetention.identity_current_evidence formed packet
    List.mem_cons_self shape 0 point m valid

theorem nonvacuous_current_evidence :
    GeneralNominalSharedSteps.SourceFormed registry root finish ∧
    ∃ m, Models finish.current m ∧
      GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context m root
        (.node declaration.id []) :=
  ⟨formed,model .int,current_model,current_evidence _ current_model⟩
end Yulang.GeneralDictionaryIdentityEvidenceExample
