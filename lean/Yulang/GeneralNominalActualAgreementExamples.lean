import Yulang.GeneralNominalActualAgreedBoundary
import Yulang.GeneralNominalActualInspectionExamples

/-! A real actual-inspection installation satisfies both local policies. -/
namespace Yulang.GeneralNominalActualAgreementExamples
open GeneralNominalActualAgreedLocal
open GeneralNominalActualInspectionExamples
open GeneralNominalSharedExamples
open GeneralNominalExamples (registry displayRoot)

theorem display_installable : Installable registry (start false) (packet false) :=
  ⟨GeneralDictionarySharedDisplayInstallation.installable,[],display_guard⟩

theorem display_selected (defer : Bool) :
    Local defer ProvenanceGap registry (start false) displayRoot
      (.selected (packet false).declaration.id (packet false).children) :=
  initial_installable_selected display_installable

end Yulang.GeneralNominalActualAgreementExamples
