import Yulang.GeneralDictionaryPointReobserve240
import Yulang.GeneralNominalPointSourceBoundary240
import Yulang.GeneralDictionaryMixedClosedRegression234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPointOptional240
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedInitialFrame233
open GeneralDictionaryVersionedPointStage233
open GeneralNominalPointKernel240

theorem install_step : Step registry root before installed :=
 ⟨root,.root,.install effect
 (GeneralNominalVersionedMixedKernel234.of_old_installable GeneralDictionaryVersionedInitialStep233.installable)
 GeneralDictionaryVersionedInitialStep233.not_committed⟩

theorem reobserve_step : Step registry root installed point :=
 GeneralDictionaryPointReobserve240.five rfl allocated reserved ordinary current_loose registry root

theorem second_install_step : Step registry root point GeneralDictionaryVersionedSecondInstall233.installed :=
 ⟨root,.root,.install GeneralDictionaryVersionedSecondInstall233.effect
 (GeneralNominalVersionedMixedKernel234.of_old_installable GeneralDictionaryVersionedSecondStep233.installable)
 GeneralDictionaryVersionedSecondStep233.not_committed⟩

theorem refresh_step : Step registry root GeneralDictionaryVersionedSecondInstall233.installed GeneralDictionaryMixedClosedStep234.next :=
 ⟨root,.root,.refresh root GeneralDictionaryMixedClosedSnapshot234.extendedContext
 GeneralDictionaryMixedClosedStep234.mixedCertificate GeneralDictionaryVersionedUpperBase233.hi
 GeneralDictionaryVersionedUpperRefresh233.upper_supported GeneralDictionaryVersionedUpperRefresh233.upper_unknown
 ⟨(7 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩⟩

theorem reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root GeneralDictionaryMixedClosedStep234.next :=
 ⟨before,⟨start,GeneralDictionaryOptionalInitial229.initial,rfl⟩,
 .tail (.tail (.tail (.tail .refl install_step) reobserve_step) second_install_step) refresh_step⟩
end Yulang.GeneralDictionaryPointOptional240
