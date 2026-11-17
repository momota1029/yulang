import Yulang.GeneralDictionaryVersionLoopInstall238
import Yulang.GeneralDictionaryVersionLoopNext237
/-! Actual original-source finite prefix only. Three guarded mixed steps reach
a strictly changed repeated-capture report. No second installation, iteration
family, infinite path, or target refutation is asserted. -/
namespace Yulang.GeneralDictionaryVersionLoopPrefix238
open GeneralDictionaryVersionLoopSource237 GeneralDictionaryVersionLoopFrame237
open GeneralDictionaryVersionLoopInitial238 GeneralDictionaryVersionLoopRetarget237

theorem path : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) initial retargeted :=
 .tail (.tail (.tail .refl GeneralDictionaryVersionLoopInstall238.step) refresh_step) retarget_step

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
 sourceRegistry root retargeted := ⟨initial,initial_source,path⟩

theorem inhabited : ∃ assignment, GeneralNominalVersionedJournal232.Models retargeted assignment :=
 ⟨model,retargeted_model⟩
end Yulang.GeneralDictionaryVersionLoopPrefix238
