import Yulang.GeneralDictionaryVersionLoopSecondInstall238
import Yulang.GeneralDictionaryVersionLoopSecondNovel238
/-! Two real installations, separated by refresh and retarget, from the same
original source. This finite four-step regression is not an infinite family
and does not refute global termination. -/
namespace Yulang.GeneralDictionaryVersionLoopSecondStep238
open GeneralDictionaryVersionLoopSource237
open GeneralDictionaryVersionLoopSecondFrame238
open GeneralDictionaryVersionLoopSecondInstall238
open GeneralDictionaryVersionLoopRetarget237 (retargeted)

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root retargeted installed :=
 ⟨root,.root,.install effect installable GeneralDictionaryVersionLoopSecondNovel238.novel⟩

theorem path : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) initial installed :=
 .tail GeneralDictionaryVersionLoopPrefix238.path step

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
 sourceRegistry root installed := ⟨initial,GeneralDictionaryVersionLoopInitial238.initial_source,path⟩

theorem inhabited : ∃ assignment, GeneralNominalVersionedJournal232.Models installed assignment :=
 ⟨model,installed_model⟩

theorem recorded : installed.plans =
 [GeneralDictionaryVersionLoopSecondPacket238.plan,GeneralDictionaryVersionLoopPacket237.plan] := rfl
end Yulang.GeneralDictionaryVersionLoopSecondStep238
