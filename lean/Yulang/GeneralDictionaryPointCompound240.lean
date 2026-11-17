import Yulang.GeneralDictionaryPointReobserve240
import Yulang.GeneralNominalPointSourceBoundary240
import Yulang.GeneralDictionaryCompoundRefreshStep239
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPointCompound240
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundFrame238
open GeneralDictionaryCompoundPoint238
open GeneralNominalPointKernel240

theorem install_step : Step registry root before installed :=
 ⟨root,.root,.install effect GeneralDictionaryCompoundStep238.installable GeneralDictionaryCompoundStep238.not_committed⟩

theorem reobserve_step : Step registry root installed point :=
 GeneralDictionaryPointReobserve240.five rfl allocated reserved ordinary current_loose registry root

theorem installed_reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root installed :=
 ⟨before,⟨start,GeneralDictionaryCompoundSource238.initial,rfl⟩,.tail .refl install_step⟩

theorem point_reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root point := by
 obtain ⟨start,initial,path⟩ := installed_reachable
 exact ⟨start,initial,.tail path reobserve_step⟩

open GeneralDictionaryCompoundBase239 GeneralDictionaryCompoundSnapshot239
open GeneralDictionaryCompoundRefresh239 GeneralDictionaryCompoundRefreshStep239

theorem refresh_step : Step registry root point refreshed :=
 ⟨root,.root,.refresh root extendedContext certificate lo (supported 5 (by decide)) lower_unknown lower_known⟩

theorem refreshed_reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root refreshed := by
 obtain ⟨start,initial,path⟩ := point_reachable
 exact ⟨start,initial,.tail path refresh_step⟩

end Yulang.GeneralDictionaryPointCompound240
