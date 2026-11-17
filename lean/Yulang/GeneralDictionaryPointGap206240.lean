import Yulang.GeneralNominalPointSourceBoundary240
import Yulang.GeneralDictionaryMixedGap206Stable234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPointGap206240
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233
open GeneralDictionaryVersionedGap206Install233
open GeneralDictionaryVersionedGap206Feedback234
open GeneralDictionaryMixedGap206Refresh234
open GeneralNominalPointKernel240

theorem install_step : Step registry root current installed :=
 ⟨root,.root,.install effect (GeneralNominalVersionedMixedKernel234.of_old_installable installable) not_committed⟩

theorem equate_step : Step registry root installed feedback := by
 refine ⟨root,.root,.administrative (.equate root 0 1 ?_ ?_ installed_equal not_raw_equal)⟩ <;>
   simp only [GeneralNominalState.sources,List.mem_append]
 · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(0 : Fin 3),rfl⟩)))
 · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(1 : Fin 3),rfl⟩)))

theorem refresh_step : Step registry root feedback refreshed := by
 refine ⟨root,.root,.refresh root GeneralDictionaryMixedGap206Snapshot234.context certificate 0 ?_
 GeneralDictionaryMixedGap206Snapshot234.zero_unknown GeneralDictionaryMixedGap206Snapshot234.zero_known⟩
 simp only [GeneralNominalState.sources,List.mem_append]
 exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(0 : Fin 3),rfl⟩)))

theorem reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root refreshed :=
 ⟨current,initial,.tail (.tail (.tail .refl install_step) equate_step) refresh_step⟩
end Yulang.GeneralDictionaryPointGap206240
