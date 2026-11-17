import Yulang.GeneralDictionaryCompoundRefresh239
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundRefreshStep239
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238 GeneralDictionaryCompoundPoint238
open GeneralDictionaryCompoundBase239 GeneralDictionaryCompoundSnapshot239
open GeneralDictionaryCompoundRefresh239

theorem lower_unknown : ¬ GeneralNominalState.Known point.core.erased.current.context.state lo := by
  rw [context_exact]
  rintro ⟨slot,same,_⟩
  have small := slot.isLt
  change slot.val < 5 at small
  change slot.val = lo at same
  have high : 4 < lo := GeneralNominalIdentities.source_above_seed snapshot.seed _
  omega

theorem lower_known : GeneralNominalState.Known extendedSnapshot lo :=
  ⟨(5 : Fin 7),rfl,Or.inl (by intro h; cases h)⟩

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root point refreshed :=
  ⟨root,.root,.refresh root extendedContext certificate lo (supported 5 (by decide)) lower_unknown lower_known⟩

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root refreshed := by
  obtain ⟨first,initial,path⟩ := GeneralDictionaryCompoundPoint238.reachable
  exact ⟨first,initial,.tail path step⟩

theorem inhabited : GeneralNominalVersionedJournal232.Models refreshed GeneralDictionaryCompoundVersionedModel238.extended :=
  (GeneralDictionaryCompoundRefresh239.models_iff _).mpr GeneralDictionaryCompoundPoint238.inhabited

theorem old_not_stable : ¬ GeneralNominalVersionedMixedKernel234.Stable registry point root := by
  intro stable
  obtain ⟨focus,generated,action⟩ := step
  exact stable focus generated refreshed action

end Yulang.GeneralDictionaryCompoundRefreshStep239
