import Yulang.GeneralDictionaryMixedGap206Snapshot234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedGap206Refresh234
open GeneralDictionaryDefaultGap206Source (roles registry root plan model counter)
open GeneralDictionaryVersionedGap206Feedback234 (feedback)
open GeneralDictionaryMixedGap206Trusted234 (zero_int output_trusted)
open GeneralDictionaryMixedGap206Snapshot234
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedSupport233
open GeneralSourceState (equationAtoms)
open CommonNominalFullCarrier

theorem scalar_all (assignment) (valid : Models feedback assignment) (slot : Fin 3) :
    Equivalent (assignment slot.val).1 (.base .int) := by
  rcases show slot = 0 ∨ slot = 1 ∨ slot = 2 by omega with rfl | rfl | rfl
  · exact zero_int assignment (trusted_models output_trusted valid)
  · exact valid.1.2.1.1.2.1 (1 : Fin 3) (.base .int) rfl
  · exact valid.1.2.1.1.2.1 (2 : Fin 3) (.base .int) rfl

noncomputable def certificate : GeneralNominalVersionedMixedObservations233.Refresh feedback context where
  refines := refines
  interpretation := rfl
  support := support
  constraints := by
    intro assignment valid
    refine ⟨⟨?_,?_,?_⟩,valid.1.1.2.2⟩
    · apply (PresenceNormalForm.all_append ..).mpr
      constructor
      · exact valid.1.2.1.1.1
      · intro atom member
        simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact (scalar_all assignment valid 0).1
        · exact (scalar_all assignment valid 0).2
    · intro slot term found
      have same : term = (.base .int : Core.PresenceGeneration.TyTerm (Fin 3)) := Option.some.inj found.symm
      subst term
      exact scalar_all assignment valid slot
    · intro pair member; cases member
  cache := by
    intro observation recorded
    cases recorded with
    | scalar slot scalar found =>
      change Fin 3 at slot
      have same : GeneralNormalizedObservation.Head.scalar Inference.Base.int =
          (.scalar scalar : GeneralNormalizedObservation.Head view.shapes 3) := found
      cases same
      by_cases zero : slot = 0
      · subst slot
        exact ⟨[],[.output GeneralDictionaryVersionedGap206Install233.effect,.input plan],
          .source,output_trusted,fun assignment _ valid => zero_int assignment valid⟩
      · refine ⟨[],[],.source,.source,?_⟩
        intro assignment old _
        have casesSlot : slot = 1 ∨ slot = 2 := by omega
        rcases casesSlot with rfl | rfl
        · exact old.1.1.2.1 (1 : Fin 3) (.base .int) rfl
        · exact old.1.1.2.1 (2 : Fin 3) (.base .int) rfl
    | structural slot kind children found => cases found
    | nominal slot descriptor found => cases found

noncomputable def refreshed := GeneralNominalVersionedRefresh232.refresh feedback context

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root feedback refreshed := by
  refine ⟨root,.root,.refresh root context certificate 0 ?_ zero_unknown zero_known⟩
  simp only [GeneralNominalState.sources,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(0 : Fin 3),rfl⟩)))

theorem not_stable : ¬ GeneralNominalVersionedMixedKernel234.Stable registry feedback root := by
  intro stable
  obtain ⟨focus,generated,action⟩ := step
  exact stable focus generated refreshed action

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root refreshed := by
  obtain ⟨first,initial,path⟩ := GeneralDictionaryMixedGap206Trusted234.reachable
  exact ⟨first,initial,.tail path step⟩

theorem models_iff (assignment) : Models refreshed assignment ↔ Models feedback assignment :=
  GeneralNominalVersionedMixedObservations233.refresh_models certificate

theorem model_retained : Models refreshed model :=
  (models_iff model).mpr GeneralDictionaryVersionedGap206After234.model_retained

theorem counter_removed : ¬ Models refreshed counter :=
  fun valid => GeneralDictionaryVersionedGap206After234.counter_removed ((models_iff counter).mp valid)

end Yulang.GeneralDictionaryMixedGap206Refresh234
