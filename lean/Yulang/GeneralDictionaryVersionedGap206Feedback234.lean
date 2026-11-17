import Yulang.GeneralDictionaryVersionedGap206Install233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedGap206Feedback234
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 GeneralDictionaryVersionedGap206Install233
open GeneralNominalVersionedJournal232 GeneralNominalVersionedKernel232
open CommonNominalFullCarrier

theorem installed_equal : Equal installed 0 1 := by
  intro assignment valid
  have cert := GeneralNominalVersionedInstalledEvidence233.certificate rfl children_empty valid
  have witness := (GeneralNominalVersionedReplayEffects232.replay_output_witness_iff plan assignment ⟨0,0⟩).mp
    (cert.outputs ⟨0,0⟩ (List.mem_singleton_self _))
  obtain ⟨body,supplied,_,holds⟩ := witness
  have found := (GeneralDictionaryAssociatedProvenance.lookup_exact roles declaration declaration_checked.identified.2.2.1 0 body).mpr supplied
  have same : body = .default 0 0 (.var 0) := Option.some.inj found.symm
  subst body
  exact (GeneralNominalCenteredHeadMatEffects.positional_default plan assignment (0 : Fin 1)).mp holds

theorem raw_counter : GeneralNominalState.Models installed.core.erased.current.context.state counter := by
  exact (GeneralNominalVersionedInstallation231.replay_private_models plan counter).mpr
    (head_models counter GeneralDictionaryDefaultGap206Source.counter_model).1

theorem not_raw_equal : ¬ GeneralNominalFeedbackSteps.RawEqual installed.core.erased.current 0 1 := by
  intro equal
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.scalar .int) (equal counter raw_counter)

noncomputable def feedback := GeneralNominalVersionedAdministrative232.equate installed 0 1

theorem feedback_step : Step registry root installed feedback := by
  refine ⟨root,.root,.administrative (.equate root 0 1 ?_ ?_ installed_equal not_raw_equal)⟩ <;>
    simp only [GeneralNominalState.sources,List.mem_append]
  · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(0 : Fin 3),rfl⟩)))
  · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(1 : Fin 3),rfl⟩)))

theorem not_stable : ¬ Stable registry installed root := by
  intro stable
  obtain ⟨focus,generated,action⟩ := feedback_step
  exact stable focus generated feedback action

end Yulang.GeneralDictionaryVersionedGap206Feedback234
