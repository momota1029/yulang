import Yulang.GeneralDictionaryVersionedSecondInstall233
import Yulang.GeneralDictionaryVersionedVariant233
import Yulang.GeneralDictionaryVersionedInitialStep233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedSecondStep233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedPointStage233
open GeneralDictionaryVersionedSecondInstall233
open GeneralNominalVersionedJournal232
open CommonNominalFullCarrier

 theorem cache : GeneralNominalVersionedKernelCache232.Valid point :=
  GeneralNominalVersionedKernelCache232.step_cache GeneralDictionaryVersionedPointStage233.step
    (GeneralNominalVersionedKernelCache232.step_cache GeneralDictionaryVersionedInitialStep233.step
      (GeneralDictionaryDefaultCache208.initial_valid context root))

theorem installable : GeneralNominalVersionedKernel232.Installable registry point effect := by
  refine ⟨rfl,rfl,GeneralDictionaryVersionedPointSafety233.safe,cache,?_,
    GeneralDictionaryVersionedPointSafety233.choice,GeneralDictionaryVersionedPointSafety233.positions,
    GeneralDictionaryVersionedPointSafety233.alternatives,
    GeneralDictionaryVersionedBothModel233.extended,installation_models⟩
  · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
    rw [GeneralDictionaryVersionedPoint233.emitted_schema]

noncomputable abbrev counter := GeneralDictionaryVersionedVariant233.variant GeneralDictionaryOptionalOutput229.value

theorem counter_model : Models point counter := GeneralDictionaryVersionedVariant233.point_model _

theorem no_packet : ¬ GeneralNominalVersionedPlans231.Holds plan counter := by
  intro valid
  have merges := valid.2.1.1.2.1
  rw [GeneralDictionaryVersionedPoint233.bindings_exact] at merges
  change PresenceNormalForm.All CommonNominalFullCarrier.model counter
    ((GeneralNominalAllocation.equations (GeneralDictionaryVersionedNames231.freshName 0)
      (.union (.var 2) (.var 2)) ++ _) ++ _) at merges
  have lower := (PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merges).1 |>.1
  have equal := (GeneralNominalCaptureMerges.equations_exact ..).mp lower
  change Equivalent (counter (GeneralDictionaryVersionedNames231.freshName 0)).1
    (.union (counter 2).1 (counter 2).1) at equal
  have freshValue : (counter (GeneralDictionaryVersionedNames231.freshName 0)).1 = GeneralDictionaryOptionalOutput229.value :=
    GeneralDictionaryVersionedVariant233.next_value _ 0
  have two : (counter 2).1 = .emptyRecord :=
    congrArg Prod.fst (GeneralDictionaryVersionedVariant233.old_value
      GeneralDictionaryOptionalOutput229.value 2 (by simp [GeneralDictionaryVersionedInitialModel233.pool]))
  have bad : Equivalent GeneralDictionaryOptionalOutput229.value (.union .emptyRecord .emptyRecord) := by
    rw [← freshValue,← two]
    exact equal
  exact GeneralDictionaryOptionalOutput229.not_width
    ⟨subtype_trans bad.1 ((common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩),
      subtype_trans ((common_union_is_join _ _ _).mp (subtype_refl _) |>.1) bad.2⟩

theorem not_committed : ¬ GeneralNominalVersionedInstallStep232.Committed point plan :=
  fun committed => no_packet (committed.1 counter counter_model).1

theorem step : GeneralNominalVersionedKernel232.Step registry root point installed :=
  ⟨root,.root,.install effect installable not_committed⟩

theorem path : B4Target.Steps (GeneralNominalVersionedKernel232.Step registry root)
    GeneralDictionaryVersionedInitialFrame233.before installed :=
  .tail (.tail (.tail .refl GeneralDictionaryVersionedInitialStep233.step)
    GeneralDictionaryVersionedPointStage233.step) step

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles)
    sourceRegistry root installed :=
  ⟨GeneralDictionaryVersionedInitialFrame233.before,
    ⟨start,GeneralDictionaryOptionalInitial229.initial,rfl⟩,path⟩

/-- A genuinely new-boundary-only source trace, with both historical versions. -/
theorem reachable_nonempty :
    B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) sourceRegistry root installed ∧
    ∃ model, Models installed model ∧
      GeneralNominalVersionedEvidence231.Evidence registry installed.core model root (.node declaration.id []) :=
  ⟨reachable,GeneralDictionaryVersionedBothModel233.extended,installed_model,evidence installed_model⟩

end Yulang.GeneralDictionaryVersionedSecondStep233
