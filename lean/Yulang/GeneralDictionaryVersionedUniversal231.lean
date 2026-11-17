import Yulang.GeneralDictionaryVersionedEvidence231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedUniversal231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Snapshot GeneralDictionaryUpper230Step
open GeneralDictionaryUpper230Selected
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

variable {m : Assignment}
variable (valid : GeneralNominalCenteredHeadMatStepJournal.Models after m)
include valid

theorem old_packet : GeneralNominalCenteredHeadMatStepPackets.Holds plan m := by
  have stageValid := (models m).mp valid
  have installedValid := (GeneralDictionaryOptionalStage229.stage_models m).mp stageValid
  exact (GeneralNominalCenteredHeadMatStepJournal.install_models (state := start) (effect := effect) rfl).mp installedValid |>.2.1

theorem observed_bounds (index : Nat) (small : index < 2) :
    (∃ value, Observes m (.nominal (.source 0) 0 index) value) ∧
      ∀ value, Observes m (.nominal (.source 0) 0 index) value →
        GeneralNominalCaptureMerges.Fits m (2,2) value := by
  apply nominal_argument_bounds extendedSnapshot m valid.1 (0 : Fin 6) pointDesc rfl index (2,2)
  rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl <;> rfl

theorem observed_value (index : Nat) (small : index < 2)
    (seen : Observes m (.nominal (.source 0) 0 index) value) : Equivalent value (m 2).1 :=
  let fit := (observed_bounds valid index small).2 value seen
  ⟨fit.2,fit.1⟩

theorem projection : ProjectionModels extendedSnapshot (GeneralNominalPacketSupport.report currentPacket) m := by
  change ProjectionModels extendedSnapshot
    (GeneralNominalRecursiveCandidates.report extendedContext declaration [(0,0)]) m
  rw [GeneralDictionaryUpper230Current.report_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact observed_bounds valid 0 (by decide)
    · cases List.mem_singleton.mp member
      exact observed_bounds valid 1 (by decide)
  · intro test member; cases member
  · intro first one last two _ origin located value seen
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj located
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals first
    | exact (observed_bounds valid 0 (by decide)).2 value seen
    | exact (observed_bounds valid 1 (by decide)).2 value seen
  · intro first one last two _ a b firstOrigin lastOrigin x y seenX seenY
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj firstOrigin
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals cases Option.some.inj lastOrigin
    all_goals
      have ex : Equivalent x (m 2).1 := by first
        | exact observed_value valid 0 (by decide) seenX
        | exact observed_value valid 1 (by decide) seenX
      have ey : Equivalent y (m 2).1 := by first
        | exact observed_value valid 0 (by decide) seenY
        | exact observed_value valid 1 (by decide) seenY
      exact ⟨subtype_trans ex.1 ey.2,subtype_trans ey.1 ex.2⟩

theorem old_head : plan.SchemaHolds plan.headSchema m :=
  (GeneralNominalCenteredHeadMatStepPackets.head_equations (old_packet valid)).2.2

theorem head_holds : GeneralNominalVersionedPlans231.SchemaHolds currentPlan currentPlan.headSchema m := by
  have old := old_head valid
  rw [head_schema] at old
  rw [schema_equal,head_schema]
  constructor
  · exact old.1
  · intro entry member
    have entryHolds := old.2 entry member
    rcases List.mem_cons.mp member with rfl | member
    all_goals first | cases List.mem_singleton.mp member | skip
    all_goals
      simp only [ite_true] at entryHolds ⊢
      rw [GeneralDictionaryVersionedPacket231.binder_exact]
      simpa only [GeneralDictionaryOptionalInstall229.binder_exact] using entryHolds

theorem actual_fits : GeneralNominalCaptureMerges.Fits m (2,2) (m actual).1 := by
  have old := old_head valid
  rw [head_schema] at old
  have agrees := old.2 ⟨0,origin0,.actual⟩ (List.mem_cons_self ..)
  simp only [ite_true] at agrees
  rw [GeneralDictionaryOptionalInstall229.binder_exact] at agrees
  obtain ⟨⟨x,seen⟩,_,same⟩ := agrees
  have fit := (observed_bounds valid 0 (by decide)).2 x seen
  have equal := same x (m actual).1 seen (.source _)
  exact ⟨subtype_trans fit.1 equal.1,subtype_trans equal.2 fit.2⟩

theorem outputs : GeneralNominalVersionedPlans231.Outputs currentPlan m := by
  have old := (old_packet valid).2.2
  unfold GeneralNominalCenteredHeadMatStepPackets.Outputs at old
  rw [GeneralDictionaryOptionalInstall229.emitted_schema] at old
  unfold GeneralNominalVersionedPlans231.Outputs
  rw [GeneralDictionaryVersionedPacket231.emitted_schema]
  intro equation member
  cases List.mem_singleton.mp member
  exact old _ (List.mem_singleton_self _)

end Yulang.GeneralDictionaryVersionedUniversal231
