import Yulang.GeneralDictionaryVersionedProjection231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedPacket231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedNames231
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedFrame231 (binder)
open GeneralNominalCenters
open CommonNominalFullCarrier

theorem binder_exact : binder currentPlan 0 = actual := by
  rw [GeneralNominalVersionedFrame231.binder_eq]
  exact GeneralDictionaryUpper230Selected.binder_exact

theorem head_holds : SchemaHolds currentPlan currentPlan.headSchema extended := by
  rw [schema_equal,head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source 0⟩,?_⟩
    intro value seen
    cases seen
    refine ⟨[.inl .emptyRecord,.inl .emptyRecord],rfl,?_⟩
    rw [old_value 0 (by simp [GeneralDictionaryVersionedSupport231.pool])]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    all_goals first | cases List.mem_singleton.mp member | skip
    all_goals
      simp only [ite_true]
      refine ⟨?_,⟨_,.source _⟩,?_⟩
      · first | exact ⟨_,GeneralDictionaryVersionedProjection231.seen0⟩ | exact ⟨_,GeneralDictionaryVersionedProjection231.seen1⟩
      · intro x y seenX seenY
        cases seenY
        rw [binder_exact,actual_retained]
        first
        | exact GeneralDictionaryVersionedProjection231.observed_value 0 (by decide) seenX
        | exact GeneralDictionaryVersionedProjection231.observed_value 1 (by decide) seenX

theorem emitted_schema : emittedSchema currentPlan =
    ⟨[⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩],false⟩ := by
  unfold emittedSchema emittedRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem outputs : Outputs currentPlan extended := by
  unfold Outputs
  rw [emitted_schema]
  intro equation member
  cases List.mem_singleton.mp member
  change Equivalent (extended 4).1 GeneralDictionaryOptionalOutput229.value
  rw [output_retained]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem input_fits (name : Nat)
    (needed : name ∈ currentPlan.packet.declaration.inputNames ∨
      GeneralNominalSharedCaptures.Needed currentPlan.packet name) :
    GeneralNominalCaptureMerges.Fits extended
      ((GeneralNominalVersionedFrame231.capture currentPlan.packet).inputs name) (extended (binder currentPlan name)).1 := by
  have same : name = 0 := by
    rcases needed with named | needed
    · simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.Pattern.variables] using named
    · obtain ⟨clause,member,_⟩ := needed
      cases member
  subst name
  rw [binder_exact]
  change GeneralNominalCaptureMerges.Fits extended
    ((GeneralNominalVersionedAllocation231.capture _ _ _ _ currentPlan.packet.bindings).inputs 0) (extended actual).1
  rw [GeneralDictionaryUpper230Current.bindings_exact]
  exact GeneralDictionaryVersionedMerge231.actual_fits

theorem packet_holds : Holds currentPlan extended := by
  refine ⟨retains_journal.1,⟨GeneralDictionaryVersionedProjection231.ordinary,
    GeneralDictionaryVersionedProjection231.raw_projection,?_,input_fits,head_holds,?_,?_⟩,outputs⟩
  · exact point_root_holds snapshot.seed root root_point extended
  · intro equation member _
    exact outputs equation member
  · intro clause member
    cases member

/-- Exact prospective total-packet regression, with the historical journal
retained in the same model. Not yet successor Reachable/Stable/EvidenceAt. -/
theorem journal_and_new_total_packet :
    ∃ m, GeneralNominalCenteredHeadMatStepJournal.Models after m ∧ Holds currentPlan m :=
  ⟨extended,retains_journal,packet_holds⟩
end Yulang.GeneralDictionaryVersionedPacket231
