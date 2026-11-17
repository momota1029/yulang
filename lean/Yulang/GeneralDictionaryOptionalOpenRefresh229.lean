import Yulang.GeneralDictionaryOptionalJoint229

/-! The optional-field barrier is not a proof of global stability. Generated
upper aggregates are still unknown in the five-slot snapshot, despite having a
trusted exact width-record meaning. Constructing a support-preserving refresh
and exhausting all administrative cases remain separate obligations. -/
namespace Yulang.GeneralDictionaryOptionalOpenRefresh229
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryOptionalStage229
open GeneralNominalCenteredHeadMatStepSupport
open GeneralNominalCenteredHeadMatStepObservations
open CommonNominalFullCarrier GeneralNominalCenters

theorem generated_unknown (purpose : Nat) :
    ¬ GeneralNominalState.Known stage.core.erased.current.context.state
      (fresh snapshot.seed root.identity declaration.id purpose 0 0) := by
  rintro ⟨slot,same,_⟩
  have bound : slot.val < 5 := slot.isLt
  change slot.val = _ at same
  have large := fresh_large purpose
  omega

theorem readback : Readback stage [] plan := by
  intro slot member test observation head m valid
  exact GeneralCanonicalObservations.recorded_sound snapshot m valid.1
    (GeneralNominalSupport.head_recorded head)

theorem input_trusted : Trusted stage [.input plan] :=
  .input plan .source (List.mem_cons_self ..) readback

theorem upper_justified : Justifies stage (fun m => Equivalent (m hi).1 .emptyRecord) := by
  refine ⟨[.input plan],input_trusted,?_⟩
  intro m valid
  have input : GeneralNominalCenteredHeadMatStepPackets.Inputs plan m :=
    valid.2.2 (.input plan) (List.mem_cons_self ..)
  have merges := input.1.2.1
  rw [bindings_exact] at merges
  change PresenceNormalForm.All CommonNominalFullCarrier.model m
    ((GeneralNominalAllocation.equations lo (.union (.var 4) (.var 4)) ++
      GeneralNominalAllocation.equations hi (.inter (.var 2) (.var 2))) ++ _) at merges
  have upper := ((PresenceNormalForm.all_append ..).mp
    ((PresenceNormalForm.all_append ..).mp merges).1).2
  have equal := (GeneralNominalCaptureMerges.equations_exact ..).mp upper
  change Equivalent (m hi).1 (.inter (m 2).1 (m 2).1) at equal
  have width := width_two m valid.1
  have self : Equivalent (.inter (m 2).1 (m 2).1) (m 2).1 :=
    ⟨(common_inter_is_meet ..).mp (subtype_refl _) |>.1,
      (common_inter_is_meet ..).mpr ⟨subtype_refl _,subtype_refl _⟩⟩
  exact ⟨subtype_trans equal.1 (subtype_trans self.1 width.1),
    subtype_trans width.2 (subtype_trans self.2 equal.2)⟩

theorem upper_supported : hi ∈ GeneralNominalState.sources stage.core.erased.current.context.state := by
  apply List.mem_append_left
  apply List.mem_append_right
  change hi ∈ ([] ++ GeneralNominalAllocation.reserved snapshot registry root.identity) ++ []
  simp only [List.nil_append,List.append_nil]
  exact GeneralNominalAllocationSupport.reservation snapshot _
    (GeneralNominalAllocationSupport.input_key (List.mem_singleton_self declaration)
      (by decide : 0 ∈ declaration.inputNames) (Or.inr rfl))

/-- These are premises a future head-completion construction must handle.
They do not assert that a valid refining context has already been built. -/
theorem outstanding_upper :
    hi ∈ GeneralNominalState.sources stage.core.erased.current.context.state ∧
    ¬ GeneralNominalState.Known stage.core.erased.current.context.state hi ∧
    Justifies stage (fun m => Equivalent (m hi).1 .emptyRecord) :=
  ⟨upper_supported,generated_unknown 1,upper_justified⟩

end Yulang.GeneralDictionaryOptionalOpenRefresh229
