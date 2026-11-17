import Yulang.GeneralDictionaryVersionedReconstruction231
import Yulang.GeneralNominalVersionedPreparedTransport231
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! Nonvacuous modelwise evidence in the actually reconstructed current frame.
The context/state transformer is explicit, but no successor operational
Reachable/Stable judgment or full V8 EvidenceAt theorem is asserted here. -/
namespace Yulang.GeneralDictionaryVersionedFinal231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedReconstruction231
open GeneralNominalVersionedInstallation231
open GeneralNominalCommonBridge (Assignment)

theorem frame : GeneralNominalVersionedEvidence231.Frame
    registry reconstructed.core root declaration.id replayed :=
  GeneralNominalVersionedPreparedTransport231.frame_extended
    (reserved currentPacket) (atoms currentPacket) (allocated currentPacket)
    registry after.core root declaration.id currentPlan GeneralDictionaryVersionedEvidence231.frame
    (fun _ h => h) GeneralDictionaryVersionedNames231.extended
    (replay_valid currentPlan GeneralDictionaryVersionedNames231.extended
      GeneralDictionaryVersionedPacket231.packet_holds)

theorem request_exact (member : output ∈ GeneralNominalCenteredHeadOutputs.requests reconstructed.core root) :
    output = ⟨0,4⟩ :=
  GeneralDictionaryUpper230Selected.request_exact
    (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
      (before := reconstructed.core) (after := after.core) (fun _ h => h) (fun _ h => h) member)

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready reconstructed.core root replayed := by
  intro output member
  cases request_exact member
  exact ⟨.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩,rfl,rfl⟩

theorem class_effects (valid : GeneralNominalCenteredHeadMatStepJournal.Models reconstructed m) :
    GeneralNominalVersionedEffects231.ClassEffects reconstructed.core root replayed m := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro output member body found
    cases request_exact member
    have equal : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
    subst body
    intro equation present
    cases List.mem_singleton.mp present
    have out := GeneralDictionaryVersionedUniversal231.outputs ((models_iff m).mp valid).1
    unfold GeneralNominalVersionedPlans231.Outputs at out
    rw [GeneralDictionaryVersionedPacket231.emitted_schema] at out
    have equation := out ⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩ (List.mem_singleton_self _)
    change CommonNominalFullCarrier.Equivalent (m 4).1 GeneralDictionaryOptionalOutput229.value at equation ⊢
    exact equation
  · intro first one last two _
    cases request_exact one
    cases request_exact two
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem certificate (valid : GeneralNominalCenteredHeadMatStepJournal.Models reconstructed m) :
    GeneralNominalVersionedEvidence231.Certificate registry reconstructed.core m root declaration.id [] replayed :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics frame
    GeneralDictionaryVersionedReconstruction231.children_empty.symm
    (packet_holds valid) ready (class_effects valid)

theorem evidence (valid : GeneralNominalCenteredHeadMatStepJournal.Models reconstructed m) :
    GeneralNominalVersionedEvidence231.Evidence registry reconstructed.core m root (.node declaration.id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨replayed,certificate valid⟩

theorem nonvacuous_current_frame_completion :
    (∃ m, GeneralNominalCenteredHeadMatStepJournal.Models reconstructed m) ∧
      ∀ m, GeneralNominalCenteredHeadMatStepJournal.Models reconstructed m →
        GeneralNominalVersionedEvidence231.Evidence registry reconstructed.core m root (.node declaration.id []) :=
  ⟨GeneralDictionaryVersionedReconstruction231.inhabited,fun _ => evidence⟩

end Yulang.GeneralDictionaryVersionedFinal231
