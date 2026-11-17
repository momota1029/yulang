import Yulang.GeneralDictionaryVersionedPrepared231
import Yulang.GeneralNominalVersionedEvidence231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedEvidence231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedNames231

theorem frame : GeneralNominalVersionedEvidence231.Frame registry after.core root declaration.id currentPlan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,
    rfl,rfl,GeneralDictionaryVersionedPrepared231.prepared⟩

theorem children_empty : GeneralNominalVersionedFrame231.children currentPacket = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [GeneralNominalVersionedFrame231.children_length_eq,GeneralDictionaryUpper230Regression.children_empty]
  rfl

theorem class_effects : GeneralNominalVersionedEffects231.ClassEffects after.core root currentPlan extended := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro output member body found
    cases GeneralDictionaryUpper230Selected.request_exact member
    have equal : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
    subst body
    intro equation present
    cases List.mem_singleton.mp present
    change CommonNominalFullCarrier.Equivalent (extended 4).1 GeneralDictionaryOptionalOutput229.value
    rw [output_retained]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · intro first one last two _
    cases GeneralDictionaryUpper230Selected.request_exact one
    cases GeneralDictionaryUpper230Selected.request_exact two
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem certificate : GeneralNominalVersionedEvidence231.Certificate
    registry after.core extended root declaration.id [] currentPlan :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics frame children_empty.symm
    GeneralDictionaryVersionedPacket231.packet_holds ready class_effects

theorem evidence : GeneralNominalVersionedEvidence231.Evidence
    registry after.core extended root (.node declaration.id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨currentPlan,certificate⟩

theorem old_no_instance : ¬ GeneralDictionaryTotalEvidence206.Instance
    registry after.core extended root key children :=
  GeneralDictionaryUpper230Current.no_instance rfl rfl rfl extended two_retained lower_retained

theorem old_no_evidence (dictionaries) : ¬ GeneralDictionaryTotalEvidence206.Evidence
    registry after.core extended root (.node declaration.id dictionaries) := by
  intro given
  have payload := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr given
  cases payload with
  | node source _ => exact old_no_instance source

/-- Nonempty evidence-component regression in a common full model. This does
not establish universal EvidenceAt or operational reachability in a successor
boundary; that boundary and its twelve laws are still to be constructed. -/
theorem common_model_evidence :
    ∃ m, GeneralNominalCenteredHeadMatStepJournal.Models after m ∧
      GeneralNominalVersionedPlans231.Holds currentPlan m ∧
      GeneralNominalVersionedEvidence231.Evidence registry after.core m root (.node declaration.id []) ∧
      ¬ GeneralDictionaryTotalEvidence206.Evidence registry after.core m root (.node declaration.id []) :=
  ⟨extended,retains_journal,GeneralDictionaryVersionedPacket231.packet_holds,evidence,old_no_evidence []⟩

end Yulang.GeneralDictionaryVersionedEvidence231
