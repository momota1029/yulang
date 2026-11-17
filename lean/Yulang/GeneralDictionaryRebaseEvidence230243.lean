import Yulang.GeneralNominalRebaseEvidenceProjection243
import Yulang.GeneralDictionaryRebase230Public242
import Yulang.GeneralDictionaryVersionedCompletion231
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
/-! Nonempty full recursive evidence survives local stable-name replacement
in the real 230 reconstructed example. This is an existential public-model
projection, not a new source-kernel reachability claim. -/
namespace Yulang.GeneralDictionaryRebaseEvidence230243
open GeneralDictionaryRebase230Public242 (oldEntries newEntries hidden)
open GeneralDictionaryJournalRefinement228Source (snapshot root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryOptionalInstall229 (model)
open GeneralDictionaryVersionedNames231 (extended)
open GeneralDictionaryRebase230Private241 (oldBindings newBindings)
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseEscapedMerges242
open GeneralNominalRebasePublicModel242 (Models)
open GeneralNominalRebaseEscapedStore242 (definitionBlock)

theorem old_support : (definitionBlock oldEntries).flatMap GeneralNominalState.atomSources ⊆
 GeneralDictionaryVersionedSupport231.pool := by decide +kernel

theorem old_definitions : Definitions oldEntries extended := by
 apply (GeneralNominalRebaseEscapedStore242.definitions_iff oldEntries extended).mp
 have original := (GeneralNominalRebaseEscapedStore242.definitions_iff oldEntries model).mpr GeneralDictionaryRebase230Public242.old_definitions
 intro atom member
 apply (GeneralNominalCenteredModelExtension.atom_same atom (first := extended) (last := model) ?_).mpr (original atom member)
 intro name present
 exact GeneralDictionaryVersionedNames231.old_value name (old_support (List.mem_flatMap.mpr ⟨atom,member,present⟩))

theorem original_evidence : GeneralNominalVersionedEvidence231.Evidence registry GeneralDictionaryUpper230Step.after.core extended root (.node declaration.id []) :=
 GeneralDictionaryVersionedCompletion231.evidence
   ⟨GeneralDictionaryVersionedNames231.retains_journal,GeneralDictionaryVersionedMerge231.merge_model⟩

def before (publicModel : GeneralNominalCommonBridge.Assignment) : Prop :=
 Models hidden (fun internal => Definitions oldEntries internal ∧
   GeneralNominalVersionedEvidence231.Evidence registry GeneralDictionaryUpper230Step.after.core internal root (.node declaration.id [])) publicModel

def after (publicModel : GeneralNominalCommonBridge.Assignment) : Prop :=
 Models hidden (fun internal => Definitions newEntries internal ∧
   GeneralNominalRebaseEvidenceView243.Evidence registry GeneralDictionaryUpper230Step.after.core
   (GeneralNominalRebaseLookup242.substitution oldEntries) internal root (.node declaration.id [])) publicModel

theorem public_exact (publicModel : GeneralNominalCommonBridge.Assignment) : before publicModel ↔ after publicModel :=
 GeneralNominalRebaseEvidenceProjection243.evidence_public_replacement oldEntries newEntries
   (GeneralNominalRebaseDefinitions241.coherent snapshot.seed root.identity declaration.id oldBindings declaration.inputNames)
   (external_entries _ _ _ _ _ GeneralDictionaryRebase230Public242.old_fresh GeneralDictionaryRebase230Public242.old_linked)
   (GeneralNominalRebaseDefinitions241.coherent snapshot.seed root.identity declaration.id newBindings declaration.inputNames)
   (external_entries _ _ _ _ _ GeneralDictionaryRebase230Private241.isolated GeneralDictionaryRebase230Private241.linked)
   (targets_within _ _ _ _ _ _ GeneralDictionaryRebase230Public242.multiplicity)
   GeneralDictionaryRebase230Public242.targets_hidden registry GeneralDictionaryUpper230Step.after.core root (.node declaration.id []) publicModel

theorem nonvacuous : before extended ∧ after extended := by
 have original : before extended := ⟨extended,⟨fun _ _ => rfl,fun _ => rfl⟩,old_definitions,original_evidence⟩
 exact ⟨original,(public_exact extended).mp original⟩
theorem replacement_values : ∃ internal,
 Definitions newEntries internal ∧
 GeneralNominalRebaseEvidenceView243.Evidence registry GeneralDictionaryUpper230Step.after.core
   (GeneralNominalRebaseLookup242.substitution oldEntries) internal root (.node declaration.id []) ∧
 (internal GeneralDictionaryOptionalInstall229.actual).1 = .emptyRecord ∧
 (internal 4).1 = GeneralDictionaryOptionalOutput229.value ∧
 CommonNominalFullCarrier.Equivalent (internal GeneralDictionaryOptionalInstall229.lo).1 .emptyRecord := by
 obtain ⟨internal,same,definitions,evidence⟩ := nonvacuous.2
 have actual : internal GeneralDictionaryOptionalInstall229.actual = extended GeneralDictionaryOptionalInstall229.actual :=
   same.1 _ (by decide +kernel)
 have four : internal 4 = extended 4 := same.1 _ (by decide +kernel)
 have two : internal 2 = extended 2 := same.1 _ (by decide +kernel)
 have block := (GeneralNominalRebaseEscapedStore242.definitions_iff newEntries internal).mpr definitions
 rw [definition_block_eq snapshot registry root.identity declaration newBindings] at block
 have lower := GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value
   (name := 0) (by decide +kernel : 0 ∈ declaration.inputNames) block
 change CommonNominalFullCarrier.Equivalent (internal GeneralDictionaryOptionalInstall229.lo).1 (internal 2).1 at lower
 rw [two,GeneralDictionaryVersionedNames231.two_retained] at lower
 exact ⟨internal,definitions,evidence,by rw [actual,GeneralDictionaryVersionedNames231.actual_retained],
   by rw [four,GeneralDictionaryVersionedNames231.output_retained],lower⟩
end Yulang.GeneralDictionaryRebaseEvidence230243
