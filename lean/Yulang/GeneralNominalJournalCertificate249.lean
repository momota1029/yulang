import Yulang.GeneralNominalOrderedJournalExpansion249
import Yulang.GeneralNominalOrderedJournalClosed249
import Yulang.GeneralPresenceProtectionCheck249
import Yulang.GeneralPresenceOrderedCheck247
/-! Executable checks on a materialized journal. The existing actual compiler
is noncomputable; no new executable source solver or rejection rule is claimed. -/
namespace Yulang.GeneralNominalJournalCertificate249
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247
open GeneralNominalRebaseJournalView243 (Journal)
open GeneralPresenceConsumerSupport246 (listTypedReads)
open CommonNominalFullCarrier

def reads (journal : Journal) (old : List (Entry Nat)) (consumers : List (Atom Nat)) (publicNames : List Nat) : List Nat :=
 GeneralNominalJournalSupport249.support journal ++ listTypedReads (rewrite old consumers) ++ publicNames

def check (journal : Journal) (old fresh : List (Entry Nat))
 (consumers : List (Atom Nat)) (publicNames : List Nat) : Bool :=
 GeneralPresenceOrderedCheck247.check old &&
 (GeneralPresenceOrderedCheck247.check fresh &&
 (GeneralPresenceProtectionCheck249.check (reads journal old consumers publicNames) fresh &&
 GeneralPresenceProtectionCheck249.check publicNames old))

theorem checked_public_models (state : GeneralNominalVersionedJournal232.State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state)
 (old fresh : List (Entry Nat)) (consumers : List (Atom Nat)) (publicNames : List Nat)
 (passed : check (GeneralNominalRebaseJournalView243.compile state (mapping old)) old fresh consumers publicNames = true)
 (boundary : Assignment) :
 (∃ assignment, GeneralNominalVersionedJournal232.Models state assignment ∧
   All model assignment (consumers ++ block old) ∧ Agrees model (fun name => name ∈ publicNames) assignment boundary) ↔
 (∃ assignment, (GeneralNominalRebaseJournalView243.compile state (mapping old)).Models assignment ∧
   All model assignment (rewrite old consumers ++ block fresh) ∧ Agrees model (fun name => name ∈ publicNames) assignment boundary) := by
 have checks : GeneralPresenceOrderedCheck247.check old = true ∧
     GeneralPresenceOrderedCheck247.check fresh = true ∧
     GeneralPresenceProtectionCheck249.check (reads (GeneralNominalRebaseJournalView243.compile state (mapping old)) old consumers publicNames) fresh = true ∧
     GeneralPresenceProtectionCheck249.check publicNames old = true := by
   simpa only [check,Bool.and_eq_true] using passed
 have allProtected := (GeneralPresenceProtectionCheck249.check_exact _ fresh).mp checks.2.2.1
 have oldProtected := (GeneralPresenceProtectionCheck249.check_exact publicNames old).mp checks.2.2.2
 apply GeneralNominalOrderedJournalExpansion249.public_models_iff state empty old fresh
   ((GeneralPresenceOrderedCheck247.check_exact old).mp checks.1)
   ((GeneralPresenceOrderedCheck247.check_exact fresh).mp checks.2.1)
 · intro name member entry present
   exact allProtected name (List.mem_append_left _ (List.mem_append_left _ member)) entry present
 · intro name member entry present
   exact allProtected name (List.mem_append_left _ (List.mem_append_right _ member)) entry present
 · exact oldProtected
 · intro name member entry present
   exact allProtected name (List.mem_append_right _ member) entry present
theorem check_of_within (state : GeneralNominalVersionedJournal232.State roles)
 (old fresh : List (Entry Nat)) (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh)
 (within : GeneralPresenceOrderedDependence247.TargetsWithin fresh old)
 (consumers : List (Atom Nat)) (publicNames : List Nat)
 (privateNames : ∀ name ∈ publicNames, ∀ entry ∈ old, entry.1 ≠ name) :
 check (GeneralNominalRebaseJournalView243.compile state (mapping old)) old fresh consumers publicNames = true := by
 have freshPrivate : ∀ name ∈ publicNames, ∀ entry ∈ fresh, entry.1 ≠ name := by
   intro name member entry present
   obtain ⟨original,found,equal⟩ := within entry present
   rw [← equal]
   exact privateNames name member original found
 simp only [check,Bool.and_eq_true]
 refine ⟨(GeneralPresenceOrderedCheck247.check_exact old).mpr oldSafe,
   (GeneralPresenceOrderedCheck247.check_exact fresh).mpr freshSafe,?_,
   (GeneralPresenceProtectionCheck249.check_exact publicNames old).mpr privateNames⟩
 apply (GeneralPresenceProtectionCheck249.check_exact _ fresh).mpr
 intro name member entry present
 rcases List.mem_append.mp member with member | member
 · rcases List.mem_append.mp member with member | member
   · exact GeneralNominalOrderedJournalClosed249.within_protected old oldSafe fresh within state name member entry present
   · exact GeneralPresenceOrderedExpansion249.protected_of_within old fresh oldSafe within consumers name member entry present
 · exact freshPrivate name member entry present

theorem protected_of_only_new (state : GeneralNominalVersionedJournal232.State roles)
 (old fresh : List (Entry Nat)) (oldSafe : SafeOrder old)
 (newReads : GeneralPresenceProtectionCheck249.NewProtected
   (GeneralNominalJournalSupport249.support (GeneralNominalRebaseJournalView243.compile state (mapping old))) old fresh) :
 GeneralNominalOrderedJournalExpansion249.Protected state old fresh :=
 GeneralPresenceProtectionCheck249.protected_of_new _ old fresh
   (GeneralNominalOrderedJournalClosed249.journal_closed old oldSafe state) newReads
end Yulang.GeneralNominalJournalCertificate249
