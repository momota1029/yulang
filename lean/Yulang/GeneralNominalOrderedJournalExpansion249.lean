import Yulang.GeneralNominalJournalSupport249
import Yulang.GeneralNominalVersionedSourceCongruence238
import Yulang.GeneralPresenceOrderedExpansion249
/-! Full actual journal readback for expanded target domains. All lists are
those of the actual Journal243 compiler. LegacyEmpty and calculated support
protection remain explicit. This is not a new operational source transition. -/
namespace Yulang.GeneralNominalOrderedJournalExpansion249
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247
open GeneralPresenceCommonLaws245
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalRebaseJournalView243 (Journal)

def Protected (state : State roles) (old fresh : List (Entry Nat)) : Prop :=
 ∀ name ∈ GeneralNominalJournalSupport249.support
   (GeneralNominalRebaseJournalView243.compile state (mapping old)),
   ∀ entry ∈ fresh, entry.1 ≠ name

theorem journal_preserved (journal : Journal) (fresh : List (Entry Nat)) (assignment : Assignment)
 (protectedReads : ∀ name ∈ GeneralNominalJournalSupport249.support journal,
   ∀ entry ∈ fresh, entry.1 ≠ name) :
 journal.Models (solve model fresh assignment) ↔ journal.Models assignment := by
 apply GeneralNominalJournalSupport249.models_iff journal _ assignment (solve_rows model fresh assignment)
 intro name member
 exact congrArg Prod.fst (solve_outside model fresh assignment name (protectedReads name member))

theorem journal_exact (state : State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state)
 (entries : List (Entry Nat)) (assignment : Assignment) :
 (GeneralNominalRebaseJournalView243.compile state (mapping entries)).Models assignment ↔
 GeneralNominalVersionedJournal232.Models state (solve model entries assignment) := by
 rw [GeneralNominalRebaseJournalView243.compile_exact state empty,
   GeneralNominalOrderedRaw248.read_mapping]

theorem journal_forward (state : State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state)
 (old fresh : List (Entry Nat)) (protectedReads : Protected state old fresh)
 (assignment : Assignment) (valid : All model assignment (block old)) :
 (GeneralNominalRebaseJournalView243.compile state (mapping old)).Models (solve model fresh assignment) ↔
 GeneralNominalVersionedJournal232.Models state assignment := by
 rw [journal_preserved _ fresh assignment protectedReads,journal_exact state empty]
 exact GeneralNominalVersionedSourceCongruence238.models_iff
   (GeneralPresenceOrderedRecovery247.solve_compatible model common_laws old assignment valid) state empty

theorem public_models_iff (state : State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state)
 (old fresh : List (Entry Nat)) (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh)
 (protectedJournal : Protected state old fresh) (consumers : List (Atom Nat))
 (protectedConsumers : GeneralPresenceOrderedExpansion249.Protected old fresh consumers)
 (sharedNames : Nat → Prop)
 (oldPrivate : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (freshPrivate : ∀ name, sharedNames name → ∀ entry ∈ fresh, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, GeneralNominalVersionedJournal232.Models state assignment ∧
   All model assignment (consumers ++ block old) ∧ Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, (GeneralNominalRebaseJournalView243.compile state (mapping old)).Models assignment ∧
   All model assignment (rewrite old consumers ++ block fresh) ∧ Agrees model sharedNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,journal,valid,agree⟩
   refine ⟨solve model fresh assignment,?_,
     GeneralPresenceOrderedExpansion249.models_forward model common_laws old fresh freshSafe
       consumers protectedConsumers assignment valid,?_⟩
   · exact (journal_forward state empty old fresh protectedJournal assignment
       ((all_append model assignment _ _).mp valid).2).mpr journal
   · intro name shared
     rw [solve_outside model fresh assignment name (freshPrivate name shared)]
     exact agree name shared
 · rintro ⟨assignment,journal,valid,agree⟩
   refine ⟨solve model old assignment,(journal_exact state empty old assignment).mp journal,
     GeneralPresenceOrderedRebase247.models_backward model common_laws old fresh oldSafe consumers assignment valid,?_⟩
   intro name shared
   rw [solve_outside model old assignment name (oldPrivate name shared)]
   exact agree name shared

theorem mixed_source_exact (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (entries : List (Entry Nat)) (assignment : Assignment) :
 (GeneralNominalRebaseJournalView243.compile state (mapping entries)).Models assignment ↔
 GeneralNominalVersionedJournal232.Models state (solve model entries assignment) :=
 journal_exact state (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reachable) entries assignment

theorem point_source_exact (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state)
 (entries : List (Entry Nat)) (assignment : Assignment) :
 (GeneralNominalRebaseJournalView243.compile state (mapping entries)).Models assignment ↔
 GeneralNominalVersionedJournal232.Models state (solve model entries assignment) := by
 rw [GeneralNominalRebaseJournalView243.point_source_exact reachable,
   GeneralNominalOrderedRaw248.read_mapping]
theorem point_legacy_empty (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state) :
 GeneralNominalVersionedMixedRegistry234.LegacyEmpty state := by
 obtain ⟨initial,source,path⟩ := reachable
 exact GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty
   (show B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state from
     ⟨initial,source,GeneralNominalPointErasure240.steps_old path⟩)

theorem point_journal_forward (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state)
 (old fresh : List (Entry Nat)) (protectedReads : Protected state old fresh)
 (assignment : Assignment) (valid : All model assignment (block old)) :
 (GeneralNominalRebaseJournalView243.compile state (mapping old)).Models (solve model fresh assignment) ↔
 GeneralNominalVersionedJournal232.Models state assignment :=
 journal_forward state (point_legacy_empty state reachable) old fresh protectedReads assignment valid
end Yulang.GeneralNominalOrderedJournalExpansion249
