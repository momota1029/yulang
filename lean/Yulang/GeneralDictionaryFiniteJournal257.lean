import Yulang.GeneralDictionaryJournalRepair257
namespace Yulang.GeneralDictionaryFiniteJournal257
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (View)
open GeneralDictionaryLooseLoopPacket240 (actual)
open GeneralDictionaryUpperHistory257 (history)
open GeneralDictionaryLooseIterationBook240 (context)
open GeneralPresenceOrderedBlock247 (solve)
open CommonNominalFullCarrier

def view (n : Nat) : View :=
 { GeneralDictionaryFiveSlot257.view n with
   ordinary := (GeneralDictionaryFiveSlot257.view n).ordinary ++ GeneralDictionaryBinderFact257.facts }

theorem models_exact (n : Nat) (assignment : Assignment) :
 (view n).Models assignment ↔
 (GeneralDictionaryFiveSlot257.view n).Models assignment ∧ GeneralDictionaryBinderFact257.Holds assignment := by
 unfold View.Models
 change (All model assignment ((GeneralDictionaryFiveSlot257.view n).ordinary ++ GeneralDictionaryBinderFact257.facts) ∧ _) ↔ _
 rw [all_append,GeneralDictionaryBinderFact257.facts_exact]
 constructor
 · rintro ⟨⟨ordinary,binder⟩,rest⟩; exact ⟨⟨ordinary,rest⟩,binder⟩
 · rintro ⟨⟨ordinary,rest⟩,binder⟩; exact ⟨⟨ordinary,binder⟩,rest⟩

theorem solve_binder (n : Nat) (assignment : Assignment) :
 GeneralDictionaryBinderFact257.Holds (solve model (history n) assignment) ↔ GeneralDictionaryBinderFact257.Holds assignment := by
 have binder := GeneralPresenceOrderedBlock247.solve_outside model (history n) assignment actual (GeneralDictionaryBinderGap257.actual_outside n)
 have initial : solve model (history n) assignment 2 = assignment 2 := by
   apply GeneralPresenceOrderedBlock247.solve_outside
   intro entry member
   have above := GeneralDictionaryUpperHistory257.targets_above n entry member
   omega
 unfold GeneralDictionaryBinderFact257.Holds
 rw [binder,initial]

/-- The finite View is interpreted under the ordered raw solver, with the
actual center certificate retained. It is not a source-state transition. -/
theorem solved_exact (n : Nat) (assignment : Assignment) :
 (view (n+1)).Models assignment ↔
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1))
   (solve model (history (n+1)) assignment) := by
 rw [models_exact,GeneralDictionaryJournalRepair257.exact,solve_binder]
 exact and_congr ((GeneralDictionaryFiveSlot257.models_exact (n+1) assignment).symm.trans
   (GeneralDictionaryCompactView257.compact_solved (n+1) assignment)) Iff.rfl

def Agree (internal boundary : Assignment) : Prop :=
 (∀ name, name ≤ 4 ∨ name = actual → internal name = boundary name) ∧
 (∀ name, (internal name).2 = (boundary name).2)

theorem solve_agrees (n : Nat) (internal boundary : Assignment) (same : Agree internal boundary) :
 Agree (solve model (history n) internal) boundary := by
 constructor
 · intro name kept
   have fixed : solve model (history n) internal name = internal name := by
     apply GeneralPresenceOrderedBlock247.solve_outside
     intro entry member
     rcases kept with small | rfl
     · have above := GeneralDictionaryUpperHistory257.targets_above n entry member
       omega
     · exact GeneralDictionaryBinderGap257.actual_outside n entry member
   exact fixed.trans (same.1 name kept)
 · intro name
   exact (GeneralPresenceOrderedBlock247.solve_rows model (history n) internal name).trans (same.2 name)

theorem public_models (n : Nat) (boundary : Assignment) :
 (∃ internal, Agree internal boundary ∧
   GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1)) internal) ↔
 (∃ internal, Agree internal boundary ∧ (view (n+1)).Models internal) := by
 constructor
 · rintro ⟨internal,same,valid⟩
   obtain ⟨raw,binder⟩ := (GeneralDictionaryJournalRepair257.exact n internal).mp valid
   have blockValid : All model internal (GeneralPresenceDefinitionRewrite244.block (history (n+1))) :=
     fun atom member => raw.2.2 atom (GeneralDictionaryUpperHistory257.block_in_source (n+1) member)
   have compact := (GeneralDictionaryCompactView257.recovered (n+1) internal blockValid).mpr raw
   have small := (GeneralDictionaryFiveSlot257.models_exact (n+1) internal).mp compact
   exact ⟨internal,same,(models_exact (n+1) internal).mpr ⟨small,binder⟩⟩
 · rintro ⟨internal,same,valid⟩
   exact ⟨solve model (history (n+1)) internal,solve_agrees (n+1) internal boundary same,
     (solved_exact n internal).mp valid⟩

theorem stable (n : Nat) : view (n+1) = view 1 := by
 unfold view
 rw [GeneralDictionaryFiveSlot257.stable]

theorem ordinary_bound (n : Nat) : (view n).ordinary.length ≤ 10 := by
 change ((GeneralDictionaryFiveSlot257.view n).ordinary ++ GeneralDictionaryBinderFact257.facts).length ≤ 10
 rw [List.length_append,GeneralDictionaryBinderFact257.facts_length]
 have small := GeneralDictionaryFiveSlot257.ordinary_bound n
 omega
end Yulang.GeneralDictionaryFiniteJournal257
