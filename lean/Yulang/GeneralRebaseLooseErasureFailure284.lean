import Yulang.GeneralRebaseRawWatchFailure284
import Yulang.GeneralRebaseLoopView282

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseLooseErasureFailure284
open GeneralDictionaryLooseLoopSource240 (model F)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralRebaseLooseAliases283 (history_shape canonical)
open GeneralRebaseLoopBase282.Loose (decode_reach)
open GeneralRebaseAliasFamily283 (lowerRow upperRow)
open GeneralRebaseAliasMemo283 (assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralRebaseHistoryOrder282 (history decode compatible)
open GeneralRebaseRawWatchFailure284 (eraseProbe omitted_unsound nominal_not_bottom)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralPresenceDefinitionRewrite244 (Entry)

theorem determined (n : Nat) (row : Entry Nat) (recorded : row ∈ history (state n)) :
    ∃ front ∈ ([2,4] : List Nat), ∀ a, Models (state n) a → Equivalent (a row.1).1 (a front).1 := by
  obtain ⟨memo,_,lowerExact,upperExact,interp⟩ := canonical n
  obtain ⟨i,less,rfl|rfl⟩ := (history_shape n row).mp recorded
  · refine ⟨2,List.mem_cons_self,?_⟩
    intro a good
    have x := (interp a (lower (i+1))).1
    change Equivalent (a (GeneralRebaseAliasMemo283.root memo (lower (i+1)))).1 (decode (state n) a (lower (i+1))).1 at x
    rw [lowerExact (i+1) (by omega)] at x
    have final := (compatible (decode_reach n) good (lower (i+1))).1
    have both := GeneralRebaseLoopBase282.equiv_trans x final
    exact ⟨both.2,both.1⟩
  · refine ⟨4,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
    intro a good
    have x := (interp a (upper i)).1
    change Equivalent (a (GeneralRebaseAliasMemo283.root memo (upper i))).1 (decode (state n) a (upper i)).1 at x
    rw [upperExact i less] at x
    have final := (compatible (decode_reach n) good (upper i)).1
    have both := GeneralRebaseLoopBase282.equiv_trans x final
    exact ⟨both.2,both.1⟩

theorem any_omitted_counterexample (n : Nat) (watch : List Nat) (row : Entry Nat)
    (stored : row ∈ history (state n)) (missing : row.1 ∉ watch) :
    ∃ base : Assignment, Models (state n) (decode (state n) base) ∧
      ¬ Models (state n) (GeneralPresenceOrderedBlock247.solve CommonNominalFullCarrier.model
        (GeneralRebaseFutureWatch284.trim watch (history (state n))) base) := by
  obtain ⟨front,listed,forces⟩ := determined n row stored
  have seed := GeneralRebaseLoopView282.Loose.seed_exact n
  have known : front ≤ (GeneralRebaseMixedOwnedTrace277.raw (state n)).seed := by
    rw [seed]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
    rcases listed with rfl|rfl <;> decide
  have visible := (GeneralRebaseWholeJournal282.source_visibility (decode_reach n) [front]
    (fun _ d => List.mem_singleton.mp d ▸ known)).1 front (List.mem_singleton_self _)
  have notBottom : ¬ CommonNominalFullCarrier.Subtype (model front).1 .bottom := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
    rcases listed with rfl|rfl <;> exact nominal_not_bottom
  exact ⟨_,omitted_unsound (decode_reach n) model (stages n).valid watch row stored missing front visible notBottom forces⟩

end Yulang.GeneralRebaseLooseErasureFailure284
