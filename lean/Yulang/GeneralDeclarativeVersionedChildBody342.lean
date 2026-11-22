import Yulang.GeneralDeclarativeVersionedChildView342
import Yulang.GeneralWhereOriginSupport318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15500
set_option maxHeartbeats 8000000
namespace Yulang.GeneralDeclarativeVersionedChildBody342
open GeneralDeclarativeVersionedChildView342 (basis arg d code lower actual upper in_every_model range support done)
open GeneralWhereOriginSingleCells318 (loNow hi)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralWherePhysicalCommit319 (final)
open GeneralWhereOriginSingleSource318 (sourceRegistry)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralWhereOriginSupport318 (journalSources journal_models)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeAggregate324 (aligned kept ready aggregate_model)
open GeneralDeclarativeFreshTerms324 (first second protectedNames)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeStableAssemble329 (merged tieState)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeTaggedElection340 (Ranked)
open GeneralDeclarativeTraceNames321 (names)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeBounds319 (Bound)
open PresenceNormalForm (Atom)

abbrev seed : Capture := point 2
abbrev spans : List (Nat × Capture) := [(0,seed)]
def fallback (_ : Nat) := seed
def targets (_ : GeneralDeclarations.Clause) (_ : Nat) := 0
noncomputable def keep : List Nat := [loNow,mid,hi,2] ++ journalSources final
noncomputable abbrev freshL := first (aligned basis seed []) (kept keep seed []) (.var 2) (.var 2)
noncomputable abbrev freshH := second (aligned basis seed []) (kept keep seed []) (.var 2) (.var 2)
noncomputable abbrev expanded := ready basis keep seed []

theorem tie_literal : tieState basis spans fallback = basis := rfl

theorem compiled :
    compileBody sourceRegistry interpretation d leaf basis spans keep fallback targets = some (expanded,[]) := by
  unfold compileBody
  rw [show merged basis keep spans fallback = ⟨expanded,
      fun n => if n = 0 then GeneralDeclarativeAggregate324.span basis keep seed [] else fallback n⟩ from rfl]
  simp [GeneralDeclarativeClauseBatch327.prepare,GeneralDeclarativeWhereOutputBatch327.whole,
    GeneralDeclarativeBatch320.collect,GeneralDeclarativeEmissionForest322.children,
    GeneralDeclarativeEntailment320.appendFacts,leaf]

theorem edges :
    expanded.normal.ordinary =
      [.tyLe (.var 2) (.var 2),.tyLe (.var 2) (.var 2),
      .tyLe (.var freshL) (.var 2),.tyLe (.var 2) (.var freshL),
      .tyLe (.var freshH) (.var 2),.tyLe (.var 2) (.var freshH),
      .tyLe (.var freshL) (.var 2),.tyLe (.var 2) (.var freshH)] := rfl

theorem grown : Extends basis expanded :=
  ⟨(by intro a there; cases there),fun _ h => h,fun _ h => h⟩

theorem not_original (n : Nat) (used : n ∈ [loNow,mid,hi,2]) : n < freshL := by
  apply GeneralDeclarativeNewNames321.before_after
  unfold protectedNames
  apply List.mem_append_left _
  apply List.mem_append_left _
  apply List.mem_append_right _
  exact List.mem_append_left _ (List.mem_append_left _ used)

noncomputable def level (n : Nat) : Nat := if n = 2 ∨ n = freshL ∨ n = freshH then 0 else 1

theorem level2 : level 2 = 0 := by simp [level]
theorem levelLo : level freshL = 0 := by simp [level]
theorem levelHi : level freshH = 0 := by simp [level]

theorem level_source {n : Nat} (used : n ∈ [loNow,mid,hi]) (notTwo : n ≠ 2) : level n = 1 := by
  have below : n < freshL := not_original n (List.mem_append_left [2] used)
  have more : n ≠ freshH := by
    change n ≠ freshL + 1
    omega
  simp [level,notTwo,Nat.ne_of_lt below,more]

theorem old_sources :
    loNow ≠ 2 ∧ mid ≠ 2 ∧ hi ≠ 2 := by
  have lo : 4 < loNow := GeneralNominalIdentities.source_above_seed _ _
  have middle : 4 < mid := GeneralNominalIdentities.source_above_seed _ _
  have upper : 4 < hi := GeneralNominalIdentities.source_above_seed _ _
  omega

theorem lo_level : level loNow = 1 := level_source List.mem_cons_self old_sources.1
theorem mid_level : level mid = 1 :=
  level_source (List.mem_cons_of_mem _ List.mem_cons_self) old_sources.2.1
theorem hi_level : level hi = 1 :=
  level_source (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) old_sources.2.2

theorem level_bound (h : Bound expanded.normal a b) : level a ≤ level b := by
  induction h with
  | interval present =>
    rcases List.mem_cons.mp present with exact | rest
    · cases exact
      simp only [lo_level,mid_level,Nat.le_refl]
    · cases List.mem_singleton.mp rest
      simp only [mid_level,hi_level,Nat.le_refl]
  | constraint present =>
    rw [edges] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with h|h|h|h|h|h|h|h <;> cases h <;>
      simp only [level2,levelLo,levelHi,Nat.le_refl]
  | refl => exact Nat.le_refl _
  | trans _ _ one last => exact Nat.le_trans one last

theorem ranked : Ranked expanded level := by
  refine ⟨level_bound,?_,?_⟩
  · intro x y found
    change (⟨x,.variable y⟩ : GeneralDeclarativeHead320.Equation) ∈ [lower,actual,upper] at found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with no|no|no <;> cases no
  · intro row seen n mentioned _
    change row ∈ [lower,actual,upper] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with rfl|rfl|rfl
    all_goals
      have two : n = 2 := List.mem_singleton.mp mentioned
      subst n
      first
      | simpa only [level2,lo_level] using Nat.zero_lt_one
      | simpa only [level2,mid_level] using Nat.zero_lt_one
      | simpa only [level2,hi_level] using Nat.zero_lt_one

/-- Conservative across the whole separate versioned ledger, not just
the mixed subjournal and not just on a handful of selected names. -/
theorem current_models (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) :
    ∃ n, Models expanded n ∧
      GeneralWhereVersionInstall317.Models final n ∧ ∀ k ∈ journalSources final, n k = m k := by
  have each : ∀ a ∈ [seed], GeneralDeclarativeDemand320.Bounds basis a := by
    intro a h
    cases List.mem_singleton.mp h
    exact point_bounded _ _
  have share : GeneralDeclarativeMergeCenters324.Linked basis seed [] := by
    intro n _ a h
    cases List.mem_singleton.mp h
    exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  obtain ⟨n,models,agrees⟩ := aggregate_model (extra := keep) each share m (in_every_model m valid)
  have common k (h : k ∈ journalSources final) : n k = m k :=
    agrees k (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ h)))
  exact ⟨n,models,(journal_models final (fun k h => common k h)).mpr valid,common⟩

end Yulang.GeneralDeclarativeVersionedChildBody342
