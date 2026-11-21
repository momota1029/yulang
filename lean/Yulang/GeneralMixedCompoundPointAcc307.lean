import Yulang.GeneralMixedCompoundPointExact307

namespace Yulang.GeneralMixedCompoundPointAcc307
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralMixedCompoundRefreshBound307 (Run score score_le)
open GeneralMixedCompoundPointExact307 (every_step raw_score_lt RawRun exact_run)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)

def remaining (s : State roles) : Nat := 3 - score s

theorem decreases {s t : State roles} (path : Run n s) (move : Step registry root s t) :
    remaining t < remaining s := by
  have less := raw_score_lt path move
  have limit := score_le t
  unfold remaining
  omega

theorem accessible_at {s : State roles} (path : Run n s) :
    Acc (fun after before => Step registry root before after) s := by
  let claim (fuel : Nat) := ∀ n (s : State roles), remaining s = fuel → Run n s →
    Acc (fun after before => Step registry root before after) s
  have inductiveClaim (fuel : Nat) : claim fuel := by
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro k s eq live
      refine Acc.intro s ?_
      intro t move
      have less := decreases live move
      rw [eq] at less
      apply ih (remaining t) less (k+1) t rfl
      exact every_step live move
  exact inductiveClaim (remaining s) n s rfl path

theorem accessible : Acc (fun after before => Step registry root before after) point :=
    accessible_at .zero

theorem saturated_from {s : State roles} (path : Run n s) :
    ∃ t, B4Target.Steps (Step registry root) s t ∧ (∀ next, ¬ Step registry root t next) := by
  classical
  have h := accessible_at path
  induction h generalizing n with
  | intro s _ ih =>
    by_cases next : ∃ t, Step registry root s t
    · obtain ⟨t,first⟩ := next
      obtain ⟨halt,after,stop⟩ := ih t first (every_step path first)
      have prepend {after : State roles} (rest : B4Target.Steps (Step registry root) t after) :
          B4Target.Steps (Step registry root) s after := by
        induction rest with
        | refl => exact .tail .refl first
        | tail _ step ih => exact .tail ih step
      exact ⟨halt,prepend after,stop⟩
    · exact ⟨s,.refl,fun t act => next ⟨t,act⟩⟩

theorem full_score_stable {s t : State roles} (path : Run n s) (full : score s = 3) :
    ¬ Step registry root s t := by
  intro move
  have limit := score_le t
  have more := raw_score_lt path move
  omega

end Yulang.GeneralMixedCompoundPointAcc307
