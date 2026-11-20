import Yulang.GeneralRebaseDepthTraceCost286

/-! The rank is an exact worst-case count of remaining raw steps at every
reachable prefix of the fixture, not just an upper bound at initialization. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthBudgetExact286
open GeneralDictionaryOutputDepth252 (roles root registry initial)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthSchedule286 (Event Open Done Halted)
open GeneralRebaseDepthScheduleWord286 (Word base)
open GeneralRebaseDepthFullRank286 (rank weight)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralNominalState (Known)

noncomputable def outstanding (s : State roles) : List Event := by
  classical exact base.filter (fun e => decide (Open s e))

theorem membership (s : State roles) (e : Event) : e ∈ outstanding s ↔ Open s e := by
  classical
  unfold outstanding
  rw [List.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun h => ⟨by cases e <;> decide,h⟩⟩

theorem distinct (s : State roles) : (outstanding s).Nodup := by
  classical
  exact (by decide : base.Nodup).filter _

theorem length {s : State roles} (covered : GeneralRebaseDepthPhase286.Covered s) :
    (outstanding s).length = rank s := by
  classical
  have installedCost : (if Open s .install then 1 else 0) = weight s := by
    rcases covered with pre|post
    · have enabled : Open s .install := GeneralRebaseDepthPhase286.exclusive pre
      rw [GeneralRebaseDepthFullRank286.weight_pre pre,ite_eq_left enabled]
    · have disabled : ¬ Open s .install := fun waiting => waiting post
      rw [GeneralRebaseDepthFullRank286.weight_post post,ite_eq_right disabled]
  unfold outstanding base
  rw [List.filter_cons,List.filter_cons,List.filter_cons,List.filter_nil]
  have help : ∀ (P : Prop) [Decidable P], ∀ e : Event, ∀ rest : List Event,
      (if decide P then e :: rest else rest).length = (if P then 1 else 0) + rest.length := by
    intro P _ e rest
    by_cases yes : P <;> simp [yes,Nat.add_comm]
  rw [help,help,help,installedCost]
  simp only [Open,GeneralRebaseDepthFullRank286.rank,GeneralRebaseDepthPathRank285.rank,
    GeneralRebaseDepthPathRank285.pending]
  by_cases z : Known (snapshot s) 0 <;> by_cases o : Known (snapshot s) 1 <;> simp [z,o]

theorem upper_from_prefix {s t : State roles} {n k : Nat} (prefixPath : ActualPath initial s n)
    (tail : ActualPath s t k) : k ≤ rank s := by
  have c := GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) prefixPath
  have bound := (GeneralRebaseDepthFullRank286.all_paths c tail).2
  omega

theorem attained_from_prefix {s : State roles} {n : Nat} (path : ActualPath initial s n) :
    ∃ finish, Word s (outstanding s) finish ∧ ActualPath s finish (rank s) ∧ Halted finish := by
  have covered := GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) path
  obtain ⟨finish,order,after⟩ := GeneralRebaseDepthScheduleWord286.realizable path (outstanding s)
    (distinct s) (fun e member => (membership s e).mp member)
  have all (e : Event) : Done finish e := by
    have rejected : ¬ Open finish e := by
      intro openAfter
      have still := (after e).mp openAfter
      exact still.2 ((membership s e).mpr still.1)
    cases e <;> exact Classical.byContradiction rejected
  refine ⟨finish,order,length covered ▸ GeneralRebaseDepthScheduleWord286.actual order,?_⟩
  exact GeneralRebaseDepthSchedule286.halt_of_done (all .install) ⟨all .zero,all .one⟩

end Yulang.GeneralRebaseDepthBudgetExact286
