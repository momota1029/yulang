import Yulang.GeneralRebaseDepthSchedule286

/-! All six permutations of the three single-purpose actions have a
corresponding actual raw trace. The general word lemma also applies from
any reachable prefix, so it does not rely on enumerating concrete states. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthScheduleWord286
open GeneralDictionaryOutputDepth252 (roles registry root initial)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Stable)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthSchedule286 (Event Move Done Open Halted)

inductive Word : State roles → List Event → State roles → Prop
  | empty (s) : Word s [] s
  | cons {s t u : State roles} {e : Event} {rest : List Event} :
      Move e s t → Word t rest u → Word s (e :: rest) u

theorem actual {s t : State roles} {order : List Event} (log : Word s order t) :
    ActualPath s t order.length := by
  induction log with
  | empty => exact .empty _
  | @cons a b c label rest move later ih =>
    have one : ActualPath a b 1 := .more (.empty _) move.actual
    simpa [Nat.add_comm] using GeneralRebaseDepthPathComplete285.concat one ih

theorem finished_not_open {s : State roles} {e : Event} (done : Done s e) : ¬ Open s e := by
  cases e <;> exact fun waiting => waiting done

theorem realizable {s : State roles} {n : Nat} (prefixPath : ActualPath initial s n)
    (order : List Event) (distinct : order.Nodup)
    (start : ∀ e ∈ order, Open s e) :
    ∃ finish, Word s order finish ∧
      ∀ e, Open finish e ↔ Open s e ∧ e ∉ order := by
  induction order generalizing s n with
  | nil => exact ⟨s,.empty _,by simp⟩
  | cons e rest ih =>
    obtain ⟨t,move⟩ := GeneralRebaseDepthSchedule286.realize prefixPath e (start e (List.mem_cons_self ..))
    have next : ActualPath initial t (n+1) := .more prefixPath move.actual
    have tailDistinct := (List.nodup_cons.mp distinct).2
    have tailOpen : ∀ x ∈ rest, Open t x := by
      intro x member
      have different : x ≠ e := by
        intro equal
        exact (List.nodup_cons.mp distinct).1 (equal ▸ member)
      exact (move.only x different).mpr (start x (List.mem_cons_of_mem _ member))
    obtain ⟨finish,log,remaining⟩ := ih next tailDistinct tailOpen
    refine ⟨finish,.cons move log,?_⟩
    intro x
    by_cases same : x = e
    · subst x
      constructor
      · intro after
        exact (finished_not_open move.done ((remaining e).mp after).1).elim
      · intro before
        exact (before.2 (List.mem_cons_self ..)).elim
    · rw [remaining x, move.only x same]
      simp only [List.mem_cons,same,false_or]

def base : List Event := [.install,.zero,.one]

theorem initially_open (e : Event) : Open initial e := by
  cases e with
  | install => exact GeneralRebaseDepthPhase286.exclusive GeneralRebaseDepthPhase286.start
  | zero => exact GeneralRebaseDepthPreSharp286.previously_unknown 0 (by decide)
  | one => exact GeneralRebaseDepthPreSharp286.previously_unknown 1 (by decide)

theorem permutation {order : List Event} (permuted : order.Perm base) :
    ∃ finish, Word initial order finish ∧ ActualPath initial finish 3 ∧
      Halted finish ∧ Stable registry finish root := by
  have distinct : order.Nodup := permuted.nodup_iff.mpr (by decide : base.Nodup)
  obtain ⟨finish,log,remaining⟩ := realizable (.empty initial) order distinct (fun e _ => initially_open e)
  have length : order.length = 3 := permuted.length_eq
  have ends (e : Event) (here : e ∈ base) : Done finish e := by
    have excluded : ¬ Open finish e := fun still =>
      ((remaining e).mp still).2 (permuted.mem_iff.mpr here)
    cases e <;> exact Classical.byContradiction excluded
  have stop := GeneralRebaseDepthSchedule286.halt_of_done
    (ends .install (by decide)) ⟨ends .zero (by decide),ends .one (by decide)⟩
  exact ⟨finish,log,length ▸ actual log,stop,(GeneralNominalVersionedMixedKernel234.closure stop).1⟩

end Yulang.GeneralRebaseDepthScheduleWord286
