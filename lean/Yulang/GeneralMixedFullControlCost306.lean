import Yulang.GeneralMixedFullControlFinish306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedFullControlCost306
open GeneralDictionaryOutputDepth252 (roles initial registry root)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthSchedule286 (Halted)
open GeneralRebaseDepthPathComplete285 (concat)
open GeneralMixedFullControlCode306 (Event Code code Action action_step)
open GeneralMixedFullControlStep306 (split)
open GeneralMixedFullControlTrace306 (RawRoute encode decode check)
open GeneralMixedFullControlFinish306 (terminal_exact)
open GeneralMixedFullControlScheduler306 (leastCost terminal exact_finishing_lengths)
open GeneralMixedFullControlMinimal306 (obligations)

theorem snoc {s t u : State roles} {e : Event} (trace : RawRoute s entries t) (edge : Action e t u) :
    RawRoute s (entries ++ [(e,code u)]) u := by
  induction trace with
  | done => exact .append edge (.done _)
  | append first _ ih => exact .append first (ih edge)

theorem from_path {s t : State roles} {before len : Nat} (prefixPath : ActualPath initial s before)
    (after : ActualPath s t len) :
    ∃ entries : List (Event × Code), RawRoute s entries t ∧ entries.length = len := by
  induction after with
  | empty => exact ⟨[],.done _,rfl⟩
  | more old move ih =>
    obtain ⟨entries,walk,size⟩ := ih
    obtain ⟨event,marked⟩ := (split (concat prefixPath old)).mp move
    exact ⟨entries ++ [(event,code _)],snoc walk marked,by simp [size]⟩

theorem to_path {s t : State roles} (given : RawRoute s trace t) :
    ActualPath s t trace.length := by
  induction given with
  | done => exact .empty _
  | append edge _ ih =>
    simpa only [List.length_cons,Nat.add_comm 1] using concat (.more (.empty _) (action_step edge)) ih

theorem finishing_lengths {s : State roles} {n : Nat} (prior : ActualPath initial s n) (length : Nat) :
    (∃ t, ActualPath s t length ∧ Halted t) ↔
      leastCost (code s) ≤ length ∧ length ≤ obligations (code s) := by
  rw [← exact_finishing_lengths (code s) length]
  constructor
  · rintro ⟨t,actual,stops⟩
    obtain ⟨entries,walk,size⟩ := from_path prior actual
    have chosen := (terminal_exact (concat prior actual)).mpr stops
    exact ⟨entries,chosen ▸ encode prior walk,size⟩
  · rintro ⟨entries,valid,len⟩
    obtain ⟨t,walk,atEnd⟩ := decode prior valid
    have actual := to_path walk
    exact ⟨t,len ▸ actual,(terminal_exact (concat prior actual)).mp atEnd⟩

end Yulang.GeneralMixedFullControlCost306
