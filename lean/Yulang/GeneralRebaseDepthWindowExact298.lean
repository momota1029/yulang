import Yulang.GeneralRebaseExplicitWindow298
import Yulang.GeneralRebasePackedNonleaf298
import Yulang.GeneralRebasePackedDepthDecision298

namespace Yulang.GeneralRebaseDepthWindowExact298
open GeneralDictionaryOutputDepth252 (roles root sourceRegistry registry initial)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseWeakProgress268 (Weak)
open GeneralRebaseWeakExit298 (View)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseExplicitWindow298.Actual (window evaluated sole_target concrete_real_target)

open GeneralRebaseOutputDepthSuccessor271 (owner output support)

/-- The concrete supplied window is complete for the displayed strict
targets of every real weak path, not merely for the shown route. -/
theorem exact_window (target : View [owner] [output]) :
    target ∈ evaluated ↔ ∃ u : State roles, Weak registry root [owner] [output] initial u ∧
      project [owner] [output] u = target := by
  constructor
  · intro found
    have targetEmpty : target.remaining = [] := by
      have loc := List.mem_map_of_mem (f := fun t : View [owner] [output] => t.remaining) found
      rw [sole_target] at loc
      exact List.mem_singleton.mp loc
    obtain ⟨u,w,actual⟩ := concrete_real_target
    exact ⟨u,w,GeneralRebaseStep258.state_ext _ _ (actual.trans targetEmpty.symm)⟩
  · rintro ⟨u,w,rfl⟩
    have targetEmpty := GeneralRebaseOutputDepthSuccessor271.every_weak u w
    have loc : ([] : List GeneralRebaseStep258.Fact) ∈ evaluated.map (·.remaining) :=
      sole_target.symm ▸ List.mem_cons_self ..
    obtain ⟨t,member,done⟩ := List.mem_map.mp loc
    have eq : t = project [owner] [output] u := GeneralRebaseStep258.state_ext _ _ (done.trans targetEmpty.symm)
    exact eq ▸ member

end Yulang.GeneralRebaseDepthWindowExact298
