import Yulang.GeneralNominalRebaseStore241
/-! A replacement table alone is not a progress condition. This negative test
keeps an unrestricted replacement relation separate from the proposed scheduler. -/
namespace Yulang.GeneralNominalRebaseNoop241
open GeneralNominalRebaseStore241

def Unrestricted (before after : State) : Prop :=
 ∃ owner ∈ before.owners, ∃ block, after = rebase before owner block

theorem current_rebase : rebase state owner (state.blocks owner) = state := by
 cases state
 simp only [rebase,replace_current]

theorem self_step (present : owner ∈ state.owners) : Unrestricted state state :=
 ⟨owner,present,state.blocks owner,(current_rebase).symm⟩

theorem no_acc (present : owner ∈ state.owners) :
 ¬ Acc (fun after before => Unrestricted before after) state := by
 intro accessible
 induction accessible with
 | intro current _ ih => exact ih current (self_step present) present
end Yulang.GeneralNominalRebaseNoop241
