import Yulang.GeneralDictionaryDefaultKernel208
import Yulang.GeneralNominalCenteredHeadMatStepTrustedGrowth

namespace Yulang.GeneralDictionaryDefaultGrowth208
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadMatStepTrustedGrowth
variable {roles : Roles.RoleDecls} {before after : State roles}

theorem administrative (action : GeneralDictionaryDefaultKernel208.Administrative before focus after) : Growth before after := by
  cases action with
  | enqueue linked absent =>
      exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => List.mem_append_left _ h,
        fun _ h => h,fun _ h => h,fun _ h => h⟩
  | refresh context certificate source member unknown known =>
      exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
        fun _ h => h,fun _ h => h,fun _ h => certificate.refines.ordinary _ h⟩
  | equate first last one two equal novel =>
      exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
        fun _ h => h,fun _ h => h,fun _ h => List.mem_append_left _ h⟩
  | reobserve revision certificate improved =>
      exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
        fun _ h => h,fun _ h => h,fun _ h => h⟩

theorem at_growth (action : GeneralDictionaryDefaultKernel208.At registry before focus after) : Growth before after := by
  cases action with
  | administrative action => exact administrative action
  | refresh focus context certificate source member unknown known =>
      exact administrative (.refresh focus context certificate source member unknown known)
  | install effect enabled novel =>
      refine ⟨rfl,rfl,fun _ h => List.mem_append_left _ h,fun _ h => List.mem_cons_of_mem _ h,
        fun _ h => List.mem_cons_of_mem _ h,fun _ h => List.mem_append_left _ h,
        fun _ h => List.mem_cons_of_mem _ h,fun _ h => h,?_⟩
      have context := effect.frame.context_eq.trans (congrArg (fun state => state.erased.current.context) enabled.snapshot_eq)
      intro atom member
      have old : atom ∈ effect.plan.packet.context.state.ordinary := context.symm ▸ member
      exact List.mem_append_left _ (List.mem_append_left _ old)
  | merge first last one two same novel =>
      exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
        fun _ h => h,fun _ h => List.mem_cons_of_mem _ h,fun _ h => List.mem_append_left _ h⟩

theorem step (action : GeneralDictionaryDefaultKernel208.Step registry root before after) : Growth before after :=
  at_growth action.choose_spec.2

end Yulang.GeneralDictionaryDefaultGrowth208
