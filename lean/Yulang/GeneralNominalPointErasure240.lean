import Yulang.GeneralNominalPointKernel240
namespace Yulang.GeneralNominalPointErasure240
open GeneralNominalVersionedJournal232
open GeneralNominalPointKernel240
variable {roles : Roles.RoleDecls}

theorem administrative_old (action : Administrative (before : State roles) focus after) :
 GeneralNominalVersionedMixedKernel234.Administrative before focus after := by
 cases action with
 | enqueue linked absent => exact .enqueue _ linked absent
 | refresh context certificate source member unknown known => exact .refresh _ context certificate source member unknown known
 | equate first last one two equal novel => exact .equate _ first last one two equal novel
 | reobserve revision certificate improved preserved => exact .reobserve _ revision certificate improved

theorem at_old (action : At registry (before : State roles) focus after) :
 GeneralNominalVersionedMixedKernel234.At registry before focus after := by
 cases action with
 | administrative action => exact .administrative (administrative_old action)
 | refresh focus context certificate source member unknown known => exact .refresh focus context certificate source member unknown known
 | install effect enabled novel => exact .install effect enabled novel
 | merge first last one two equal novel => exact .merge first last one two equal novel

theorem step_old (step : Step registry root (before : State roles) after) :
 GeneralNominalVersionedMixedKernel234.Step registry root before after := by
 obtain ⟨focus,generated,action⟩ := step
 exact ⟨focus,generated,at_old action⟩

theorem steps_old (path : B4Target.Steps (Step registry root) (before : State roles) after) :
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) before after := by
 induction path with
 | refl => exact .refl
 | tail _ step ih => exact .tail ih (step_old step)

theorem old_stable (stable : GeneralNominalVersionedMixedKernel234.Stable registry (state : State roles) root) :
 Stable registry state root := fun focus generated after action => stable focus generated after (at_old action)

theorem old_acc (accessible : Acc (fun after before : State roles => GeneralNominalVersionedMixedKernel234.Step registry root before after) state) :
 Acc (fun after before => Step registry root before after) state :=
 Subrelation.accessible (fun step => step_old step) accessible
end Yulang.GeneralNominalPointErasure240
