import Yulang.GeneralMixedDiagnosticLocal304
import Yulang.GeneralDeferredLadderRequestFree303

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedDiagnosticRequestFree304
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMergedConflict232 (ClassEquations MergedOutputConflict)
open GeneralDeferredLadderResnapshot304 (HeadView)
open GeneralDeferredLadderRequestFree303 (classes_empty)
open GeneralMixedDiagnosticHead304 (boundary8 sharing_iff)
open GeneralMixedDiagnosticLocal304 (boundary7 local6_forward priority_iff)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {a b : State roles}

theorem empty_class (a : State roles) (focus : Occurrence roles) (m : Assignment)
    (empty : requests a.core focus = []) : ClassEquations a focus m := by
  have atAlias {other : Occurrence roles}
      (alias : GeneralNominalSaturationState.Alias a.core.erased.current focus.identity other.identity) :
      requests a.core other = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro output listed
    have found := (GeneralNominalCenteredHeadOutputs.same_class_requests alias).mpr listed
    rw [empty] at found
    cases found
  constructor
  · constructor
    · intro first member
      rw [empty] at member
      cases member
    · intro old _ alias
      exact (GeneralNominalVersionedEffects231.class_effects_iff ..).mp
        (classes_empty a.core old.plan.packet.site.occurrence (atAlias alias) old.plan m)
  · intro old _ alias
    exact classes_empty a.core old.plan.packet.site.occurrence (atAlias alias) old.plan m

/-- Unlike full model inhabitation, the empty focal request list is
sufficient to exclude this merged error even in an inconsistent journal. -/
theorem no_merged (a : State roles) (focus : Occurrence roles) (empty : requests a.core focus = []) :
    ¬ MergedOutputConflict a focus := by
  rintro ⟨_,_,_,_,⟨m,valid⟩,bad⟩
  exact bad ⟨m,valid,empty_class a focus m empty⟩

theorem local_without_slice (head : HeadView a b) (reg : Registry) (root : Occurrence roles)
    (empty : requests a.core root = []) (f : Frontier (Occurrence roles)) :
    B4TargetV8.Local (boundary8 roles) reg a root f ↔ B4TargetV8.Local (boundary8 roles) reg b root f := by
  have noneRight : requests b.core root = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro o listed
    have old := (GeneralDeferredLadderOperationalView304.requests_iff head.raw root o).mpr listed
    rw [empty] at old
    cases old
  have merged : MergedOutputConflict a root ↔ MergedOutputConflict b root :=
    ⟨fun h => False.elim (no_merged a root empty h),
      fun h => False.elim (no_merged b root noneRight h)⟩
  have old (v : Frontier (Occurrence roles)) :
      B4TargetV7.Local (boundary7 roles) reg a root v ↔ B4TargetV7.Local (boundary7 roles) reg b root v :=
    B4TargetV7.local_transport (fun _ => ⟨local6_forward head reg root,local6_forward head.symm reg root⟩)
      merged (priority_iff head reg root) v
  exact B4TargetV8.local_transport old (sharing_iff head reg root) (priority_iff head reg root) f

end Yulang.GeneralMixedDiagnosticRequestFree304
