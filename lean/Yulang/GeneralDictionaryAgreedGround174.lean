import Yulang.GeneralNominalActualAgreedBoundary
import Yulang.GeneralDictionaryActualGroundExecutor173

/-! Ground initial-source restriction of the policy-parametric agreed Local.
Actual Step is unchanged. The executor is a noncomputable witness, not a
compiler. No choice of provenance policy is asserted as language semantics.
Tree correctness still takes child accessibility as its explicit argument. -/
namespace Yulang.GeneralDictionaryAgreedGround174
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualAgreedLocal
open CommonRoleOutermostResolver B4TargetV5
open B4TargetV3 (Executor Local)
variable {roles : Roles.RoleDecls}

def boundary (defer : Bool) (gap : GapPredicate roles) : SourceBoundary (GeneralNominalActualBoundary.vocabulary roles) :=
  { GeneralNominalActualAgreedBoundary.boundary defer gap with
    Initial := (GeneralNominalActualBoundary.groundBoundary roles).Initial }

theorem reachable_old {defer : Bool} {gap : GapPredicate roles}
    (h : Reachable (boundary defer gap) registry root state) :
    Reachable (GeneralNominalActualBoundary.groundBoundary roles) registry root state := h

theorem reachable_agreed {defer : Bool} {gap : GapPredicate roles}
    (h : Reachable (boundary defer gap) registry root state) :
    Reachable (GeneralNominalActualAgreedBoundary.boundary defer gap) registry root state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := h
  exact ⟨_,⟨context,source,rfl⟩,path⟩

theorem progress (defer : Bool) (gap : GapPredicate roles)
    (registry : Registry) (checked : (boundary defer gap).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary defer gap) registry root state) :
    Acc (fun next current => (boundary defer gap).Step registry root current next) state :=
  GeneralNominalActualBoundary.ground_progress registry checked state root (reachable_old reachable)

noncomputable def diagnostic (defer : Bool) (gap : GapPredicate roles)
    (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Tree := by
  classical
  let f := GeneralNominalActualAgreedBoundary.frontiers defer gap registry state
  exact if exact : FrontierExact f then
    if accessible : Acc (Child f.Local) root then resolve f exact root accessible else .pending
  else .pending

theorem diagnostic_eq_resolve (defer : Bool) (gap : GapPredicate roles)
    (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (exact : FrontierExact (GeneralNominalActualAgreedBoundary.frontiers defer gap registry state))
    (accessible : Acc (Child (GeneralNominalActualAgreedBoundary.frontiers defer gap registry state).Local) root) :
    diagnostic defer gap registry state root =
      resolve (GeneralNominalActualAgreedBoundary.frontiers defer gap registry state) exact root accessible := by
  classical
  simp only [diagnostic, dite_eq_left exact, dite_eq_left accessible]

noncomputable def executor (defer : Bool) (gap : GapPredicate roles) :
    Executor (GeneralNominalActualBoundary.vocabulary roles) where
  run registry state root :=
    let final := GeneralDictionaryActualGroundExecutor173.finalState roles registry state root
    (final, diagnostic defer gap registry final root)

theorem execution (defer : Bool) (gap : GapPredicate roles)
    (registry : Registry) (checked : (boundary defer gap).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary defer gap) registry root state) :
    B4Target.Steps ((boundary defer gap).Step registry root) state
      ((executor defer gap).run registry state root).1 :=
  (GeneralDictionaryActualGroundExecutor173.final_spec roles registry checked state root (reachable_old reachable)).1

theorem halted (defer : Bool) (gap : GapPredicate roles)
    (registry : Registry) (checked : (boundary defer gap).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary defer gap) registry root state) :
    ∀ next, ¬ (boundary defer gap).Step registry root
      ((executor defer gap).run registry state root).1 next :=
  (GeneralDictionaryActualGroundExecutor173.final_spec roles registry checked state root (reachable_old reachable)).2

theorem treeExecution (defer : Bool) (gap : GapPredicate roles)
    (registry : Registry) (_checked : (boundary defer gap).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary defer gap) registry root state)
    (exact : FrontierExact (GeneralNominalActualAgreedBoundary.frontiers defer gap registry ((executor defer gap).run registry state root).1))
    (accessible : Acc (Child (GeneralNominalActualAgreedBoundary.frontiers defer gap registry ((executor defer gap).run registry state root).1).Local) root) :
    ((executor defer gap).run registry state root).2 =
      resolve (GeneralNominalActualAgreedBoundary.frontiers defer gap registry ((executor defer gap).run registry state root).1) exact root accessible :=
  diagnostic_eq_resolve defer gap registry _ root exact accessible

theorem saturationTotal (defer : Bool) (gap : GapPredicate roles) :
    B4TargetV5.SaturationTotal (boundary defer gap) (executor defer gap) := by
  intro registry checked state root initial
  exact GeneralDictionaryActualGroundExecutor173.saturationTotal roles registry checked state root initial

theorem initialReorders (defer : Bool) (gap : GapPredicate roles)
    (registry other : Registry) (order : (boundary defer gap).Reorders registry other)
    (state : Tracked roles) (root : Occurrence roles)
    (given : (boundary defer gap).Initial registry root state) :
    (boundary defer gap).Initial other root state := by
  obtain ⟨context,labels,source,point,ground,same⟩ := given
  exact ⟨context,labels,GeneralDictionaryInitialSource.source_reorders registry other order context root source,
    point,ground,same⟩

end Yulang.GeneralDictionaryAgreedGround174
