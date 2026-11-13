import Yulang.GeneralDictionaryActualV5173
import Yulang.GeneralDictionaryFeedbackExecutor

/-! I-28: a noncomputable witness executor on the ground initial-source
restriction of Actual Step. Ground progress is proved, not a parameter. The
finite diagnostic resolver still has a pending fallback outside child-accessible
states; where-accessibility and canonical order remain unproved. This is not
an executable implementation or full B4 correctness. -/
namespace Yulang.GeneralDictionaryActualGroundExecutor173

open GeneralNominalActualBoundary GeneralNominalSupport
open GeneralDictionaryFeedbackExecutor (exists_halted)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open CommonRoleOutermostResolver
open B4TargetV5
open B4TargetV3 (Executor Local)

noncomputable def finalState (roles : Roles.RoleDecls)
    (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Tracked roles := by
  classical
  exact if domain : (groundBoundary roles).Checked registry ∧ Reachable (groundBoundary roles) registry root state then
    Classical.choose (exists_halted ((groundBoundary roles).Step registry root) state
      (ground_progress registry domain.1 state root domain.2))
  else state

theorem final_spec (roles : Roles.RoleDecls)
    (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (groundBoundary roles) registry root state) :
    B4Target.Steps ((groundBoundary roles).Step registry root) state (finalState roles registry state root) ∧
      ∀ next, ¬ (groundBoundary roles).Step registry root (finalState roles registry state root) next := by
  classical
  unfold finalState
  rw [dite_eq_left ⟨checked,reachable⟩]
  exact Classical.choose_spec (exists_halted ((groundBoundary roles).Step registry root) state
    (ground_progress registry checked state root reachable))

/-- This total extension is only a diagnostic claim when child accessibility
exists. The explicit fallback does not classify a non-accessible child relation. -/
noncomputable def diagnostic (roles : Roles.RoleDecls) (registry : Registry)
    (state : Tracked roles) (root : Occurrence roles) : Tree := by
  classical
  exact if exact : FrontierExact (frontiers roles registry state) then
    if accessible : Acc (Child (frontiers roles registry state).Local) root then
      resolve (frontiers roles registry state) exact root accessible
    else .pending
  else .pending

theorem diagnostic_eq_resolve (roles : Roles.RoleDecls) (registry : Registry)
    (state : Tracked roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry state))
    (accessible : Acc (Child (frontiers roles registry state).Local) root) :
    diagnostic roles registry state root = resolve (frontiers roles registry state) exact root accessible := by
  classical
  simp only [diagnostic,dite_eq_left exact,dite_eq_left accessible]

noncomputable def executor (roles : Roles.RoleDecls) :
    Executor (GeneralNominalActualBoundary.vocabulary roles) where
  run registry state root :=
    let final := finalState roles registry state root
    (final,diagnostic roles registry final root)

theorem execution (roles : Roles.RoleDecls) :
    ∀ r, (groundBoundary roles).Checked r → ∀ s d, Reachable (groundBoundary roles) r d s →
      B4Target.Steps ((groundBoundary roles).Step r d) s ((executor roles).run r s d).1 :=
  fun r checked s d reachable => (final_spec roles r checked s d reachable).1

theorem halted (roles : Roles.RoleDecls) :
    ∀ r, (groundBoundary roles).Checked r → ∀ s d, Reachable (groundBoundary roles) r d s →
      ∀ next, ¬ (groundBoundary roles).Step r d ((executor roles).run r s d).1 next :=
  fun r checked s d reachable => (final_spec roles r checked s d reachable).2

theorem treeExecution (roles : Roles.RoleDecls) :
    ∀ r (_checked : (groundBoundary roles).Checked r) s d, Reachable (groundBoundary roles) r d s →
      ∀ (exact : FrontierExact (frontiers roles r ((executor roles).run r s d).1))
      (accessible : Acc (Child (frontiers roles r ((executor roles).run r s d).1).Local) d),
      ((executor roles).run r s d).2 =
        resolve (frontiers roles r ((executor roles).run r s d).1) exact d accessible :=
  fun r _ _s d _ exact accessible => diagnostic_eq_resolve roles r _ d exact accessible

theorem final_reachable (roles : Roles.RoleDecls)
    (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (groundBoundary roles) registry root state) :
    Reachable (groundBoundary roles) registry root ((executor roles).run registry state root).1 :=
  reachable_steps _ reachable (execution roles registry checked state root reachable)

theorem final_stable (roles : Roles.RoleDecls)
    (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (groundBoundary roles) registry root state) :
    (groundBoundary roles).Stable registry ((executor roles).run registry state root).1 root ∧
      ∀ child, (groundBoundary roles).Generated registry ((executor roles).run registry state root).1 root child →
        (groundBoundary roles).Stable registry ((executor roles).run registry state root).1 child :=
  closure registry checked _ root (GeneralDictionaryActualV5173.ground_reachable
    (final_reachable roles registry checked state root reachable))
    (halted roles registry checked state root reachable)

theorem final_models (roles : Roles.RoleDecls)
    (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (groundBoundary roles) registry root state) :
    ∀ model, (groundBoundary roles).Models ((executor roles).run registry state root).1 model →
      (groundBoundary roles).Models state model :=
  B4SkeletonV5.steps_models (boundary roles) registry root (stepModels registry checked root)
    (GeneralDictionaryActualV5173.ground_reachable reachable) (execution roles registry checked state root reachable)

theorem saturationTotal (roles : Roles.RoleDecls) :
    B4TargetV5.SaturationTotal (groundBoundary roles) (executor roles) := by
  intro registry checked state root initial
  have reached := reachable_initial (groundBoundary roles) initial
  exact ⟨ground_progress registry checked state root reached,execution roles registry checked state root reached,
    (final_stable roles registry checked state root reached).1,
    (final_stable roles registry checked state root reached).2,
    final_models roles registry checked state root reached⟩

end Yulang.GeneralDictionaryActualGroundExecutor173
