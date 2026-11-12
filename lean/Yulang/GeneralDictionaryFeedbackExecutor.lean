import Yulang.GeneralDictionaryCanonicalLocalOrder

/-! A noncomputable driver for the actual feedback Step, conditional on precisely
the V5 progress field. Step accessibility constructs a reachable halted state.
The tree reader uses independent child accessibility when it exists; its fallback
does not claim to establish that separate V5 obligation. -/
namespace Yulang.GeneralDictionaryFeedbackExecutor

open GeneralDictionaryReachableBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open CommonRoleOutermostResolver
open B4TargetV5
open B4TargetV3 (Executor Local)

def Progress (roles : Roles.RoleDecls) : Prop :=
  ∀ r, (boundary roles).Checked r → ∀ s d, Reachable (boundary roles) r d s →
    Acc (fun next current => (boundary roles).Step r d current next) s

theorem trace_trans {α : Type u} {step : α → α → Prop} {first middle last : α}
    (one : B4Target.Steps step first middle) (two : B4Target.Steps step middle last) :
    B4Target.Steps step first last := by
  induction two with
  | refl => exact one
  | tail _ update ih => exact .tail ih update

theorem exists_halted {α : Type u} (step : α → α → Prop) (state : α)
    (accessible : Acc (fun next current => step current next) state) :
    ∃ final, B4Target.Steps step state final ∧ ∀ next, ¬ step final next := by
  classical
  induction accessible with
  | intro state below ih =>
    by_cases advance : ∃ next, step state next
    · obtain ⟨next,update⟩ := advance
      obtain ⟨final,path,halted⟩ := ih next update
      exact ⟨final,trace_trans (.tail .refl update) path,halted⟩
    · exact ⟨state,.refl,fun next update => advance ⟨next,update⟩⟩

noncomputable def finalState (roles : Roles.RoleDecls) (progress : Progress roles)
    (registry : Registry) (state : State roles) (root : Occurrence roles) : State roles := by
  classical
  exact if domain : (boundary roles).Checked registry ∧ Reachable (boundary roles) registry root state then
    Classical.choose (exists_halted ((boundary roles).Step registry root) state
      (progress registry domain.1 state root domain.2))
  else state

theorem final_spec (roles : Roles.RoleDecls) (progress : Progress roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state) :
    B4Target.Steps ((boundary roles).Step registry root) state (finalState roles progress registry state root) ∧
      ∀ next, ¬ (boundary roles).Step registry root (finalState roles progress registry state root) next := by
  classical
  unfold finalState
  rw [dite_eq_left ⟨checked,reachable⟩]
  exact Classical.choose_spec (exists_halted ((boundary roles).Step registry root) state
    (progress registry checked state root reachable))

/-- This total extension is only a diagnostic claim when child accessibility
exists. The explicit fallback does not classify a non-accessible child relation. -/
noncomputable def diagnostic (roles : Roles.RoleDecls) (registry : Registry)
    (state : State roles) (root : Occurrence roles) : Tree := by
  classical
  exact if exact : FrontierExact (frontiers roles registry state) then
    if accessible : Acc (Child (frontiers roles registry state).Local) root then
      resolve (frontiers roles registry state) exact root accessible
    else .pending
  else .pending

theorem diagnostic_eq_resolve (roles : Roles.RoleDecls) (registry : Registry)
    (state : State roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry state))
    (accessible : Acc (Child (frontiers roles registry state).Local) root) :
    diagnostic roles registry state root = resolve (frontiers roles registry state) exact root accessible := by
  classical
  simp only [diagnostic,dite_eq_left exact,dite_eq_left accessible]

noncomputable def executor (roles : Roles.RoleDecls) (progress : Progress roles) :
    Executor (GeneralNominalFeedbackBoundary.vocabulary roles) where
  run registry state root :=
    let final := finalState roles progress registry state root
    (final,diagnostic roles registry final root)

theorem execution (roles : Roles.RoleDecls) (progress : Progress roles) :
    ∀ r, (boundary roles).Checked r → ∀ s d, Reachable (boundary roles) r d s →
      B4Target.Steps ((boundary roles).Step r d) s ((executor roles progress).run r s d).1 :=
  fun r checked s d reachable => (final_spec roles progress r checked s d reachable).1

theorem halted (roles : Roles.RoleDecls) (progress : Progress roles) :
    ∀ r, (boundary roles).Checked r → ∀ s d, Reachable (boundary roles) r d s →
      ∀ next, ¬ (boundary roles).Step r d ((executor roles progress).run r s d).1 next :=
  fun r checked s d reachable => (final_spec roles progress r checked s d reachable).2

theorem treeExecution (roles : Roles.RoleDecls) (progress : Progress roles) :
    ∀ r (_checked : (boundary roles).Checked r) s d, Reachable (boundary roles) r d s →
      ∀ (exact : FrontierExact (frontiers roles r ((executor roles progress).run r s d).1))
      (accessible : Acc (Child (frontiers roles r ((executor roles progress).run r s d).1).Local) d),
      ((executor roles progress).run r s d).2 =
        resolve (frontiers roles r ((executor roles progress).run r s d).1) exact d accessible :=
  fun r _ _s d _ exact accessible => diagnostic_eq_resolve roles r _ d exact accessible

theorem final_reachable (roles : Roles.RoleDecls) (progress : Progress roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state) :
    Reachable (boundary roles) registry root ((executor roles progress).run registry state root).1 :=
  reachable_steps _ reachable (execution roles progress registry checked state root reachable)

theorem final_stable (roles : Roles.RoleDecls) (progress : Progress roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state) :
    (boundary roles).Stable registry ((executor roles progress).run registry state root).1 root ∧
      ∀ child, (boundary roles).Generated registry ((executor roles progress).run registry state root).1 root child →
        (boundary roles).Stable registry ((executor roles progress).run registry state root).1 child :=
  closure registry checked _ root (final_reachable roles progress registry checked state root reachable)
    (halted roles progress registry checked state root reachable)

theorem final_models (roles : Roles.RoleDecls) (progress : Progress roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state) :
    ∀ model, (boundary roles).Models ((executor roles progress).run registry state root).1 model →
      (boundary roles).Models state model :=
  GeneralNominalFeedbackSteps.steps_models (execution roles progress registry checked state root reachable)

theorem saturationTotal (roles : Roles.RoleDecls) (progress : Progress roles) :
    B4TargetV5.SaturationTotal (boundary roles) (executor roles progress) := by
  intro registry checked state root initial
  have reached := reachable_initial (boundary roles) initial
  exact ⟨progress registry checked state root reached,execution roles progress registry checked state root reached,
    (final_stable roles progress registry checked state root reached).1,
    (final_stable roles progress registry checked state root reached).2,
    final_models roles progress registry checked state root reached⟩

end Yulang.GeneralDictionaryFeedbackExecutor
