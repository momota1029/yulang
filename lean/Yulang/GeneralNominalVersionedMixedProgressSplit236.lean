import Yulang.GeneralNominalVersionedMixedAdministrativeOrder236
import Yulang.GeneralNominalVersionedMixedPlanLedger235
set_option backward.isDefEq.respectTransparency false
/-! The actual source trace has no unrecorded enqueue. Every full step is
administrative or adds one plan; bounded-plan segments have no livelock. -/
namespace Yulang.GeneralNominalVersionedMixedProgressSplit236
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedMixedAdministrative236
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
 {before after : State roles}
abbrev Reachable (registry : Registry) (root : Occurrence roles) (state : State roles) :=
 B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state

theorem reachable_step (path : Reachable registry root before)
 (action : Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root before after) :
 Reachable registry root after := by
 obtain ⟨start,initial,trace⟩ := path
 exact ⟨start,initial,.tail trace action⟩

theorem split (path : Reachable registry root before)
 (action : Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root before after) :
 Update before after ∨ ∃ effect,
   Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) before effect ∧
   ¬ Committed before effect.plan ∧ after = GeneralNominalVersionedInstall232.install before effect := by
 obtain ⟨focus,generated,action⟩ := action
 cases action with
 | administrative action =>
   cases action with
   | enqueue linked absent =>
     obtain ⟨raw,recorded,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
       (GeneralNominalVersionedMixedTrace235.reachable path).1 generated
     exact False.elim (absent raw recorded same)
   | refresh context certificate source member unknown known =>
     exact Or.inl (.refresh context certificate source member unknown known)
   | equate first last one two equal novel => exact Or.inl (.equate first last one two equal novel)
   | reobserve revision certificate improved => exact Or.inl (.reobserve revision certificate improved)
 | refresh focus context certificate source member unknown known =>
   exact Or.inl (.refresh context certificate source member unknown known)
 | merge first last one two equal novel => exact Or.inl (.merge first last one two equal novel)
 | install effect enabled novel => exact Or.inr ⟨effect,enabled,novel,rfl⟩

theorem administrative_plans (update : Update before after) : after.plans = before.plans := by
 cases update <;> rfl

theorem same_length_administrative (path : Reachable registry root before)
 (action : Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root before after)
 (same : after.plans.length = before.plans.length) : Update before after := by
 rcases split path action with update | ⟨effect,_,_,rfl⟩
 · exact update
 · change (_ :: before.plans).length = before.plans.length at same
   simp only [List.length_cons] at same
   omega

def QuietStep (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
 Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root before after ∧
 after.plans.length = before.plans.length

theorem quiet_accessible (path : Reachable registry root before) :
 Acc (fun next current => QuietStep registry root current next) before := by
 have admin := GeneralNominalVersionedMixedAdministrativeOrder236.accessible before
 induction admin with
 | intro current below ih =>
   refine Acc.intro current ?_
   intro next action
   exact ih next (same_length_administrative path action.1 action.2) (reachable_step path action.1)

/-- This rank is an explicit missing obligation, not an asserted construction. -/
structure InstallationDescent (registry : Registry) (root : Occurrence roles) where
 rank : State roles → Nat
 administrative : ∀ before after, Reachable registry root before → Update before after → rank after ≤ rank before
 installation : ∀ before, Reachable registry root before → ∀ effect,
   Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) before effect →
   ¬ Committed before effect.plan → rank (GeneralNominalVersionedInstall232.install before effect) < rank before

theorem accessible_of_installation_descent (descent : InstallationDescent registry root)
 (path : Reachable registry root before) :
 Acc (fun next current => Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root current next) before := by
 have all : ∀ n current, descent.rank current ≤ n → Reachable registry root current →
   Acc (fun next current => Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root current next) current := by
   intro n
   induction n using Nat.strongRecOn with
   | ind n lower =>
     intro current
     have admin := GeneralNominalVersionedMixedAdministrativeOrder236.accessible current
     induction admin with
     | intro current below ih =>
       intro bound path
       refine Acc.intro current ?_
       intro next action
       rcases split path action with update | ⟨effect,enabled,novel,rfl⟩
       · exact ih next update (Nat.le_trans (descent.administrative _ _ path update) bound)
           (reachable_step path action)
       · exact lower _ (Nat.lt_of_lt_of_le (descent.installation _ path effect enabled novel) bound)
           _ (Nat.le_refl _) (reachable_step path action)
 exact all (descent.rank before) before (Nat.le_refl _) path

end Yulang.GeneralNominalVersionedMixedProgressSplit236
