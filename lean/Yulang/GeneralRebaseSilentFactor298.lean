import Yulang.GeneralRebaseWeakWindow298
import Yulang.GeneralRebaseQuietBound277

namespace Yulang.GeneralRebaseSilentFactor298
open B4Target (Steps)

def Silent (R : A → A → Prop) (rank : A → Nat) (a b : A) := R a b ∧ rank b = rank a

theorem path_extend {R : A → A → Prop} {start middle after : A}
    (path : Steps R start middle) (edge : R middle after) : Steps R start after :=
  .tail path edge

theorem restrict_acc {R S : A → A → Prop} (restrict : ∀ {a b}, R a b → S a b)
    {s : A} (acc : Acc S s) : Acc R s := by
  induction acc with
  | intro a below ih => exact ⟨a,fun b edge => ih b (restrict edge)⟩

/-- Strict rank progress can occur only finitely often. What remains to
establish is silent accessibility at every reached state, not just at
the starting representative. -/
theorem accessible_factor (R : A → A → Prop) (rank : A → Nat)
    (mono : ∀ a b, R a b → rank b ≤ rank a) (s : A) :
    Acc (fun next current => R current next) s ↔
    ∀ a, Steps R s a → Acc (fun next current => Silent R rank current next) a := by
  constructor
  · intro acc a path
    have descend : Acc (fun next current => R current next) a := by
      induction path with
      | refl => exact acc
      | tail _ edge ih => exact ih.inv edge
    exact restrict_acc (fun h => h.1) descend
  · intro safe
    have all : ∀ n a, rank a ≤ n → Steps R s a → Acc (fun next current => R current next) a := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n smaller =>
        intro a bounded origin
        have quiet := safe a origin
        induction quiet with
        | intro now branch ih =>
          refine Acc.intro now ?_
          intro after edge
          have le := mono now after edge
          by_cases same : rank after = rank now
          · exact ih after ⟨edge,same⟩ (by omega) (.tail origin edge)
          · exact smaller (rank after) (by omega) after (Nat.le_refl _) (.tail origin edge)
    exact all (rank s) s (Nat.le_refl _) .refl

namespace Source
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralSourceState (Output)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedInstall232 (install)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseWeakProgress268 (Stutter)
open GeneralRebaseLiveProjection264 (project)

def rank (owners : List Nat) (pool : List Output) (s : State roles) := (project owners pool s).remaining.length

theorem monotone (r : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
    (a b : State roles) (h : (Boundary roles).Step r root a b) : rank owners pool b ≤ rank owners pool a := by
  by_cases same : project owners pool b = project owners pool a
  · unfold rank; rw [same]; exact Nat.le_refl _
  · exact Nat.le_of_lt (GeneralRebaseSourceProjection264.strict_decrease owners pool h same)

theorem silent_iff (r : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
    (a b : State roles) :
    Silent ((Boundary roles).Step r root) (rank owners pool) a b ↔ Stutter (Encoded r) root owners pool a b := by
  constructor
  · rintro ⟨h,eq⟩
    refine ⟨h,?_⟩
    apply Classical.byContradiction
    intro different
    exact (Nat.ne_of_lt (GeneralRebaseSourceProjection264.strict_decrease owners pool h different)) eq
  · exact fun h => ⟨h.1,congrArg GeneralRebaseStep258.State.remaining h.2 |> congrArg List.length⟩

theorem necessary_and_sufficient (r : Registry) (root : Occurrence roles)
    (owners : List Nat) (pool : List Output) (s : State roles) :
    Acc (fun next current => (Boundary roles).Step r root current next) s ↔
    ∀ a, Steps ((Boundary roles).Step r root) s a →
      Acc (fun next current => Stutter (Encoded r) root owners pool current next) a := by
  have fact := accessible_factor (fun a b : State roles => (Boundary roles).Step r root a b)
    (rank owners pool) (monotone r root owners pool) s
  constructor
  · intro acc a seen
    exact restrict_acc (fun h => (silent_iff r root owners pool _ _).mpr h) (fact.mp acc a seen)
  · intro all
    apply fact.mpr
    intro a seen
    exact restrict_acc (fun h => (silent_iff r root owners pool _ _).mp h) (all a seen)

def StrictInstalls (r : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output) : Prop :=
  ∀ s, B4TargetV8.Reachable (Boundary roles) r root s → ∀ e : Effect roles,
    Installable (Encoded r) s e → ¬ Committed s e.plan →
      project owners pool (install s e) ≠ project owners pool s

theorem stutter_no_install {r : Registry} {root : Occurrence roles} {a b : State roles}
    (seen : B4TargetV8.Reachable (Boundary roles) r root a) (owners : List Nat) (pool : List Output)
    (strict : StrictInstalls r root owners pool)
    (quiet : Stutter (Encoded r) root owners pool a b) :
    GeneralNominalVersionedMixedProgressSplit236.QuietStep r root a b := by
  have split := GeneralNominalVersionedMixedProgressSplit236.split seen quiet.1
  rcases split with admin | ⟨e,enabled,novel,rfl⟩
  · refine ⟨quiet.1,?_⟩
    rw [GeneralNominalVersionedMixedProgressSplit236.administrative_plans admin]
  · exact False.elim (strict a seen e enabled novel quiet.2)

theorem counted_quiet {r : Registry} {root : Occurrence roles} {s t : State roles} {n : Nat}
    (seen : B4TargetV8.Reachable (Boundary roles) r root s) (owners : List Nat) (pool : List Output)
    (strict : StrictInstalls r root owners pool)
    (path : GeneralRebaseQuietBound277.Counted (Stutter (Encoded r) root owners pool) s n t) :
    n ≤ GeneralRebaseQuietBasis277.budget s := by
  have transfer : GeneralRebaseQuietBound277.Counted
      (GeneralNominalVersionedMixedProgressSplit236.QuietStep r root) s n t ∧
      B4TargetV8.Reachable (Boundary roles) r root t := by
    induction path with
    | nil => exact ⟨.nil,seen⟩
    | tail _ edge ih =>
      exact ⟨.tail ih.1 (stutter_no_install ih.2 owners pool strict edge),
        GeneralNominalVersionedMixedProgressSplit236.reachable_step ih.2 edge.1⟩
  exact GeneralRebaseQuietBound277.quiet_length seen transfer.1

theorem accessible_if_visible_install {r : Registry} {root : Occurrence roles} {s : State roles}
    (seen : B4TargetV8.Reachable (Boundary roles) r root s) (owners : List Nat) (pool : List Output)
    (strict : StrictInstalls r root owners pool) :
    Acc (fun next current => (Boundary roles).Step r root current next) s := by
  apply (necessary_and_sufficient r root owners pool s).mpr
  intro a trace
  have reached := GeneralRebaseRevisitedTrace298.reachable_tail seen trace
  have quiet := GeneralNominalVersionedMixedProgressSplit236.quiet_accessible reached
  induction quiet with
  | intro now _ ih =>
    refine Acc.intro now ?_
    intro next edge
    exact ih next (stutter_no_install reached owners pool strict edge)
      (.tail trace edge.1) (GeneralNominalVersionedMixedProgressSplit236.reachable_step reached edge.1)

end Source
end Yulang.GeneralRebaseSilentFactor298
