import Yulang.GeneralNominalVersionedMixedHistory235
set_option backward.isDefEq.respectTransparency false
/-! The actual source-reachable versioned plan ledger has no duplicate plans.
This controls install steps only; a finite plan universe and all-step termination
are still separate obligations. -/
namespace Yulang.GeneralNominalVersionedMixedPlanLedger235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {before after state : State roles}

def Synced (state : State roles) : Prop := state.plans = state.effects.map Effect.plan

theorem lift (legacy : Legacy.State roles) : Synced (GeneralNominalVersionedJournal232.lift legacy) := rfl

theorem step_sync (action : Step registry root before after) (synced : Synced before) : Synced after := by
  obtain ⟨_,_,action⟩ := action
  cases action with
  | administrative action => cases action <;> exact synced
  | refresh => exact synced
  | merge => exact synced
  | install => change _ :: before.plans = _ :: before.effects.map Effect.plan; rw [synced]

theorem plan_committed (synced : Synced state)
    (history : GeneralNominalVersionedMixedHistory235.Recorded root state)
    (member : plan ∈ state.plans) : Committed state plan := by
  rw [synced] at member
  obtain ⟨effect,present,same⟩ := List.mem_map.mp member
  subst plan
  refine ⟨?_,(history effect present).2⟩
  intro model valid
  exact ⟨valid.2.1 effect.plan (synced ▸ List.mem_map.mpr ⟨effect,present,rfl⟩),
    (valid.2.2 effect present).2⟩

theorem novel_not_recorded (synced : Synced state)
    (history : GeneralNominalVersionedMixedHistory235.Recorded root state)
    (novel : ¬ Committed state plan) : plan ∉ state.plans :=
  fun member => novel (plan_committed synced history member)

def Invariant (root : Occurrence roles) (state : State roles) : Prop :=
  Synced state ∧ GeneralNominalVersionedMixedHistory235.Recorded root state ∧ state.plans.Nodup

theorem lift_invariant (legacy : Legacy.State roles) :
    Invariant root (GeneralNominalVersionedJournal232.lift legacy) :=
  ⟨lift legacy,GeneralNominalVersionedMixedHistory235.lift legacy,List.nodup_nil⟩

theorem step (action : Step registry root before after) (invariant : Invariant root before) : Invariant root after := by
  refine ⟨step_sync action invariant.1,GeneralNominalVersionedMixedHistory235.step action invariant.2.1,?_⟩
  obtain ⟨_,_,action⟩ := action
  cases action with
  | administrative action => cases action <;> exact invariant.2.2
  | refresh => exact invariant.2.2
  | merge => exact invariant.2.2
  | install effect enabled novel =>
    exact List.nodup_cons.mpr ⟨novel_not_recorded invariant.1 invariant.2.1 novel,invariant.2.2⟩

theorem steps (path : B4Target.Steps (Step registry root) before after)
    (invariant : Invariant root before) : Invariant root after := by
  induction path with
  | refl => exact invariant
  | tail _ action ih => exact step action ih

theorem reachable
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
    Invariant root state := by
  obtain ⟨first,⟨legacy,_,same⟩,path⟩ := path
  subst first
  exact steps path (lift_invariant legacy)

theorem reachable_plan_committed
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (member : plan ∈ state.plans) : Committed state plan :=
  plan_committed (reachable path).1 (reachable path).2.1 member

theorem reachable_nodup
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
    state.plans.Nodup := (reachable path).2.2

end Yulang.GeneralNominalVersionedMixedPlanLedger235
