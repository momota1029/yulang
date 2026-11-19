import Yulang.GeneralRebaseBoundedInstallAcc277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseFiniteCodeAcc277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split reachable_step administrative_plans)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralRebaseQuietBound277 (Counted)
open GeneralRebaseMixedCounts277 (Actual)
variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}

structure Certificate (r : Registry) (root : Occurrence roles) (Key : Type) where
  code : Plan roles → Key
  inventory : List Key
  contains : ∀ s, Reachable r root s → ∀ p ∈ s.plans, code p ∈ inventory
  absorbs : ∀ s, Reachable r root s → ∀ old ∈ s.plans, ∀ e : Effect roles,
    Installable (registry r) s e → code e.plan = code old → Committed s e.plan

theorem extend {Key : Type} (cert : Certificate r root Key) {a b : State roles}
    (formed : Reachable r root a) (action : Actual r root a b)
    (known : (a.plans.map cert.code).Nodup) : (b.plans.map cert.code).Nodup := by
  rcases split formed action with update | ⟨e,enabled,novel,rfl⟩
  · rw [administrative_plans update]
    exact known
  · change (cert.code e.plan :: a.plans.map cert.code).Nodup
    apply List.nodup_cons.mpr
    refine ⟨?_,known⟩
    intro duplicate
    obtain ⟨old,stored,same⟩ := List.mem_map.mp duplicate
    exact novel (cert.absorbs a formed old stored e enabled same.symm)

theorem distinct {Key : Type} (cert : Certificate r root Key) {s : State roles}
    (formed : Reachable r root s) : (s.plans.map cert.code).Nodup := by
  obtain ⟨start,initial,path⟩ := formed
  have first : Reachable r root start := ⟨start,initial,.refl⟩
  have unique : (start.plans.map cert.code).Nodup := by
    obtain ⟨legacy,_,rfl⟩ := initial
    exact List.nodup_nil
  have hold : ∀ t, B4Target.Steps (Actual r root) start t →
      Reachable r root t ∧ (t.plans.map cert.code).Nodup := by
    intro t trail
    induction trail with
    | refl => exact ⟨first,unique⟩
    | tail _ action ih => exact ⟨reachable_step ih.1 action,extend cert ih.1 action ih.2⟩
  exact (hold s path).2

theorem installation_budget {Key : Type} (cert : Certificate r root Key) {s : State roles}
    (formed : Reachable r root s) : s.plans.length ≤ cert.inventory.length := by
  rw [← List.length_map cert.code]
  apply (distinct cert formed).length_le_of_subset
  intro key present
  obtain ⟨p,member,rfl⟩ := List.mem_map.mp present
  exact cert.contains s formed p member

theorem reached_after_count {a b : State roles} (formed : Reachable r root a)
    (walk : Counted (Actual r root) a n b) : Reachable r root b := by
  induction walk with
  | nil => exact formed
  | tail _ action ih => exact reachable_step ih action

/-- A finite key inventory plus semantic absorption of repeated keys gives
full accessibility; equality of raw plans or journals is not required. -/
theorem accessible {Key : Type} (cert : Certificate r root Key) {s : State roles}
    (formed : Reachable r root s) : Acc (fun after before => Actual r root before after) s := by
  apply GeneralRebaseBoundedInstallAcc277.adapter_accessible formed cert.inventory.length
  intro n final trace
  have bound := installation_budget cert (reached_after_count formed trace)
  omega

end Yulang.GeneralRebaseFiniteCodeAcc277
