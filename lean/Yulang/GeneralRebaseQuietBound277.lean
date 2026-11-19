import Yulang.GeneralRebaseQuietBasis277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseQuietBound277
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedAdministrative236 (Update Fact Holds monotone sites)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable QuietStep reachable_step same_length_administrative)
open GeneralRebaseMixedOwnedTrace277 (adapter_reachable raw source_extend)
open GeneralRebaseQuietBasis277 (sourceNames centerNames basis budget basis_count advances source_administrative)
open GeneralNominalState (sources)
open GeneralNominalFiniteProgress (remaining remaining_decreases)
variable {roles : Roles.RoleDecls}

inductive Counted {α : Type} (r : α → α → Prop) : α → Nat → α → Prop
  | nil : Counted r state 0 state
  | tail : Counted r start n before → r before after → Counted r start (n+1) after

theorem append {α : Type} {r : α → α → Prop} {start middle after : α}
    (one : Counted r start n middle) (two : Counted r middle k after) :
    Counted r start (n+k) after := by
  induction two with
  | nil => exact one
  | tail _ step ih => exact .tail ih step

theorem remaining_le {α β : Type} (holds : α → β → Prop) (basis : List β) (s : α) :
    remaining holds basis s ≤ basis.length := by
  classical
  induction basis with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    change (if holds s head then remaining holds tail s else remaining holds tail s + 1) ≤ tail.length + 1
    by_cases h : holds s head <;> simp only [h,ite_true,ite_false] <;> omega

theorem admin_no_grow {a b : State roles} (move : Update a b) :
    sources (raw a) ⊆ sources (raw b) := by
  cases move with
  | refresh context cert => exact GeneralNominalRefinements.sources cert.refines
  | reobserve => exact fun _ member => member
  | equate => exact source_extend _ _ _
  | merge => exact source_extend _ _ _

theorem admin_same_sources {a b : State roles} (okay : GeneralRebaseMixedOwnedTrace277.Invariant a)
    (move : Update a b) (id : Nat) :
    id ∈ sources (raw a) ↔ id ∈ sources (raw b) :=
  ⟨fun h => admin_no_grow move h,fun h => source_administrative okay move h⟩

theorem quiet_progress {start after : State roles} {registry : Registry} {root : Occurrence roles}
    (initial : Reachable registry root start)
    (walk : Counted (QuietStep registry root) start count after) :
    Reachable registry root after ∧ after.core.sites = start.core.sites ∧
    (∀ id, id ∈ sources (raw after) ↔ id ∈ sources (raw start)) ∧
    count + remaining Holds (basis start) after ≤ remaining Holds (basis start) start := by
  induction walk with
  | nil => exact ⟨initial,rfl,fun _ => Iff.rfl,by simp⟩
  | @tail n before after path edge ih =>
    obtain ⟨reached,same,old,bound⟩ := ih
    have update := same_length_administrative reached edge.1 edge.2
    have owned := adapter_reachable reached
    obtain ⟨fact,listed,missing,new⟩ := advances same (fun id seen => (old id).mp seen) update
    have less := remaining_decreases Holds (basis start) (monotone update) listed missing new
    exact ⟨reachable_step reached edge.1,(sites update).trans same,
      fun id => (admin_same_sources owned update id).symm.trans (old id),by omega⟩

/-- A quantitative bound on real installation-free paths, not just Acc.
The quadratic terms count ordered source equations and occurrence aliases;
the two linear terms count head-known and point-observation facts. -/
theorem quiet_length {start after : State roles} {registry : Registry} {root : Occurrence roles}
    (initial : Reachable registry root start)
    (walk : Counted (QuietStep registry root) start count after) : count ≤ budget start := by
  have descent := (quiet_progress initial walk).2.2.2
  have remainingBound := remaining_le Holds (basis start) start
  rw [basis_count] at remainingBound
  omega

end Yulang.GeneralRebaseQuietBound277
