import Yulang.GeneralMixedControlAtoms306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedCheckedPromotion306
open GeneralNominalState (Known)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedObservations233 (Justified CacheSound Refresh)
open GeneralCanonicalObservations (Recorded Observation)
open GeneralNormalizedObservation (Rewrites Snapshot)
abbrev snapshot {roles : Roles.RoleDecls} (a : State roles) := a.core.erased.current.context.state
open Core.PresenceGeneration (TyTerm)

structure Promotion (s : GeneralNominalState.State) where
  choose : Fin s.base.slots → Bool
  plain : ∀ slot, choose slot = true → s.nominals slot = none
  checks : ∀ slot, choose slot = true → Rewrites s.base (.var slot) (.base .int)

variable {s : GeneralNominalState.State}

def view (p : Promotion s) : Snapshot s.base where
  kinds := s.view.kinds
  shapes := s.view.shapes
  shapes_injective := s.view.shapes_injective
  canonical := s.view.canonical
  heads := fun i => if p.choose i then .scalar .int else s.view.heads i
  checked := by
    intro i t named
    split at named
    · rename_i yes
      cases Option.some.inj named
      exact p.checks i yes
    · exact s.view.checked i t named

def updated (p : Promotion s) : GeneralNominalState.State := {s with
  view := view p
  bodies_opaque := by
    intro slot desc found
    show (if p.choose slot then .scalar .int else s.view.heads slot) = _
    split
    · rename_i yes
      rw [p.plain slot yes] at found
      cases found
    · exact s.bodies_opaque slot desc found }

theorem graph_new (p : Promotion s) (i : Fin s.base.slots) (yes : p.choose i = true) :
    (updated p).view.graph i ≠ .unresolved := by
  change (if p.choose i then .scalar .int else s.view.heads i).node ≠ _
  rw [ite_eq_left yes]
  intro impossible
  cases impossible

theorem graph_old (p : Promotion s) (i : Fin s.base.slots) (no : p.choose i ≠ true) :
    (updated p).view.graph i = s.view.graph i := by
  change (if p.choose i then .scalar .int else s.view.heads i).node = _
  rw [ite_eq_right no]
  rfl

theorem known_exact (p : Promotion s) (n : Nat) :
    Known (updated p) n ↔ Known s n ∨ ∃ i : Fin s.base.slots, p.choose i = true ∧ s.base.source i = n := by
  constructor
  · rintro ⟨i,id,head|nom⟩
    · by_cases yes : p.choose i = true
      · exact Or.inr ⟨i,yes,id⟩
      · exact Or.inl ⟨i,id,Or.inl (graph_old p i yes ▸ head)⟩
    · exact Or.inl ⟨i,id,Or.inr nom⟩
  · rintro (⟨i,id,head|nom⟩ | ⟨i,yes,id⟩)
    · by_cases yes : p.choose i = true
      · exact ⟨i,id,Or.inl (graph_new p i yes)⟩
      · exact ⟨i,id,Or.inl ((graph_old p i yes).symm ▸ head)⟩
    · exact ⟨i,id,Or.inr nom⟩
    · exact ⟨i,id,Or.inl (graph_new p i yes)⟩

abbrev current {roles : Roles.RoleDecls} (a : State roles) := a.core.erased.current.context

def context {roles : Roles.RoleDecls} (a : State roles) (p : Promotion (snapshot a)) :
    GeneralNominalCandidates.Context :=
  {current a with state := updated p}

theorem cache {roles : Roles.RoleDecls} (a : State roles) (p : Promotion (snapshot a))
    (old : CacheSound a (snapshot a))
    (proved : ∀ slot, p.choose slot = true → Justified a (.normalized (snapshot a).base slot (.base .int))) :
    CacheSound a (updated p) := by
  intro observation found
  cases found with
  | scalar slot scalar head =>
    change (if p.choose slot then .scalar .int else (snapshot a).view.heads slot) = .scalar scalar at head
    split at head
    · rename_i yes
      cases head
      exact proved slot yes
    · exact old _ (Recorded.scalar (snapshot := snapshot a) slot scalar head)
  | structural slot kind children head =>
    change (if p.choose slot then .scalar .int else (snapshot a).view.heads slot) = .structural kind children at head
    split at head
    · cases head
    · exact old _ (Recorded.structural (snapshot := snapshot a) slot kind children head)
  | nominal slot d seen => exact old _ (Recorded.nominal (snapshot := snapshot a) slot d seen)

def certify {roles : Roles.RoleDecls} (a : State roles) (p : Promotion (snapshot a))
    (old : CacheSound a (snapshot a))
    (proved : ∀ slot, p.choose slot = true → Justified a (.normalized (snapshot a).base slot (.base .int))) :
    Refresh a (context a p) := by
  let oldR := GeneralNominalRefinements.refl (snapshot a)
  exact ⟨⟨oldR.base,oldR.heads,oldR.nominals,oldR.ordinary,fun i h => (known_exact p i).mpr (Or.inl h),
    oldR.reserved,oldR.allocated,rfl,rfl⟩,rfl,(fun _ yes => yes),
    (fun _ models => ⟨models.1.1.1,models.1.1.2.2⟩),cache a p old proved⟩

end Yulang.GeneralMixedCheckedPromotion306
