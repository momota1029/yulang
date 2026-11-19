import Yulang.GeneralRebasePortMeaning280
import Yulang.GeneralNominalVersionedModelSupport237

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePortCopy280
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralSourceState (Interval)
open GeneralRebasePortMeaning280 (Matches atoms_exact matches_refl)
open CommonNominalFullCarrier (Ty Equivalent subtype_refl)

abbrev Write := Nat × Nat

def lookup (writes : List Write) (target : Nat) : Option Nat :=
  match writes with
  | [] => none
  | (a,b) :: rest => if a = target then some b else lookup rest target

def Copy (writes : List Write) (base : Assignment) : Assignment := fun n =>
  match lookup writes n with
  | none => base n
  | some source => ((base source).1,(base n).2)

def Unambiguous (writes : List Write) : Prop :=
  ∀ a ∈ writes, ∀ b ∈ writes, a.1 = b.1 → a.2 = b.2

def Apart (writes : List Write) (pool : List Nat) : Prop :=
  ∀ a ∈ writes, a.1 ∉ pool

def Isolated (writes : List Write) : Prop :=
  Apart writes (writes.map Prod.snd)

theorem lookup_source {writes : List Write} (found : lookup writes target = some source) :
    (target,source) ∈ writes := by
  induction writes with
  | nil => cases found
  | cons a rest ih =>
    obtain ⟨a,b⟩ := a
    by_cases same : a = target
    · subst a
      have h : b = source := by simpa [lookup] using found
      subst b
      exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      exact ih (by simpa only [lookup,ite_eq_right same] using found)

theorem lookup_absent {writes : List Write} (apart : ∀ a ∈ writes, a.1 ≠ target) :
    lookup writes target = none := by
  cases found : lookup writes target with
  | none => rfl
  | some source => exact False.elim (apart _ (lookup_source found) rfl)

theorem lookup_exact {writes : List Write} (unique : Unambiguous writes)
    (recorded : (target,source) ∈ writes) : lookup writes target = some source := by
  induction writes with
  | nil => cases recorded
  | cons a rest ih =>
    obtain ⟨a,b⟩ := a
    by_cases same : a = target
    · have h := unique _ List.mem_cons_self _ recorded same
      change b = source at h
      simp only [lookup,ite_eq_left same, h]
    · have tail := (List.mem_cons.mp recorded).resolve_left (fun eq => same (congrArg Prod.fst eq).symm)
      exact (ite_eq_right same).trans (ih
        (fun x xin y yin equal => unique x (List.mem_cons_of_mem _ xin) y (List.mem_cons_of_mem _ yin) equal)
        tail)

theorem copy_agrees {writes : List Write} (apart : Apart writes pool) (m : Assignment) :
    Agree pool m (Copy writes m) := by
  intro n hp
  have blank : lookup writes n = none := lookup_absent (fun a present equal => apart a present (equal.symm ▸ hp))
  simp [Copy,blank]

theorem rows_preserved (writes : List Write) (m : Assignment) (n : Nat) :
    (Copy writes m n).2 = (m n).2 := by
  unfold Copy
  cases lookup writes n <;> rfl

theorem copy_value {writes : List Write} (unique : Unambiguous writes)
    {m : Assignment} (recorded : (target,source) ∈ writes) :
    (Copy writes m target).1 = (m source).1 := by
  simp [Copy,lookup_exact unique recorded]

theorem source_unchanged {writes : List Write} (isolated : Isolated writes)
    {m : Assignment} (recorded : (target,source) ∈ writes) :
    Copy writes m source = m source :=
  (copy_agrees isolated m source (List.mem_map.mpr ⟨_,recorded,rfl⟩)).symm

theorem copy_equation {writes : List Write} (unique : Unambiguous writes) (isolated : Isolated writes)
    {m : Assignment} (recorded : (target,source) ∈ writes) :
    (Copy writes m target).1 = (Copy writes m source).1 := by
  rw [copy_value unique recorded,source_unchanged isolated recorded]

def PairWrites (fixed original : Interval) : List Write :=
  [(fixed.1,original.1),(fixed.2,original.2)]

theorem interval_copy {writes : List Write} (unique : Unambiguous writes) (isolated : Isolated writes)
    (written : PairWrites fixed original ⊆ writes) (m : Assignment) :
    Matches (Copy writes m) fixed original := by
  have lo := copy_equation (m := m) unique isolated (written (List.mem_cons_self))
  have hi := copy_equation (m := m) unique isolated (written (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · rw [lo]; exact subtype_refl _
  · rw [lo]; exact subtype_refl _
  · rw [hi]; exact subtype_refl _
  · rw [hi]; exact subtype_refl _

theorem copy_model {state : State roles} (support : Support state supported)
    (apart : Apart writes supported) {m : Assignment} (valid : Models state m) :
    Models state (Copy writes m) :=
  GeneralNominalVersionedModelSupport237.patch support valid (copy_agrees apart m)

end Yulang.GeneralRebasePortCopy280
