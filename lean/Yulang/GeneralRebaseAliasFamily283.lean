import Yulang.GeneralRebaseAliasMemo283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseAliasFamily283
open Core.PresenceGeneration (TyTerm)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (SafeOrder)
open GeneralRebaseOneSource283 (One)
open GeneralRebaseAliasMemo283 (Aliases cache root equation exists_cache define_or_free)

def lowerRow (lo : Nat → Nat) (i : Nat) : Entry Nat :=
  (lo (i+1),.union (.var (lo i)) (.var (lo i)))

def upperRow (hi upRead : Nat → Nat) (i : Nat) : Entry Nat :=
  (hi i,.inter (.var (upRead i)) (.var (upRead i)))

structure Family (defs : List (Entry Nat)) (n lowSource highSource : Nat)
    (lo hi upRead : Nat → Nat) : Prop where
  cover : ∀ e, e ∈ defs ↔ ∃ i < n, e = lowerRow lo i ∨ e = upperRow hi upRead i
  low_base : lo 0 = lowSource
  upper_reads : ∀ i < n, upRead i = lo i ∨ upRead i = highSource
  low_fresh : ∀ e ∈ defs, e.1 ≠ lowSource
  high_fresh : ∀ e ∈ defs, e.1 ≠ highSource
  safe : SafeOrder defs

theorem lower_one (lo : Nat → Nat) (i : Nat) : One (lowerRow lo i).2 (lo i) :=
  .join (.var _) (.var _)

theorem upper_one (hi upRead : Nat → Nat) (i : Nat) : One (upperRow hi upRead i).2 (upRead i) :=
  .meet (.var _) (.var _)

theorem compiled {defs : List (Entry Nat)} {n a b : Nat} {lo hi upRead : Nat → Nat}
    (family : Family defs n a b lo hi upRead) :
    ∃ memo, cache defs [] = some memo := by
  apply exists_cache
  intro row used
  obtain ⟨i,bound,rfl|rfl⟩ := (family.cover row).mp used
  · exact ⟨_,lower_one lo i⟩
  · exact ⟨_,upper_one hi upRead i⟩

theorem lower_root {defs : List (Entry Nat)} {n a b : Nat} {lo hi upRead : Nat → Nat}
    (family : Family defs n a b lo hi upRead) {memo : Aliases} (made : cache defs [] = some memo)
    (i : Nat) (small : i ≤ n) : root memo (lo i) = a := by
  induction i with
  | zero => rw [family.low_base]; exact define_or_free defs memo a made family.low_fresh
  | succ i ih =>
    have member : lowerRow lo i ∈ defs := (family.cover _).mpr ⟨i,by omega,Or.inl rfl⟩
    exact (equation defs [] memo family.safe made _ member _ (lower_one lo i)).trans (ih (by omega))

theorem upper_root {defs : List (Entry Nat)} {n a b : Nat} {lo hi upRead : Nat → Nat}
    (family : Family defs n a b lo hi upRead) {memo : Aliases} (made : cache defs [] = some memo)
    (i : Nat) (small : i < n) :
    (upRead i = lo i → root memo (hi i) = a) ∧ (upRead i = b → root memo (hi i) = b) := by
  have member : upperRow hi upRead i ∈ defs := (family.cover _).mpr ⟨i,small,Or.inr rfl⟩
  have eq := equation defs [] memo family.safe made _ member _ (upper_one hi upRead i)
  constructor
  · intro hit
    change root memo (hi i) = root memo (upRead i) at eq
    rw [hit] at eq
    exact eq.trans (lower_root family made i (by omega))
  · intro hit
    change root memo (hi i) = root memo (upRead i) at eq
    rw [hit] at eq
    exact eq.trans (define_or_free defs memo b made family.high_fresh)

theorem target_range {defs : List (Entry Nat)} {n a b : Nat} {lo hi upRead : Nat → Nat}
    (family : Family defs n a b lo hi upRead) {memo : Aliases}
    (made : cache defs [] = some memo) (e : Entry Nat) (assigned : e ∈ defs) :
    root memo e.1 ∈ [a,b] := by
  obtain ⟨i,within,rfl|rfl⟩ := (family.cover e).mp assigned
  · exact List.mem_cons.mpr (Or.inl (lower_root family made (i+1) (by omega)))
  · rcases family.upper_reads i within with left|right
    · exact List.mem_cons.mpr (Or.inl ((upper_root family made i within).1 left))
    · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr ((upper_root family made i within).2 right)))

end Yulang.GeneralRebaseAliasFamily283
