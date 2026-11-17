import Yulang.GeneralDictionaryLooseFamilyNames240
import Yulang.GeneralDictionaryLooseLoopInitial240
set_option backward.isDefEq.respectTransparency false
/-! Uniform finite observation bases for the proposed retarget iteration.
These are explicit source maps and descriptors, not an operational trace. -/
namespace Yulang.GeneralDictionaryLooseFamilyBase240
open GeneralDictionaryLooseFamilyNames240
open GeneralDictionaryLooseLoopSource240 (model S F P)
open CommonNominalFullCarrier

def source (n : Nat) (slot : Fin (n+5)) : Nat :=
 if slot.val < 5 then slot.val else lower (slot.val-4)

theorem source_small (slot : Fin (n+5)) (small : slot.val < 5) : source n slot = slot.val := by
 simp [source,small]
theorem source_large (slot : Fin (n+5)) (large : 5 ≤ slot.val) : source n slot = lower (slot.val-4) := by
 simp [source,show ¬ slot.val < 5 by omega]
theorem source_injective (n) : Function.Injective (source n) := by
 intro a b equal
 by_cases first : a.val < 5
 · by_cases last : b.val < 5
   · exact Fin.ext (by simpa only [source,first,last,ite_true] using equal)
   · have big := lower_above (b.val-5)
     have arith : b.val-4 = (b.val-5)+1 := by omega
     rw [source_small a first,source_large b (by omega),arith] at equal
     omega
 · by_cases last : b.val < 5
   · have big := lower_above (a.val-5)
     have arith : a.val-4 = (a.val-5)+1 := by omega
     rw [source_large a (by omega),arith,source_small b last] at equal
     omega
   · rw [source_large a (by omega),source_large b (by omega)] at equal
     have same := injective equal
     apply Fin.ext; omega

def embed (n : Nat) (slot : Fin (n+5)) : Fin ((n+1)+5) := ⟨slot.val,by omega⟩
theorem source_embed (n) (slot : Fin (n+5)) : source (n+1) (embed n slot) = source n slot := rfl

def original (n : Nat) (slot : Fin 5) : Fin (n+5) := ⟨slot.val,by omega⟩
theorem source_original (n) (slot : Fin 5) : source n (original n slot) = slot.val := source_small _ slot.isLt

def anchor (n : Nat) : Fin (n+5) := ⟨if n=0 then 2 else n+4,by split <;> omega⟩
theorem source_anchor (n) : source n (anchor n) = lower n := by
 cases n with
 | zero => rfl
 | succ n =>
   rw [source_large _ (by simp [anchor])]
   have same : (anchor (n+1)).val-4 = n+1 := by simp [anchor]
   rw [same]

abbrev base (n : Nat) : GeneralSourceState.State where
 slots := n+5
 source := source n
 source_injective := source_injective n
 rowSource := source n
 ordinary := GeneralDictionaryLooseLoopSource240.base.ordinary.map
   (PresenceNormalForm.Atom.rename (original n))
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 heads := fun _ => .unresolved
 intervals := []
 heads_sound := by intro _ _ _ _ h; cases h
 intervals_sound := by intro _ _ _ h; cases h
abbrev view (n : Nat) : GeneralNormalizedObservation.Snapshot (base n) where
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 canonical := by intro i; exact Fin.elim0 i
 heads := fun _ => .deferred .unresolved
 checked := by intro _ _ h; cases h
abbrev foo (n : Nat) : GeneralNominalState.Descriptor (n+5) :=
 ⟨0,⟨[.type],0⟩,[.type (original n 0,original n 0)],rfl⟩
abbrev pair (n : Nat) : GeneralNominalState.Descriptor (n+5) :=
 ⟨5,⟨[.type,.type],5⟩,[.type (anchor n,original n 4),.type (anchor n,original n 4)],rfl⟩

theorem model_anchor (n) : (model (source n (anchor n))).1 = F := by
 rw [source_anchor]
 cases n with
 | zero => rfl
 | succ n => exact GeneralDictionaryLooseLoopPacket240.above_value _ (lower_above n)

theorem model_added (slot : Fin (n+5)) (added : 5 ≤ slot.val) : (model (source n slot)).1 = F := by
 rw [source_large slot added]
 apply GeneralDictionaryLooseLoopPacket240.above_value
 have same : slot.val-4 = (slot.val-5)+1 := by omega
 rw [same]
 exact lower_above _
end Yulang.GeneralDictionaryLooseFamilyBase240
