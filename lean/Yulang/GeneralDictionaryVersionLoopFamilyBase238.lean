import Yulang.GeneralDictionaryVersionLoopNames238
import Yulang.GeneralDictionaryVersionLoopInitial238
set_option backward.isDefEq.respectTransparency false
/-! Uniform finite observation bases for the proposed retarget iteration.
These are explicit source maps and descriptors, not an operational trace. -/
namespace Yulang.GeneralDictionaryVersionLoopFamilyBase238
open GeneralDictionaryVersionLoopNames238
open GeneralDictionaryVersionLoopSource237 (model S F P)
open CommonNominalFullCarrier

def source (n : Nat) (slot : Fin (n+4)) : Nat :=
 if slot.val < 4 then slot.val else lower (slot.val-3)

theorem source_small (slot : Fin (n+4)) (small : slot.val < 4) : source n slot = slot.val := by
 simp [source,small]
theorem source_large (slot : Fin (n+4)) (large : 4 ≤ slot.val) : source n slot = lower (slot.val-3) := by
 simp [source,show ¬ slot.val < 4 by omega]
theorem source_injective (n) : Function.Injective (source n) := by
 intro a b equal
 by_cases first : a.val < 4
 · by_cases last : b.val < 4
   · exact Fin.ext (by simpa only [source,first,last,ite_true] using equal)
   · have big := lower_above (b.val-4)
     have arith : b.val-3 = (b.val-4)+1 := by omega
     rw [source_small a first,source_large b (by omega),arith] at equal
     omega
 · by_cases last : b.val < 4
   · have big := lower_above (a.val-4)
     have arith : a.val-3 = (a.val-4)+1 := by omega
     rw [source_large a (by omega),arith,source_small b last] at equal
     omega
   · rw [source_large a (by omega),source_large b (by omega)] at equal
     have same := injective equal
     apply Fin.ext; omega

def embed (n : Nat) (slot : Fin (n+4)) : Fin ((n+1)+4) := ⟨slot.val,by omega⟩
theorem source_embed (n) (slot : Fin (n+4)) : source (n+1) (embed n slot) = source n slot := rfl

def original (n : Nat) (slot : Fin 4) : Fin (n+4) := ⟨slot.val,by omega⟩
theorem source_original (n) (slot : Fin 4) : source n (original n slot) = slot.val := source_small _ slot.isLt

def anchor (n : Nat) : Fin (n+4) := ⟨if n=0 then 2 else n+3,by split <;> omega⟩
theorem source_anchor (n) : source n (anchor n) = lower n := by
 cases n with
 | zero => rfl
 | succ n =>
   rw [source_large _ (by simp [anchor])]
   have same : (anchor (n+1)).val-3 = n+1 := by simp [anchor]
   rw [same]

abbrev base (n : Nat) : GeneralSourceState.State where
 slots := n+4
 source := source n
 source_injective := source_injective n
 rowSource := source n
 ordinary := GeneralDictionaryVersionLoopSource237.base.ordinary.map
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
abbrev foo (n : Nat) : GeneralNominalState.Descriptor (n+4) :=
 ⟨0,⟨[.type],0⟩,[.type (original n 0,original n 0)],rfl⟩
abbrev pair (n : Nat) : GeneralNominalState.Descriptor (n+4) :=
 ⟨5,⟨[.type,.type],5⟩,[.type (anchor n,anchor n),.type (anchor n,anchor n)],rfl⟩

theorem model_anchor (n) : (model (source n (anchor n))).1 = F := by
 rw [source_anchor]
 cases n with
 | zero => rfl
 | succ n => exact GeneralDictionaryVersionLoopPacket237.above_value _ (lower_above n)

theorem model_added (slot : Fin (n+4)) (added : 4 ≤ slot.val) : (model (source n slot)).1 = F := by
 rw [source_large slot added]
 apply GeneralDictionaryVersionLoopPacket237.above_value
 have same : slot.val-3 = (slot.val-4)+1 := by omega
 rw [same]
 exact lower_above _
end Yulang.GeneralDictionaryVersionLoopFamilyBase238
