import Yulang.GeneralDictionaryCompactView257
import Yulang.GeneralDictionaryHistoricalFields256
namespace Yulang.GeneralDictionaryCompactFields257
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalRebaseRawView243 (View Descriptor Parameter)
open GeneralDictionaryCompactView257 (compact baseAtoms)
open GeneralDictionaryUpperHistory257 (history)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralPresenceIdempotentTree257 (reduce)
open GeneralDictionaryHistoricalFields256 (representative)
open GeneralDictionaryLooseFamilyBase240 (source original anchor)

theorem slot_type (n : Nat) (slot : Fin (n+5)) :
 ((compact n).slot slot).ty = .var (representative slot) := by
 change reduce (mapping (history n) (source n slot)).ty = _
 by_cases small : slot.val < 5
 · rw [GeneralDictionaryLooseFamilyBase240.source_small slot small,
     GeneralDictionaryFullReduced257.initial_fixed n slot.val (by omega)]
   simp only [representative,small,ite_true]
 · rw [GeneralDictionaryLooseFamilyBase240.source_large slot (by omega),
     GeneralDictionaryFullReduced257.lower_fixed n (slot.val-4) (by have bound := slot.isLt; omega)]
   simp only [representative,small,ite_false]

def foo : Descriptor := ⟨0,[.type (.var 0) (.var 0)]⟩
def pair : Descriptor := ⟨5,[.type (.var 2) (.var 4),.type (.var 2) (.var 4)]⟩

theorem original_type (n : Nat) (slot : Fin 5) :
 reduce (mapping (history n) (source n (original n slot))).ty = .var slot.val := by
 rw [GeneralDictionaryLooseFamilyBase240.source_original,
   GeneralDictionaryFullReduced257.initial_fixed n slot.val (by have bound := slot.isLt; omega)]

theorem anchor_type (n : Nat) :
 reduce (mapping (history n) (source n (anchor n))).ty = .var 2 := by
 rw [GeneralDictionaryLooseFamilyBase240.source_anchor,GeneralDictionaryFullReduced257.lower_fixed n n (by omega)]

theorem foo_descriptor (n : Nat) :
 GeneralNominalViewTypeMap255.descriptor reduce
 (GeneralNominalRebaseRawView243.descriptor (GeneralDictionaryLooseFamilyBase240.base n) (mapping (history n))
 (GeneralDictionaryLooseFamilyBase240.foo n)) = foo := by
 change Descriptor.mk 0 [Parameter.type (reduce (mapping (history n) (source n (original n 0))).ty)
   (reduce (mapping (history n) (source n (original n 0))).ty)] = _
 rw [original_type]
 rfl

theorem pair_descriptor (n : Nat) :
 GeneralNominalViewTypeMap255.descriptor reduce
 (GeneralNominalRebaseRawView243.descriptor (GeneralDictionaryLooseFamilyBase240.base n) (mapping (history n))
 (GeneralDictionaryLooseFamilyBase240.pair n)) = pair := by
 change Descriptor.mk 5 [Parameter.type (reduce (mapping (history n) (source n (anchor n))).ty)
   (reduce (mapping (history n) (source n (original n 4))).ty),
   Parameter.type (reduce (mapping (history n) (source n (anchor n))).ty)
   (reduce (mapping (history n) (source n (original n 4))).ty)] = _
 rw [anchor_type,original_type]
 rfl

theorem nominal (n : Nat) (slot : Fin (n+5)) : (compact n).nominals slot =
 if slot.val = 3 then some pair else if slot.val = 2 ∨ 4 ≤ slot.val then some foo else none := by
 change Option.map (GeneralNominalViewTypeMap255.descriptor reduce)
   (Option.map (GeneralNominalRebaseRawView243.descriptor (GeneralDictionaryLooseFamilyBase240.base n) (mapping (history n)))
     (if slot.val = 3 then some (GeneralDictionaryLooseFamilyBase240.pair n)
       else if slot.val = 2 ∨ 4 ≤ slot.val then some (GeneralDictionaryLooseFamilyBase240.foo n) else none)) = _
 split
 · simp only [Option.map_some,pair_descriptor]
 · split
   · simp only [Option.map_some,foo_descriptor]
   · rfl

theorem no_heads (n : Nat) (slot : Fin (n+5)) : (compact n).heads slot = none := rfl

theorem no_intervals (n : Nat) : (compact n).intervals = [] := rfl

def baseFacts : List (Atom Nat) :=
 [.tyLe (.var 0) (.base .int),.tyLe (.base .int) (.var 0),
  .tyLe (.var 1) (.base .int),.tyLe (.base .int) (.var 1)]

theorem base_fixed (n : Nat) : baseAtoms n = baseFacts := by
 change [Atom.tyLe (reduce (mapping (history n) (source n (original n 0))).ty) (.base .int),
  Atom.tyLe (.base .int) (reduce (mapping (history n) (source n (original n 0))).ty),
  Atom.tyLe (reduce (mapping (history n) (source n (original n 1))).ty) (.base .int),
  Atom.tyLe (.base .int) (reduce (mapping (history n) (source n (original n 1))).ty)] = _
 rw [original_type,original_type]
 rfl

theorem ordinary (n : Nat) : (compact n).ordinary = baseFacts ++ GeneralDictionaryOrdinaryCanonical257.compact n := by
 change baseAtoms n ++ _ = _
 rw [base_fixed]
end Yulang.GeneralDictionaryCompactFields257
