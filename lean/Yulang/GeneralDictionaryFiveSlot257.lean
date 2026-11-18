import Yulang.GeneralDictionaryCompactFields257
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryFiveSlot257
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalRebaseRawView243 (View Descriptor)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCompactView257 (compact)
open GeneralDictionaryCompactFields257 (foo pair baseFacts)
open GeneralDictionaryHistoricalFields256 (representative)
open GeneralDictionaryLooseFamilyBase240 (original)

def descriptor (name : Nat) : Option Descriptor :=
 if name = 3 then some pair else if name = 2 ∨ 4 ≤ name then some foo else none

def projection (slot : Fin (n+5)) : Fin 5 :=
 ⟨representative slot,by have small := GeneralDictionaryHistoricalFields256.representative_small slot; omega⟩

def view (n : Nat) : View where
 slots := 5
 slot := fun index => CompTerm.var index.val
 ordinary := baseFacts ++ GeneralDictionaryOrdinaryCanonical257.compact n
 heads := fun _ => none
 intervals := []
 nominals := fun index => descriptor index.val

theorem original_projection (n : Nat) (index : Fin 5) : projection (original n index) = index := by
 apply Fin.ext
 change (if index.val < 5 then index.val else 2) = index.val
 simp only [index.isLt,ite_true]

theorem projected_descriptor (slot : Fin (n+5)) : descriptor (projection slot).val = descriptor slot.val := by
 by_cases small : slot.val < 5
 · change descriptor (if slot.val < 5 then slot.val else 2) = _
   simp only [small,ite_true]
 · have large : 5 ≤ slot.val := by omega
   change descriptor (if slot.val < 5 then slot.val else 2) = _
   simp only [small,ite_false]
   simp [descriptor,show slot.val ≠ 3 by omega,show 4 ≤ slot.val by omega]

theorem compact_nominal (n : Nat) (slot : Fin (n+5)) :
 (compact n).nominals slot = (view n).nominals (projection slot) := by
 rw [GeneralDictionaryCompactFields257.nominal]
 exact (projected_descriptor slot).symm

theorem compact_target (n : Nat) (slot : Fin (n+5)) :
 ((compact n).slot slot).ty = ((view n).slot (projection slot)).ty :=
 GeneralDictionaryCompactFields257.slot_type n slot

theorem models_exact (n : Nat) (assignment : Assignment) :
 (compact n).Models assignment ↔ (view n).Models assignment := by
 unfold View.Models
 have ordinary : (compact n).ordinary = (view n).ordinary := GeneralDictionaryCompactFields257.ordinary n
 rw [ordinary]
 apply and_congr Iff.rfl
 have compactHeads : (∀ index term, (compact n).heads index = some term →
   CommonNominalFullCarrier.Equivalent (((compact n).slot index).ty.eval CommonNominalFullCarrier.model assignment)
     (term.eval CommonNominalFullCarrier.model assignment)) := by
   intro index term found
   rw [GeneralDictionaryCompactFields257.no_heads] at found
   cases found
 have smallHeads : (∀ index term, (view n).heads index = some term →
   CommonNominalFullCarrier.Equivalent (((view n).slot index).ty.eval CommonNominalFullCarrier.model assignment)
     (term.eval CommonNominalFullCarrier.model assignment)) := by intro index term found; cases found
 apply and_congr (iff_of_true compactHeads smallHeads)
 apply and_congr
 · constructor <;> intro _ pair member <;> cases member
 · constructor
   · intro valid index d found
     have matching : (compact n).nominals (original n index) = some d := by
       rw [compact_nominal,original_projection]
       exact found
     have proof := valid (original n index) d matching
     rw [compact_target,original_projection] at proof
     exact proof
   · intro valid index d found
     rw [compact_nominal] at found
     have proof := valid (projection index) d found
     rw [compact_target]
     exact proof

theorem stable (n : Nat) : view (n+1) = view 1 := by
 unfold view
 rw [GeneralDictionaryOrdinaryCanonical257.stable,GeneralDictionaryOrdinaryCanonical257.stable]

theorem five_slots (n : Nat) : (view n).slots = 5 := rfl

theorem ordinary_bound (n : Nat) : (view n).ordinary.length ≤ 8 := by
 change (baseFacts ++ GeneralDictionaryOrdinaryCanonical257.compact n).length ≤ 8
 rw [List.length_append]
 have small := GeneralDictionaryOrdinaryCanonical257.length_bound n
 change 4 + (GeneralDictionaryOrdinaryCanonical257.compact n).length ≤ 8
 omega
end Yulang.GeneralDictionaryFiveSlot257
