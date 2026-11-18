import Yulang.GeneralDictionaryProjectionBoundary257
namespace Yulang.GeneralDictionaryKnownProjection257
open GeneralDictionaryLooseIterationBook240 (context)
open GeneralDictionaryLooseFamilyBase240 (source)
open GeneralDictionaryFiveSlot257 (projection)

/-- General source injectivity localizes Known to the actual slot. -/
theorem known_slot (raw : GeneralNominalState.State) (slot : Fin raw.base.slots) :
 GeneralNominalState.Known raw (raw.base.source slot) ↔
 (raw.view.graph slot ≠ .unresolved ∨ ∃ descriptor, raw.nominals slot = some descriptor) := by
 constructor
 · rintro ⟨index,same,known⟩
   have equal := raw.base.source_injective same
   subst index
   exact known
 · intro known
   exact ⟨slot,rfl,known⟩

theorem classified (n : Nat) (slot : Fin (n+5)) :
 GeneralNominalState.Known (context n).state (source n slot) ↔ 2 ≤ slot.val := by
 rw [known_slot]
 have graph : (context n).state.view.graph slot = .unresolved := rfl
 rw [graph]
 simp only [ne_self_iff_false,false_or]
 change (∃ descriptor,
   (if slot.val=3 then some (GeneralDictionaryLooseFamilyBase240.pair n)
    else if slot.val=2 ∨ 4 ≤ slot.val then some (GeneralDictionaryLooseFamilyBase240.foo n) else none) = some descriptor) ↔ _
 by_cases three : slot.val=3
 · simp [three]
 · by_cases other : slot.val=2 ∨ 4 ≤ slot.val
   · simp only [three,ite_false,other,ite_true,Option.some.injEq,exists_eq',true_iff]
     omega
   · constructor
     · rintro ⟨d,found⟩
       simp only [three,ite_false,other] at found
       cases found
     · intro large
       exact False.elim (by omega)

theorem projection_threshold (slot : Fin (n+5)) : 2 ≤ (projection slot).val ↔ 2 ≤ slot.val := by
 change 2 ≤ (if slot.val<5 then slot.val else 2) ↔ _
 split
 · rfl
 · omega

theorem preserved (n : Nat) (slot : Fin (n+5)) :
 GeneralNominalState.Known (context n).state (source n slot) ↔
 GeneralNominalState.Known (context 0).state (projection slot).val := by
 rw [classified]
 have initial := classified 0 (projection slot)
 have source0 : source 0 (projection slot) = (projection slot).val :=
   GeneralDictionaryLooseFamilyBase240.source_small _ (projection slot).isLt
 rw [source0] at initial
 exact (projection_threshold slot).symm.trans initial.symm
end Yulang.GeneralDictionaryKnownProjection257
