import Yulang.GeneralDictionaryKnownProjection257
namespace Yulang.GeneralDictionaryPointProjection257
open GeneralDictionaryLooseIterationBook240 (context)
open GeneralDictionaryLooseFamilyBase240 (foo pair anchor original)
open GeneralDictionaryFiveSlot257 (projection)
open GeneralNominalReobservationSteps (PointAt PointDescriptor PointParameter)

theorem foo_point (n : Nat) : PointDescriptor (foo n) := by
 intro parameter member
 cases List.mem_singleton.mp member
 rfl

theorem pair_nonpoint (n : Nat) : ¬ PointDescriptor (pair n) := by
 intro point
 have same := point (.type (anchor n,original n 4)) (List.mem_cons_self ..)
 have values := congrArg Fin.val same
 change (if n=0 then 2 else n+4) = 4 at values
 split at values <;> omega

theorem classified (n : Nat) (slot : Fin (n+5)) :
 PointAt (context n).state slot ↔ slot.val=2 ∨ 4 ≤ slot.val := by
 change (∃ d, (if slot.val=3 then some (pair n) else if slot.val=2 ∨ 4 ≤ slot.val then some (foo n) else none) = some d ∧ PointDescriptor d) ↔ _
 by_cases three : slot.val=3
 · simp only [three,ite_true,Option.some.injEq]
   constructor
   · rintro ⟨d,same,point⟩
     cases same
     exact False.elim (pair_nonpoint n point)
   · intro impossible; omega
 · by_cases other : slot.val=2 ∨ 4 ≤ slot.val
   · simp only [three,ite_false,other,ite_true,Option.some.injEq]
     exact ⟨fun _ => True.intro,fun _ => ⟨foo n,rfl,foo_point n⟩⟩
   · constructor
     · rintro ⟨d,found,_⟩
       simp only [three,ite_false,other] at found
       cases found
     · intro impossible; exact False.elim (other impossible)

theorem projected_kind (slot : Fin (n+5)) :
 (projection slot).val=2 ∨ 4 ≤ (projection slot).val ↔ slot.val=2 ∨ 4 ≤ slot.val := by
 change ((if slot.val<5 then slot.val else 2)=2 ∨ 4 ≤ (if slot.val<5 then slot.val else 2)) ↔ _
 by_cases small : slot.val<5
 · simp only [small,ite_true]
 · simp only [small,ite_false,true_or,true_iff]
   exact Or.inr (by omega)

theorem preserved (n : Nat) (slot : Fin (n+5)) :
 PointAt (context n).state slot ↔ PointAt (context 0).state (projection slot) := by
 rw [classified,classified]
 exact (projected_kind slot).symm
end Yulang.GeneralDictionaryPointProjection257
