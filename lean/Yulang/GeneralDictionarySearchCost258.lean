import Yulang.GeneralDictionaryEarlySearch258
namespace Yulang.GeneralDictionarySearchCost258
open GeneralDictionaryLooseFamilyNames240 (lower upper)

/-- Counts loop visits only, not arbitrary-precision arithmetic or elapsed time. -/
def probes (family : Nat → Nat) (name : Nat) : Nat → Nat → Nat
 | _,0 => 0
 | start,fuel+1 =>
   if name < lower start then 1
   else if family start = name then 1
   else 1 + probes family name (start+1) fuel

theorem fuel_bound (family : Nat → Nat) (name start fuel : Nat) : probes family name start fuel ≤ fuel := by
 induction fuel generalizing start with
 | zero => exact Nat.le_refl _
 | succ fuel ih =>
   simp only [probes]
   split
   · omega
   · split
     · omega
     · have bound := ih (start+1); omega

theorem envelope_bound (family : Nat → Nat) (name start fuel distance : Nat)
 (beyond : name < lower (start+distance)) : probes family name start fuel ≤ distance+1 := by
 induction distance generalizing start fuel with
 | zero =>
   cases fuel with
   | zero => exact Nat.zero_le _
   | succ fuel =>
     simp only [Nat.add_zero] at beyond
     simp only [probes,beyond,ite_true]
     omega
 | succ distance ih =>
   cases fuel with
   | zero => exact Nat.zero_le _
   | succ fuel =>
     simp only [probes]
     split
     · omega
     · split
       · omega
       · have shifted : name < lower ((start+1)+distance) := by simpa only [Nat.add_assoc,Nat.add_comm 1 distance] using beyond
         have bound := ih (start+1) fuel shifted
         omega

theorem match_bound (family : Nat → Nat) (name start fuel distance : Nat)
 (found : family (start+distance) = name) : probes family name start fuel ≤ distance+1 := by
 induction distance generalizing start fuel with
 | zero =>
   cases fuel with
   | zero => exact Nat.zero_le _
   | succ fuel =>
     simp only [Nat.add_zero] at found
     simp only [probes,found,ite_true]
     split <;> omega
 | succ distance ih =>
   cases fuel with
   | zero => exact Nat.zero_le _
   | succ fuel =>
     simp only [probes]
     split
     · omega
     · split
       · omega
       · have shifted : family ((start+1)+distance) = name := by simpa only [Nat.add_assoc,Nat.add_comm 1 distance] using found
         have bound := ih (start+1) fuel shifted
         omega

theorem lower_match (index : Nat) :
 probes (fun i => lower (i+1)) (lower (index+1)) 0 (lower (index+1)+1) ≤ index+1 :=
 match_bound _ _ _ _ index (by simp only [Nat.zero_add])

theorem upper_match (index : Nat) :
 probes upper (upper index) 0 (upper index+1) ≤ index+1 :=
 match_bound _ _ _ _ index (by simp only [Nat.zero_add])
end Yulang.GeneralDictionarySearchCost258
