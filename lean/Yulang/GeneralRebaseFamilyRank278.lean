import Yulang.GeneralRebaseFamilyDecode278

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
set_option maxRecDepth 14000
namespace Yulang.GeneralRebaseFamilyRank278
open GeneralRebaseFamilyDecode278
attribute [local irreducible] predecessor

def depthWithin (kind : Style) : Nat → Nat → Option Nat
  | 0,_ => none
  | fuel+1,name =>
    if name = 2 then some 0 else
    match predecessor kind name with
    | some (.lower,prior) =>
      if prior < name then (depthWithin kind fuel prior).map Nat.succ else none
    | _ => none

def depth (kind : Style) (name : Nat) : Option Nat := depthWithin kind (name+1) name

theorem greater_base (kind : Style) (lane : Lane) (prior : Nat) :
    2 < allocated kind lane prior := by
  have h := above kind lane prior
  have small : 2 ≤ kind.seed := by cases kind <;> decide
  exact Nat.lt_of_le_of_lt small h

theorem bounded_complete (kind : Style) (n fuel : Nat) (limit : lowerName kind n < fuel) :
    depthWithin kind fuel (lowerName kind n) = some n := by
  induction n generalizing fuel with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | succ n ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      change allocated kind .lower (lowerName kind n) < fuel+1 at limit
      have decreases := pred_lt kind .lower (lowerName kind n)
      have bound : lowerName kind n < fuel := by omega
      change depthWithin kind (fuel+1) (allocated kind .lower (lowerName kind n)) = some (n+1)
      rw [depthWithin]
      simp only [show allocated kind .lower (lowerName kind n) ≠ 2 from
        Nat.ne_of_gt (greater_base kind .lower _),ite_false,
        (predecessor_exact kind _ .lower _).mpr rfl,ite_eq_left decreases,
        ih fuel bound,Option.map_some]

theorem correct (kind : Style) (n : Nat) : depth kind (lowerName kind n) = some n :=
  bounded_complete kind n _ (Nat.lt_succ_self _)

theorem bounded_sound (kind : Style) (fuel name n : Nat) (found : depthWithin kind fuel name = some n) :
    lowerName kind n = name := by
  induction fuel generalizing name n with
  | zero => cases found
  | succ fuel smaller =>
    rw [depthWithin] at found
    by_cases atBase : name = 2
    · subst name
      simp only [ite_true,Option.some.injEq] at found
      subst n
      rfl
    · simp only [atBase,ite_false] at found
      cases prev : predecessor kind name with
      | none => rw [prev] at found; cases found
      | some pair =>
        obtain ⟨lane,prior⟩ := pair
        have encoded := (predecessor_exact kind name lane prior).mp prev
        have less : prior < name := encoded ▸ pred_lt kind lane prior
        cases lane
        · simp only [prev,ite_eq_left less] at found
          cases below : depthWithin kind fuel prior with
          | none => rw [below] at found; cases found
          | some index =>
            rw [below] at found
            have eq : index+1 = n := Option.some.inj found
            subst n
            change allocated kind .lower (lowerName kind index) = name
            rw [smaller prior index below]
            exact encoded
        · rw [prev] at found
          cases found

theorem sound (kind : Style) (name : Nat) (n : Nat) (found : depth kind name = some n) :
    lowerName kind n = name := bounded_sound kind _ name n found

theorem depth_exact (kind : Style) (name n : Nat) :
    depth kind name = some n ↔ lowerName kind n = name :=
  ⟨sound kind name n,fun h => h ▸ correct kind n⟩

def rank (kind : Style) (name : Nat) : Option (Lane × Nat) := do
  let (lane,prev) ← predecessor kind name
  let n ← depth kind prev
  pure (lane,n)

theorem rank_exact (kind : Style) (name : Nat) (lane : Lane) (n : Nat) :
    rank kind name = some (lane,n) ↔ allocated kind lane (lowerName kind n) = name := by
  constructor
  · intro valid
    unfold rank at valid
    cases find : predecessor kind name with
    | none => rw [find] at valid; cases valid
    | some result =>
      obtain ⟨mode,prev⟩ := result
      rw [find] at valid
      change ((depth kind prev).bind fun index => some (mode,index)) = some (lane,n) at valid
      cases next : depth kind prev with
      | none => rw [next] at valid; cases valid
      | some i =>
        rw [next] at valid
        have same := Prod.mk.inj (Option.some.inj valid)
        have laneEq : mode = lane := same.1
        have idxEq : i = n := same.2
        subst mode
        subst i
        rw [(depth_exact kind prev n).mp next]
        exact (predecessor_exact kind name lane prev).mp find
  · rintro rfl
    unfold rank
    rw [(predecessor_exact kind _ lane _).mpr rfl]
    change ((depth kind (lowerName kind n)).bind fun j => some (lane,j)) = some (lane,n)
    rw [correct]
    rfl

theorem lower_exact (kind : Style) (name n : Nat) :
    rank kind name = some (.lower,n) ↔ lowerName kind (n+1) = name :=
  rank_exact kind name .lower n

theorem upper_exact (kind : Style) (name n : Nat) :
    rank kind name = some (.upper,n) ↔ upperName kind n = name :=
  rank_exact kind name .upper n

end Yulang.GeneralRebaseFamilyRank278
