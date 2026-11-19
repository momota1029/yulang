import Init.Data.Nat.Sqrt.Lemmas
import Yulang.GeneralNominalIdentities

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalPairDecode278
open GeneralNominalIdentities (Origin pair encode source)

def unpairCandidate (n : Nat) : Nat × Nat :=
  let band := n.sqrt
  let a := n - band * band
  (a,band-a)

theorem sqrt_pair (a b : Nat) : (pair a b).sqrt = a+b := by
  let s := a+b
  let q := (pair a b).sqrt
  have lo : s*s ≤ pair a b := by unfold pair s; omega
  have hi : pair a b < (s+1)*(s+1) := by
    unfold pair s
    simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one]
    omega
  by_cases below : q < s
  · have sq := Nat.mul_le_mul (show q+1 ≤ s by omega) (show q+1 ≤ s by omega)
    have lt := Nat.lt_succ_sqrt (pair a b)
    change pair a b < (q+1)*(q+1) at lt
    omega
  by_cases above : s < q
  · have sq := Nat.mul_le_mul (show s+1 ≤ q by omega) (show s+1 ≤ q by omega)
    have le := Nat.sqrt_le (pair a b)
    change q*q ≤ pair a b at le
    omega
  omega

theorem splits (a b : Nat) : unpairCandidate (pair a b) = (a,b) := by
  unfold unpairCandidate
  rw [sqrt_pair]
  unfold pair
  apply Prod.ext <;> dsimp only <;> omega

def decodePair (n : Nat) : Option (Nat × Nat) :=
  let candidate := unpairCandidate n
  if pair candidate.1 candidate.2 = n then some candidate else none

theorem pair_exact (n : Nat) (a b : Nat) : decodePair n = some (a,b) ↔ pair a b = n := by
  constructor
  · intro found
    unfold decodePair at found
    dsimp only at found
    split at found
    · rename_i reconstructed
      have same := Option.some.inj found
      exact (congrArg (fun z : Nat × Nat => pair z.1 z.2) same).symm.trans reconstructed
    · contradiction
  · rintro rfl
    simp [decodePair,splits]

def originCandidate (n : Nat) : Origin :=
  let (r,z) := unpairCandidate n
  let (d,z) := unpairCandidate z
  let (p,z) := unpairCandidate z
  let (b,k) := unpairCandidate z
  (r,d,p,b,k)

theorem origin_roundtrip (origin : Origin) : originCandidate (encode origin) = origin := by
 rcases origin with ⟨r,d,p,b,k⟩
 simp [originCandidate,encode,splits]

def decodeOrigin (n : Nat) : Option Origin :=
  let possible := originCandidate n
  if encode possible = n then some possible else none

theorem origin_exact (n : Nat) (origin : Origin) : decodeOrigin n = some origin ↔ encode origin = n := by
  constructor
  · intro found
    unfold decodeOrigin at found
    dsimp only at found
    split at found
    · rename_i reconstructed
      exact (Option.some.inj found) ▸ reconstructed
    · contradiction
  · rintro rfl
    simp [decodeOrigin,origin_roundtrip]

end Yulang.GeneralNominalPairDecode278
