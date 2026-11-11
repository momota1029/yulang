import Yulang.GeneralDeclarations

/-! A persistent numeric encoding of source origins. The seed belongs to the
source snapshot and is preserved by private extension. Different invocation,
declaration and obligation origins have different identities even when allocated
from the same snapshot; repeating an origin returns the same identity. -/
namespace Yulang.GeneralNominalIdentities

abbrev Origin := Nat × Nat × Nat × Nat × Nat

def pair (first last : Nat) : Nat := (first + last) * (first + last) + first

private theorem band {first last : Nat} (less : first < last) : first * first + first < last * last := by
  have lower : first + 1 ≤ last := less
  have multiplied := Nat.mul_le_mul lower lower
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at multiplied
  omega

theorem pair_injective : Function.Injective (fun p : Nat × Nat => pair p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ equal
  change pair a b = pair c d at equal
  have sums : a + b = c + d := by
    by_cases less : a + b < c + d
    · have separated := band less
      unfold pair at equal
      omega
    · by_cases more : c + d < a + b
      · have separated := band more
        unfold pair at equal
        omega
      · omega
  unfold pair at equal
  rw [sums] at equal
  have first := Nat.add_left_cancel equal
  have last : b = d := by omega
  exact Prod.ext first last

def encode (key : Origin) : Nat :=
  pair key.1 (pair key.2.1 (pair key.2.2.1 (pair key.2.2.2.1 key.2.2.2.2)))

theorem encode_injective : Function.Injective encode := by
  rintro ⟨a,b,c,d,e⟩ ⟨f,g,h,i,j⟩ equal
  have one : (a, pair b (pair c (pair d e))) = (f, pair g (pair h (pair i j))) := by
    apply pair_injective
    exact equal
  have two : (b, pair c (pair d e)) = (g, pair h (pair i j)) := by
    apply pair_injective
    exact congrArg Prod.snd one
  have three : (c, pair d e) = (h, pair i j) := by
    apply pair_injective
    exact congrArg Prod.snd two
  have four : (d,e) = (i,j) := by
    apply pair_injective
    exact congrArg Prod.snd three
  exact Prod.ext (congrArg (fun p : Nat × Nat => p.1) one) (Prod.ext (congrArg (fun p : Nat × Nat => p.1) two)
    (Prod.ext (congrArg (fun p : Nat × Nat => p.1) three) four))

theorem invocation_le (key : Origin) : key.1 ≤ encode key := by
  unfold encode pair
  omega

def source (seed : Nat) (key : Origin) : Nat := seed + 1 + encode key

theorem source_identity (seed : Nat) (first last : Origin) :
    source seed first = source seed last ↔ first = last := by
  constructor
  · intro equal
    exact encode_injective (Nat.add_left_cancel equal)
  · rintro rfl; rfl

theorem source_above_seed (seed : Nat) (key : Origin) : seed < source seed key := by
  unfold source
  omega

theorem source_above_invocation (seed : Nat) (key : Origin) : key.1 < source seed key := by
  have bound := invocation_le key
  unfold source
  omega

end Yulang.GeneralNominalIdentities
