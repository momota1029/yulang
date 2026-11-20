import Yulang.GeneralRebaseFreshOnlyFixtures283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseArchiveUnbounded283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseAliasFamily283 (Family)
open GeneralRebaseTwoWrites283 (Distinct known)
open GeneralRebaseInstallCache283 (Valid)
open GeneralRebaseFreshOnlyFixtures283

def keys (lo hi : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n+1 => lo (n+1) :: hi n :: keys lo hi n

theorem key_member (lo hi : Nat → Nat) (n key : Nat) :
    key ∈ keys lo hi n ↔ ∃ i < n, key = lo (i+1) ∨ key = hi i := by
  induction n with
  | zero => simp [keys]
  | succ n ih =>
    simp only [keys,List.mem_cons,ih]
    constructor
    · rintro (rfl|rfl|⟨i,small,h⟩)
      · exact ⟨n,by omega,Or.inl rfl⟩
      · exact ⟨n,by omega,Or.inr rfl⟩
      · exact ⟨i,by omega,h⟩
    · rintro ⟨i,small,h⟩
      by_cases hit : i = n
      · subst i
        exact h.elim Or.inl (fun z => Or.inr (Or.inl z))
      · exact Or.inr (Or.inr ⟨i,by omega,h⟩)

theorem key_count (lo hi : Nat → Nat) (n : Nat) : (keys lo hi n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [keys,List.length_cons,ih]
    omega

theorem nodup {lo hi : Nat → Nat} (sep : Distinct lo hi) (n : Nat) : (keys lo hi n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro repeated
      rcases List.mem_cons.mp repeated with same|later
      · exact sep.split _ _ same
      · obtain ⟨i,less,same|same⟩ := (key_member lo hi n _).mp later
        · have smaller := sep.monotone (i := i+1) (j := n+1) (by omega)
          omega
        · exact sep.split _ _ same
    · apply List.nodup_cons.mpr
      refine ⟨?_,ih⟩
      intro repeated
      obtain ⟨i,less,same|same⟩ := (key_member lo hi n _).mp repeated
      · exact sep.split _ _ same.symm
      · have eq := sep.hi_unique same
        omega

theorem length {defs : List (Entry Nat)} {lo hi up : Nat → Nat} {n a b : Nat}
    (family : Family defs n a b lo hi up) (sep : Distinct lo hi) :
    defs.length = 2*n := by
  have distinct := GeneralPresencePersistentSnapshot250.safe_nodup defs family.safe
  have perm := (List.perm_ext_iff_of_nodup distinct (nodup sep n)).mpr
    (fun k => (known family).trans (key_member lo hi n k).symm)
  exact (List.length_map Prod.fst).symm.trans (perm.length_eq.trans (key_count lo hi n))

theorem version_exact (n : Nat) (defs : List (Entry Nat))
    (valid : Valid defs (GeneralDictionaryVersionLoopIteration239.state n)) : defs.length = 2*n :=
  length (GeneralRebaseVersionDelta283.family_cache n defs valid) GeneralRebaseVersionDelta283.distinct

theorem loose_exact (n : Nat) (defs : List (Entry Nat))
    (valid : Valid defs (GeneralDictionaryLooseIterationIteration240.state n)) : defs.length = 2*n :=
  length (GeneralRebaseLooseDelta283.family_cache n defs valid) GeneralRebaseLooseDelta283.distinct

theorem version_no_uniform_bound (budget : Nat) : ∃ n,
    budget < (GeneralRebaseInstallCache283.initial (GeneralDictionaryVersionLoopIteration239.state n)).length := by
  refine ⟨budget+1,?_⟩
  have valid := GeneralRebaseInstallCache283.initial_valid
    (GeneralNominalVersionedMixedSeedLedger237.reachable (GeneralRebaseLoopBase282.Version.decode_reach (budget+1)))
  have grows := version_exact (budget+1) _ valid
  omega

theorem loose_no_uniform_bound (budget : Nat) : ∃ n,
    budget < (GeneralRebaseInstallCache283.initial (GeneralDictionaryLooseIterationIteration240.state n)).length := by
  refine ⟨budget+1,?_⟩
  have valid := GeneralRebaseInstallCache283.initial_valid
    (GeneralNominalVersionedMixedSeedLedger237.reachable (GeneralRebaseLoopBase282.Loose.decode_reach (budget+1)))
  have grows := loose_exact (budget+1) _ valid
  omega

end Yulang.GeneralRebaseArchiveUnbounded283
