import Yulang.GeneralGeneratedDictionaryMinFuel299

namespace Yulang.GeneralGeneratedDictionaryRankCheck299
open CommonRoleOutermostResolver (Dictionary)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299 (all_left run_has_row)
open GeneralGeneratedDictionaryMinFuel299

def inferredRank (read : Read) (cap : Nat) (i : Nat) : Nat :=
  (earliest read i cap).getD 0

def Known (read : Read) (domain : List Nat) : Prop :=
  ∀ i e, read i = some e → i ∈ domain

def check (read : Read) (domain : List Nat) (cap : Nat) : Bool :=
  domain.all fun i => (read i).isSome && (earliest read i cap).isSome

theorem checked_at (read : Read) (domain : List Nat) (cap : Nat)
    (pass : check read domain cap = true) {i : Nat} (member : i ∈ domain) :
    (∃ row, read i = some row) ∧ ∃ k, earliest read i cap = some k := by
  have both := List.all_eq_true.mp pass i member
  simp only [Bool.and_eq_true] at both
  constructor
  · cases h : read i with
    | none => simp [h] at both
    | some row => exact ⟨row,rfl⟩
  · cases h : earliest read i cap with
    | none => simp [h] at both
    | some k => exact ⟨k,rfl⟩

theorem no_later (read : Read) (i cap k n : Nat)
    (atCap : earliest read i cap = some k) (hit : ∃ d, run read n i = some d) : k ≤ n := by
  by_cases leq : k ≤ n
  · exact leq
  · have empty := (earliest_some read i cap k atCap).2.2 n (by omega)
    obtain ⟨d,found⟩ := hit
    rw [empty] at found
    cases found

theorem checked_closed (read : Read) (domain : List Nat) (cap : Nat)
    (known : Known read domain) (passed : check read domain cap = true) : Closed read := by
  intro i e h child member
  obtain ⟨_,k,hk⟩ := checked_at read domain cap passed (known i e h)
  obtain ⟨d,ok⟩ := (earliest_some read i cap k hk).2.1
  cases k with
  | zero => cases ok
  | succ k =>
    obtain ⟨row,ds,seen,all,_⟩ := (run_exact _ _ _ _).mp ok
    cases Option.some.inj (seen.symm.trans h)
    obtain ⟨_,childHit⟩ := all_left all child member
    exact run_has_row childHit

theorem checked_ranked (read : Read) (domain : List Nat) (cap : Nat)
    (known : Known read domain) (passed : check read domain cap = true) :
    Ranked read (inferredRank read cap) := by
  intro i e h child member
  obtain ⟨_,k,hk⟩ := checked_at read domain cap passed (known i e h)
  obtain ⟨d,ok⟩ := (earliest_some read i cap k hk).2.1
  cases k with
  | zero => cases ok
  | succ k =>
    obtain ⟨row,ds,seen,all,_⟩ := (run_exact _ _ _ _).mp ok
    cases Option.some.inj (seen.symm.trans h)
    obtain ⟨p,childHit⟩ := all_left all child member
    obtain ⟨childRow,childRowHit⟩ := run_has_row childHit
    obtain ⟨_,kc,hc⟩ := checked_at read domain cap passed (known child childRow childRowHit)
    have bound := no_later read child cap kc k hc ⟨p,childHit⟩
    simp [inferredRank,hk,hc]
    omega

theorem checked_total (read : Read) (domain : List Nat) (cap : Nat)
    (known : Known read domain) (passed : check read domain cap = true)
    (i : Nat) (e : Entry) (hit : read i = some e) :
    ∃ d, run read cap i = some d := by
  obtain ⟨_,k,hk⟩ := checked_at read domain cap passed (known i e hit)
  obtain ⟨leq,⟨d,found⟩,_⟩ := earliest_some read i cap k hk
  exact ⟨d,GeneralGeneratedDictionaryAcc299.monotone_fuel _ _ _ _ _ leq found⟩

end Yulang.GeneralGeneratedDictionaryRankCheck299
