import Yulang.GeneralGeneratedDictionaryAcc299

namespace Yulang.GeneralGeneratedDictionaryMinFuel299
open CommonRoleOutermostResolver (Dictionary)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299 (all_left)
open GeneralGeneratedDictionaryAcc299 (monotone_fuel)

def earliest (read : Read) (i : Nat) : Nat → Option Nat
  | 0 => none
  | n+1 => (earliest read i n).orElse (fun _ =>
      match run read (n+1) i with
      | none => none
      | some _ => some (n+1))

def Exact (read : Read) (i k : Nat) : Prop :=
  (∃ d, run read k i = some d) ∧ ∀ n, n < k → run read n i = none

theorem earliest_none (read : Read) (i cap : Nat) (no : earliest read i cap = none) :
    ∀ j, j ≤ cap → run read j i = none := by
  induction cap with
  | zero =>
    intro j leq
    cases Nat.eq_zero_of_le_zero leq
    rfl
  | succ cap ih =>
    cases e : earliest read i cap with
    | some _ => simp [earliest,e] at no
    | none =>
      cases h : run read (cap+1) i with
      | some _ => simp [earliest,e,h] at no
      | none =>
        intro j leq
        by_cases eq : j = cap+1
        · simpa [eq] using h
        · exact ih e j (by omega)

theorem earliest_some (read : Read) (i cap k : Nat) (found : earliest read i cap = some k) :
    k ≤ cap ∧ Exact read i k := by
  induction cap with
  | zero => cases found
  | succ cap ih =>
    cases e : earliest read i cap with
    | some prior =>
      have eq : prior = k := by simpa [earliest,e] using found
      subst prior
      obtain ⟨leq,cert⟩ := ih e
      exact ⟨by omega,cert⟩
    | none =>
      cases test : run read (cap+1) i with
      | none => simp [earliest,e,test] at found
      | some d =>
        have eq : cap+1 = k := by simpa [earliest,e,test] using found
        subst k
        exact ⟨Nat.le_refl _,⟨d,test⟩,fun j lt => earliest_none read i cap e j (by omega)⟩

end Yulang.GeneralGeneratedDictionaryMinFuel299
