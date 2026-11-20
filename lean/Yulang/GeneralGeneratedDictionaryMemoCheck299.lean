import Yulang.GeneralGeneratedDictionaryMemo299
import Yulang.GeneralGeneratedDictionaryHeight299

namespace Yulang.GeneralGeneratedDictionaryMemoCheck299
open CommonRoleOutermostResolver (Dictionary)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryMemo299
open GeneralGeneratedDictionaryRankCheck299
open GeneralGeneratedDictionaryRankExists299
open GeneralGeneratedDictionaryAcc299
open GeneralGeneratedDictionaryScope299 (run_has_row)
open GeneralGeneratedDictionaryMinFuel299

theorem checked_iff (read : Read) (domain : List Nat) (known : Known read domain)
    (cap : Nat) : checkMemo read domain cap = true ↔ check read domain cap = true := by
  constructor
  · intro yes
    apply List.all_eq_true.mpr
    intro i mem
    obtain ⟨d,hit⟩ := (memo_exact read domain known cap i).mp (List.all_eq_true.mp yes i mem)
    obtain ⟨row,seen⟩ := run_has_row hit
    obtain ⟨k,when⟩ := found_at_cap read i cap ⟨d,hit⟩
    simp [seen,when]
  · intro yes
    apply List.all_eq_true.mpr
    intro i mem
    obtain ⟨⟨_,_⟩,k,h⟩ := checked_at read domain cap yes mem
    obtain ⟨leq,⟨d,hit⟩,_⟩ := earliest_some read i cap k h
    exact (memo_exact read domain known cap i).mpr ⟨d,monotone_fuel read k cap i d leq hit⟩

theorem checked_length (read : Read) (domain : List Nat) (known : Known read domain)
    (closed : Closed read) :
    checkMemo read domain domain.length = true ↔
      ∀ x ∈ domain, (∃ row, read x = some row) ∧ Acc (Edge read) x :=
  (checked_iff read domain known _).trans (GeneralGeneratedDictionaryFiniteCap299.check_length read domain closed known)

def bitFirst (read : Read) (domain : List Nat) (x : Nat) : Nat → Option Nat
  | 0 => none
  | n+1 => (bitFirst read domain x n).orElse
    (fun _ => if lookup x (memo read domain (n+1)) then some (n+1) else none)

theorem bit_first_exact (read : Read) (domain : List Nat) (known : Known read domain)
    (x cap : Nat) : bitFirst read domain x cap = earliest read x cap := by
  induction cap with
  | zero => rfl
  | succ n ih =>
    simp only [bitFirst,earliest,ih]
    congr 1
    funext _
    cases h : run read (n+1) x with
    | none =>
      have f : lookup x (memo read domain (n+1)) = false := by
        cases b : lookup x (memo read domain (n+1)) with
        | false => rfl
        | true =>
          obtain ⟨d,hit⟩ := (memo_exact read domain known (n+1) x).mp b
          rw [h] at hit
          cases hit
      rw [f]
      rfl
    | some d =>
      rw [(memo_exact read domain known (n+1) x).mpr ⟨d,h⟩]
      rfl

end Yulang.GeneralGeneratedDictionaryMemoCheck299
