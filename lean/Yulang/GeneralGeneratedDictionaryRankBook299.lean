import Yulang.GeneralGeneratedDictionaryMemoCheck299

namespace Yulang.GeneralGeneratedDictionaryRankBook299
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299 (run_has_row)
open GeneralGeneratedDictionaryMemo299 (stage stage_exact)
open GeneralGeneratedDictionaryRankCheck299
open GeneralGeneratedDictionaryRankExists299
open GeneralGeneratedDictionaryMinFuel299
open GeneralGeneratedDictionaryAcc299 (monotone_fuel)

def get (i : Nat) : List (Nat × Option Nat) → Option Nat
  | [] => none
  | (j,k)::rest => if i=j then k else get i rest

def ranks (read : Read) (domain : List Nat) : Nat → List (Nat × Option Nat)
  | 0 => domain.map fun i => (i,none)
  | n+1 =>
    let prev := ranks read domain n
    domain.map fun i => (i,(get i prev).orElse (fun _ =>
      if stage read (fun j => (get j prev).isSome) i then some (n+1) else none))

theorem get_present (f : Nat → Option Nat) (domain : List Nat) (i : Nat) (present : i ∈ domain) :
    get i (domain.map (fun j => (j,f j))) = f i := by
  induction domain with
  | nil => cases present
  | cons j tail ih =>
    by_cases same : i=j
    · subst j; simp [get]
    · simp [get,same]
      rcases List.mem_cons.mp present with equal|mem
      · exact False.elim (same equal)
      · exact ih mem

theorem get_missing (f : Nat → Option Nat) (domain : List Nat) (i : Nat) (absent : i ∉ domain) :
    get i (domain.map (fun j => (j,f j))) = none := by
  induction domain with
  | nil => rfl
  | cons j tail ih =>
    have same : i ≠ j := fun h => absent (List.mem_cons.mpr (.inl h))
    have tailAbsent : i ∉ tail := fun h => absent (List.mem_cons.mpr (.inr h))
    simp [get,same,ih tailAbsent]

theorem earliest_at_cap (read : Read) (i cap : Nat) :
    (earliest read i cap).isSome = true ↔ ∃ d, run read cap i = some d := by
  constructor
  · intro present
    cases eq : earliest read i cap with
    | none => simp [eq] at present
    | some k =>
      obtain ⟨bound,⟨d,hit⟩,_⟩ := earliest_some read i cap k eq
      exact ⟨d,monotone_fuel read k cap i d bound hit⟩
  · intro hit
    obtain ⟨k,when⟩ := found_at_cap read i cap hit
    simp [when]

theorem earliest_outside (read : Read) (domain : List Nat) (known : Known read domain)
    (i n : Nat) (missing : i ∉ domain) : earliest read i n = none := by
  cases h : earliest read i n with
  | none => rfl
  | some k =>
    obtain ⟨_,⟨d,ok⟩,_⟩ := earliest_some read i n k h
    obtain ⟨row,hit⟩ := run_has_row ok
    exact False.elim (missing (known i row hit))

theorem ranks_exact (read : Read) (domain : List Nat) (known : Known read domain)
    (i n : Nat) : get i (ranks read domain n) = earliest read i n := by
  induction n generalizing i with
  | zero =>
    by_cases present : i ∈ domain
    · rw [ranks,get_present _ _ _ present]; rfl
    · rw [ranks,get_missing _ _ _ present]; rfl
  | succ n ih =>
    by_cases present : i ∈ domain
    · rw [ranks,get_present _ _ _ present]
      simp only [earliest,ih]
      congr 1
      funext _
      have exactStage := stage_exact read n (fun j => (earliest read j n).isSome)
        (fun j => earliest_at_cap read j n) i
      cases h : run read (n+1) i with
      | none =>
        have off : stage read (fun j => (earliest read j n).isSome) i = false := by
          cases seen : stage read (fun j => (earliest read j n).isSome) i with
          | false => rfl
          | true =>
            obtain ⟨d,ret⟩ := exactStage.mp seen
            rw [h] at ret
            cases ret
        rw [off]
        rfl
      | some d =>
        rw [exactStage.mpr ⟨d,h⟩]
        rfl
    · rw [ranks,get_missing _ _ _ present,earliest_outside read domain known i _ present]

def ready (read : Read) (domain : List Nat) (cap : Nat) : Bool :=
  let book := ranks read domain cap
  domain.all (fun i => (get i book).isSome)

def bookRank (read : Read) (domain : List Nat) (cap i : Nat) : Nat :=
  (get i (ranks read domain cap)).getD 0

theorem book_rank_exact (read : Read) (domain : List Nat) (known : Known read domain)
    (cap : Nat) : bookRank read domain cap = inferredRank read cap := by
  funext i
  simp [bookRank,inferredRank,ranks_exact read domain known]

theorem book_check (read : Read) (domain : List Nat) (known : Known read domain) (cap : Nat) :
    ready read domain cap = true ↔ check read domain cap = true := by
  constructor
  · intro pass
    apply List.all_eq_true.mpr
    intro i mem
    have first := List.all_eq_true.mp pass i mem
    change (get i (ranks read domain cap)).isSome = true at first
    rw [ranks_exact read domain known] at first
    obtain ⟨d,ok⟩ := (earliest_at_cap read i cap).mp first
    obtain ⟨row,found⟩ := run_has_row ok
    simp [found,first]
  · intro pass
    apply List.all_eq_true.mpr
    intro i mem
    obtain ⟨⟨_,_⟩,k,when⟩ := checked_at read domain cap pass mem
    change (get i (ranks read domain cap)).isSome = true
    simp [ranks_exact read domain known,when]

theorem book_ranked (read : Read) (domain : List Nat) (known : Known read domain)
    (cap : Nat) (pass : ready read domain cap = true) :
    Ranked read (bookRank read domain cap) := by
  rw [book_rank_exact read domain known cap]
  exact checked_ranked read domain cap known ((book_check read domain known cap).mp pass)

end Yulang.GeneralGeneratedDictionaryRankBook299
