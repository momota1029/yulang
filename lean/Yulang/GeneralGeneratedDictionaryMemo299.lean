import Yulang.GeneralGeneratedDictionaryFiniteCap299

namespace Yulang.GeneralGeneratedDictionaryMemo299
open CommonRoleOutermostResolver (Dictionary)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299 (all_left run_has_row)
open GeneralGeneratedDictionaryRankCheck299

def lookup (x : Nat) : List (Nat × Bool) → Bool
  | [] => false
  | (i,b)::rest => if x=i then b else lookup x rest

def stage (read : Read) (prev : Nat → Bool) (i : Nat) : Bool :=
  match read i with
  | none => false
  | some row => row.children.all prev

def memo (read : Read) (domain : List Nat) : Nat → List (Nat × Bool)
  | 0 => domain.map fun i => (i,false)
  | n+1 =>
    let prev := memo read domain n
    domain.map fun i => (i,stage read (fun j => lookup j prev) i)

theorem lookup_present (f : Nat → Bool) (domain : List Nat) (i : Nat)
    (present : i ∈ domain) :
    lookup i (domain.map (fun j => (j,f j))) = f i := by
  induction domain with
  | nil => cases present
  | cons j tail ih =>
    by_cases same : i=j
    · subst j; simp [lookup]
    · simp [lookup,same]
      rcases List.mem_cons.mp present with equal|mem
      · exact False.elim (same equal)
      · exact ih mem

theorem lookup_absent (f : Nat → Bool) (domain : List Nat) (i : Nat)
    (absent : i ∉ domain) :
    lookup i (domain.map (fun j => (j,f j))) = false := by
  induction domain with
  | nil => rfl
  | cons j tail ih =>
    have same : i ≠ j := fun h => absent (List.mem_cons.mpr (.inl h))
    have tailAbsent : i ∉ tail := fun h => absent (List.mem_cons.mpr (.inr h))
    simp [lookup,same,ih tailAbsent]

theorem stage_exact (read : Read) (n : Nat) (prev : Nat → Bool)
    (correct : ∀ j, prev j = true ↔ ∃ d, run read n j = some d) (i : Nat) :
    stage read prev i = true ↔ ∃ d, run read (n+1) i = some d := by
  cases hit : read i with
  | none =>
    simp [stage,hit,run]
  | some row =>
    constructor
    · intro ready
      have all := List.all_eq_true.mp (show row.children.all prev = true by
        simpa [stage,hit] using ready)
      obtain ⟨ds,hs⟩ := collect_exists (run read n) row.children
        (fun j mem => (correct j).mp (all j mem))
      exact ⟨.node row.key ds,by simp [run,hit,hs]⟩
    · rintro ⟨d,out⟩
      obtain ⟨r,ds,hr,all,shape⟩ := (run_exact _ _ _ _).mp out
      cases Option.some.inj (hr.symm.trans hit)
      simp only [stage,hit]
      exact List.all_eq_true.mpr (fun j mem => (correct j).mpr (all_left all j mem))

theorem memo_exact (read : Read) (domain : List Nat) (known : Known read domain)
    (n i : Nat) :
    lookup i (memo read domain n) = true ↔ ∃ d, run read n i = some d := by
  induction n generalizing i with
  | zero =>
    by_cases here : i ∈ domain
    · rw [memo,lookup_present _ _ _ here]
      simp [run]
    · rw [memo,lookup_absent _ _ _ here]
      simp [run]
  | succ n ih =>
    by_cases here : i ∈ domain
    · rw [memo,lookup_present _ _ _ here]
      exact stage_exact read n _ ih i
    · rw [memo,lookup_absent _ _ _ here]
      constructor
      · intro h; cases h
      · rintro ⟨d,found⟩
        obtain ⟨row,seen⟩ := run_has_row found
        exact False.elim (here (known i row seen))

def checkMemo (read : Read) (domain : List Nat) (cap : Nat) : Bool :=
  let all := memo read domain cap
  domain.all (fun i => lookup i all)

end Yulang.GeneralGeneratedDictionaryMemo299
