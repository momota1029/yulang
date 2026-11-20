import Yulang.CommonRoleOutermostResolver

namespace Yulang.GeneralGeneratedDictionaryRun299
open CommonRoleOutermostResolver (Dictionary All₂)

structure Entry where
  key : Nat
  children : List Nat
  deriving DecidableEq

abbrev Read := Nat → Option Entry

def collect (f : Nat → Option Dictionary) : List Nat → Option (List Dictionary)
  | [] => some []
  | x::xs => do
      let d ← f x
      let ds ← collect f xs
      return d::ds

theorem collect_exact (f : Nat → Option Dictionary) (xs : List Nat) (ds : List Dictionary) :
    collect f xs = some ds ↔ All₂ (fun x d => f x = some d) xs ds := by
  induction xs generalizing ds with
  | nil =>
    cases ds <;> constructor <;> intro h
    · exact .nil
    · rfl
    · cases h
    · cases h
  | cons x tail ih =>
    constructor
    · intro ok
      cases hx : f x with
      | none => simp [collect,hx] at ok
      | some d =>
        cases ht : collect f tail with
        | none => simp [collect,hx,ht] at ok
        | some rest =>
          simp only [collect,hx,ht,Pure.pure] at ok
          cases ok
          exact .cons hx ((ih _).mp ht)
    · intro ok
      cases ok with
      | cons h t => simp [collect,h,(ih _).mpr t]

theorem collect_exists (f : Nat → Option Dictionary) (xs : List Nat)
    (total : ∀ x ∈ xs, ∃ d, f x = some d) : ∃ ds, collect f xs = some ds := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    obtain ⟨d,hd⟩ := total x (by simp)
    obtain ⟨ds,hds⟩ := ih (fun z h => total z (by simp [h]))
    exact ⟨d::ds,by simp [collect,hd,hds]⟩

def run (read : Read) : Nat → Nat → Option Dictionary
  | 0,_ => none
  | n+1,x => do
      let row ← read x
      let ds ← collect (run read n) row.children
      return .node row.key ds

theorem run_exact (read : Read) (n x : Nat) (d : Dictionary) :
    run read (n+1) x = some d ↔ ∃ row ds, read x = some row ∧
      All₂ (fun child dict => run read n child = some dict) row.children ds ∧
      d = .node row.key ds := by
  constructor
  · intro h
    cases hr : read x with
    | none => simp [run,hr] at h
    | some row =>
      cases ht : collect (run read n) row.children with
      | none => simp [run,hr,ht] at h
      | some ds =>
        exact ⟨row,ds,rfl,(collect_exact _ _ _).mp ht,
          (by simpa [run,hr,ht] using h.symm)⟩
  · rintro ⟨row,ds,hr,all,rfl⟩
    simp [run,hr,(collect_exact _ _ _).mpr all]

def Ranked (read : Read) (rank : Nat → Nat) : Prop :=
  ∀ x row, read x = some row → ∀ child ∈ row.children, rank child < rank x

def Closed (read : Read) : Prop :=
  ∀ x row, read x = some row → ∀ child ∈ row.children, ∃ next, read child = some next

theorem total_with_fuel (read : Read) (rank : Nat → Nat) (decreases : Ranked read rank)
    (closed : Closed read) (n x : Nat) (enough : rank x < n)
    {row : Entry} (seen : read x = some row) : ∃ d, run read n x = some d := by
  induction n generalizing x row with
  | zero => omega
  | succ n ih =>
    obtain ⟨ds,fields⟩ := collect_exists (run read n) row.children (by
      intro child member
      obtain ⟨next,found⟩ := closed x row seen child member
      have lower := decreases x row seen child member
      exact ih child (by omega) found)
    exact ⟨.node row.key ds,by simp [run,seen,fields]⟩

theorem rank_suffices (read : Read) (rank : Nat → Nat) (decreases : Ranked read rank)
    (closed : Closed read) (x : Nat) {row : Entry} (seen : read x = some row) :
    ∃ d, run read (rank x + 1) x = some d :=
  total_with_fuel read rank decreases closed _ x (by omega) seen

end Yulang.GeneralGeneratedDictionaryRun299
