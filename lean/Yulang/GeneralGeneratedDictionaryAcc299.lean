import Yulang.GeneralGeneratedDictionaryScope299

namespace Yulang.GeneralGeneratedDictionaryAcc299
open CommonRoleOutermostResolver (All₂ Dictionary Child)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299
open B4Target (Vocabulary)
open B4TargetV8

def Edge (read : Read) (child current : Nat) : Prop :=
  ∃ row, read current = some row ∧ child ∈ row.children

theorem step_fuel (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) : run read (n+1) x = some d := by
  induction n generalizing x d with
  | zero => cases hit
  | succ n ih =>
    obtain ⟨row,ds,readRow,all,rfl⟩ := (run_exact _ _ _ _).mp hit
    apply (run_exact _ _ _ _).mpr
    refine ⟨row,ds,readRow,?_,rfl⟩
    simpa only [List.map_id,id_eq] using map_all id (fun a d h => ih a d h) all

theorem monotone_fuel (read : Read) (n m x : Nat) (d : Dictionary)
    (leq : n ≤ m) (hit : run read n x = some d) : run read m x = some d := by
  induction m with
  | zero => cases Nat.eq_zero_of_le_zero leq; exact hit
  | succ k ih =>
    by_cases equal : n = k+1
    · simpa [equal] using hit
    · exact step_fuel read k x d (ih (by omega))

theorem child_sound {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}
    {read : Read} {decode : Nat → v.Demand}
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    {x a : Nat} (edge : Edge read a x) : Child (Local b r s) (decode a) (decode x) := by
  obtain ⟨row,hit,member⟩ := edge
  exact ⟨row.key,_,faith x row hit,List.mem_map.mpr ⟨a,member,rfl⟩⟩

theorem pull_accessibility {α β} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (sound : ∀ a x, R a x → S (f a) (f x))
    (y : β) (marked : Acc S y) : ∀ x, f x = y → Acc R x := by
  induction marked with
  | intro y pred ih =>
    intro x eq
    apply Acc.intro
    intro sub edge
    exact ih (f sub) (eq ▸ sound sub x edge) sub rfl

theorem source_accessible {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}
    {read : Read} {decode : Nat → v.Demand}
    (faith : Faithful (b:=b) (r:=r) (s:=s) read decode)
    (x : Nat) (acc : Acc (Child (Local b r s)) (decode x)) : Acc (Edge read) x :=
  pull_accessibility decode (fun _ _ edge => child_sound faith edge) _ acc x rfl

theorem success_accessible (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) : Acc (Edge read) x := by
  induction n generalizing x d with
  | zero => cases hit
  | succ n ih =>
    obtain ⟨row,ds,readRow,all,_⟩ := (run_exact _ _ _ _).mp hit
    apply Acc.intro
    rintro child ⟨other,also,member⟩
    have same := Option.some.inj (also.symm.trans readRow)
    subst other
    obtain ⟨p,seen⟩ := all_left all child member
    exact ih child p seen

theorem common_fuel (read : Read) (children : List Nat)
    (each : ∀ c ∈ children, ∃ n dc, run read n c = some dc) :
    ∃ n, ∀ c ∈ children, ∃ dc, run read n c = some dc := by
  induction children with
  | nil => exact ⟨0,by intro c no; cases no⟩
  | cons root tail ih =>
    obtain ⟨a,da,ha⟩ := each root (by simp)
    obtain ⟨b,hb⟩ := ih (fun c mem => each c (by simp [mem]))
    refine ⟨max a b,?_⟩
    intro c found
    rcases List.mem_cons.mp found with rfl | rest
    · exact ⟨da,monotone_fuel read a _ _ da (Nat.le_max_left _ _) ha⟩
    · obtain ⟨d,hd⟩ := hb c rest
      exact ⟨d,monotone_fuel read b _ _ d (Nat.le_max_right _ _) hd⟩

theorem accessible_success (read : Read) (closed : Closed read) (x : Nat)
    (acc : Acc (Edge read) x) :
    ∀ row, read x = some row → ∃ n d, run read n x = some d := by
  induction acc with
  | intro x pred ih =>
    intro row hit
    have each : ∀ c ∈ row.children, ∃ n dc, run read n c = some dc := by
      intro c mem
      obtain ⟨childRow,childHit⟩ := closed x row hit c mem
      exact ih c ⟨row,hit,mem⟩ childRow childHit
    obtain ⟨n,n_ok⟩ := common_fuel read row.children each
    obtain ⟨ds,produced⟩ := collect_exists (run read n) row.children n_ok
    exact ⟨n+1,.node row.key ds,by simp [run,hit,produced]⟩

theorem iff_accessible (read : Read) (closed : Closed read) (x : Nat)
    {row : Entry} (hit : read x = some row) :
    (∃ n d, run read n x = some d) ↔ Acc (Edge read) x := by
  exact ⟨fun ⟨n,d,ok⟩ => success_accessible read n x d ok,
    fun acc => accessible_success read closed x acc row hit⟩

end Yulang.GeneralGeneratedDictionaryAcc299
