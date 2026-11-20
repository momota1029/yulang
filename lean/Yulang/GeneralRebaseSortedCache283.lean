import Yulang.GeneralRebaseProspectiveDelta283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSortedCache283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (SafeOrder)
open GeneralNominalAcyclicEquations237 (Descending Coherent)

abbrev Ascending (entries : List (Entry Nat)) : Prop :=
  entries.Pairwise (fun a b => a.1 < b.1)

def insert (row : Entry Nat) : List (Entry Nat) → List (Entry Nat)
  | [] => [row]
  | head :: tail =>
    if row.1 < head.1 then row :: head :: tail
    else if row.1 = head.1 then head :: tail
    else head :: insert row tail

theorem insert_mem (row e : Entry Nat) (before : List (Entry Nat))
    (coherence : ∀ older ∈ before, older.1 = row.1 → older.2 = row.2) :
    e ∈ insert row before ↔ e = row ∨ e ∈ before := by
  induction before with
  | nil => simp [insert]
  | cons head tail ih =>
    by_cases low : row.1 < head.1
    · simp [insert,low]
    by_cases equal : row.1 = head.1
    · have eq : head = row := Prod.ext equal.symm (coherence head List.mem_cons_self equal.symm)
      simp [insert,equal,eq]
    · simp only [insert,low,ite_false,equal,List.mem_cons,
        ih (fun other present => coherence other (List.mem_cons_of_mem _ present))]
      exact or_left_comm

theorem insert_asc (row : Entry Nat) (before : List (Entry Nat)) (order : Ascending before)
    (coherence : ∀ older ∈ before, older.1 = row.1 → older.2 = row.2) :
    Ascending (insert row before) := by
  induction before with
  | nil => simp [insert,Ascending]
  | cons head tail ih =>
    obtain ⟨smaller,previous⟩ := List.pairwise_cons.mp order
    by_cases low : row.1 < head.1
    · rw [insert,ite_eq_left low]
      exact List.pairwise_cons.mpr ⟨(fun other listed => by
        rcases List.mem_cons.mp listed with rfl|listed
        · exact low
        · exact Nat.lt_trans low (smaller other listed)),order⟩
    by_cases equal : row.1 = head.1
    · rw [insert,ite_eq_right low,ite_eq_left equal]; exact order
    · rw [insert,ite_eq_right low,ite_eq_right equal]
      have tailEq : ∀ older ∈ tail, older.1 = row.1 → older.2 = row.2 :=
        fun other present => coherence other (List.mem_cons_of_mem _ present)
      refine List.pairwise_cons.mpr ⟨?_,ih previous tailEq⟩
      intro other listed
      rcases (insert_mem row other tail tailEq).mp listed with rfl|member
      · omega
      · exact smaller other member

def push : List (Entry Nat) → List (Entry Nat) → List (Entry Nat)
  | [], cached => cached
  | row :: tail, cached => push tail (insert row cached)

theorem push_exact (delta cached : List (Entry Nat)) (before : Ascending cached)
    (coherence : Coherent (delta ++ cached)) :
    Ascending (push delta cached) ∧
      ∀ e, e ∈ push delta cached ↔ e ∈ delta ∨ e ∈ cached := by
  induction delta generalizing cached with
  | nil => exact ⟨before,by simp [push]⟩
  | cons row tail ih =>
    have same : ∀ older ∈ cached, older.1 = row.1 → older.2 = row.2 := by
      intro older listed hit
      exact coherence _ (List.mem_append_right _ listed) _ (List.mem_append_left _ List.mem_cons_self) hit
    have swapEq (e : Entry Nat) : e ∈ tail ++ insert row cached ↔ e ∈ (row :: tail) ++ cached := by
      rw [List.mem_append,List.mem_append,insert_mem row e cached same,List.mem_cons]
      exact ⟨fun h => h.elim (fun x => Or.inl (Or.inr x)) (fun h => h.elim (fun x => Or.inl (Or.inl x)) Or.inr),
        fun h => h.elim (fun h => h.elim (fun x => Or.inr (Or.inl x)) Or.inl) (fun x => Or.inr (Or.inr x))⟩
    have next := ih (insert row cached) (insert_asc row cached before same)
      (fun a one b two eq => coherence a ((swapEq a).mp one) b ((swapEq b).mp two) eq)
    refine ⟨next.1,?_⟩
    intro e
    exact (next.2 e).trans ((List.mem_append.symm.trans (swapEq e)).trans List.mem_append)

theorem safe (entries : List (Entry Nat)) (order : Ascending entries)
    (rank : Descending entries) : SafeOrder entries := by
  induction entries with
  | nil => trivial
  | cons row tail ih =>
    obtain ⟨later,asc⟩ := List.pairwise_cons.mp order
    refine ⟨?_,?_,?_,ih asc (fun r mem => rank r (List.mem_cons_of_mem _ mem))⟩
    · intro reads
      exact Nat.lt_irrefl _ (rank row List.mem_cons_self _
        (GeneralNominalOrderedSupport248.typed_reads_subset _ reads))
    · intro item listed hit
      exact Nat.lt_irrefl row.1 (hit ▸ later item listed)
    · intro item listed reads
      have weaker := later item listed
      have higher := rank row List.mem_cons_self _
        (GeneralNominalOrderedSupport248.typed_reads_subset _ reads)
      omega
end Yulang.GeneralRebaseSortedCache283
