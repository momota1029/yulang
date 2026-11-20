import Yulang.GeneralSourceRoleCstReifyRow296

/-! Repeated identical observations in a computed occurrence trace can be
coalesced. Never coalesce two different replies for the same typed key. -/
namespace Yulang.GeneralSourceRoleCstCoalesce296
open GeneralSourceRoleCstNameCatalog296 (Catalog fiber member_of_fiber)
open GeneralSourceRoleCstNamingTrace295 (Trace)
open GeneralSourceRoleCstNamingRequests295 (Query)

def coalesce : Trace → Catalog
  | [] => []
  | row::rows => if row ∈ rows then coalesce rows else row::coalesce rows

theorem coalesce_mem (t : Trace) (p : Query × Option Nat) : p ∈ coalesce t ↔ p ∈ t := by
  induction t with
  | nil => rfl
  | cons row rows ih =>
    by_cases mem : row ∈ rows
    · simp only [coalesce,ite_eq_left mem,ih,List.mem_cons]
      exact ⟨Or.inr,fun h => h.elim (fun eq => eq ▸ mem) id⟩
    · simp [coalesce,mem,ih]

theorem coalesce_nodup (t : Trace) : (coalesce t).Nodup := by
  induction t with
  | nil => simp [coalesce]
  | cons row rows ih =>
    by_cases h : row ∈ rows
    · simpa [coalesce,h] using ih
    · rw [coalesce,ite_eq_right h,List.nodup_cons]
      exact ⟨fun m => h ((coalesce_mem rows row).mp m),ih⟩

theorem fiber_empty_of_no_pair (c : Catalog) (q : Query)
    (absent : ∀ v, (q,v) ∉ c) : fiber c q = [] := by
  cases h : fiber c q with
  | nil => rfl
  | cons a as =>
    have known : a ∈ fiber c q := by rw [h]; exact List.mem_cons_self
    exact False.elim (absent a ((member_of_fiber ..).mp known))

theorem singleton_fiber (c : Catalog) (q : Query) (v : Option Nat)
    (uniqueRows : c.Nodup) (seen : (q,v) ∈ c)
    (oneValue : ∀ x, (q,x) ∈ c → x = v) :
    fiber c q = [v] := by
  induction c with
  | nil => cases seen
  | cons hd tail ih =>
    rcases hd with ⟨k,a⟩
    have saved := List.nodup_cons.mp uniqueRows
    by_cases key : k = q
    · subst k
      have val := oneValue a List.mem_cons_self
      subst a
      have noTail (x : Option Nat) : (q,x) ∉ tail := by
        intro found
        have e := oneValue x (List.mem_cons_of_mem _ found)
        cases e
        exact saved.1 found
      have e := fiber_empty_of_no_pair tail q noTail
      unfold fiber at e ⊢
      simp [e]
    · have rest : (q,v) ∈ tail := by
        rcases List.mem_cons.mp seen with x | x
        · exact False.elim (key (Prod.mk.inj x).1.symm)
        · exact x
      have got := ih saved.2 rest (fun x m => oneValue x (List.mem_cons_of_mem _ m))
      simpa [fiber,key] using got

end Yulang.GeneralSourceRoleCstCoalesce296
