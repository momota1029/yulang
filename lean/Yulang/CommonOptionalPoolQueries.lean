import Yulang.CommonOptionalPool

/-!
# A linear optional-bound inventory for the actual source pool

Each original required target contributes its own payload query and the same
label with top payload. The latter is the presence test used by default
decomposition. No Cartesian product of all labels and nodes is needed.
There are at most 2N queries and at most 5N+3 nodes after pool extension.

This establishes the finite inventory and its top-query closure. It does
not by itself prove that every future branch transition stays in it.
-/

namespace Yulang.CommonOptionalPoolQueries

open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonOptionalPool (Query)

variable {m : Nat}

def ofTerm (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) : List (Query pool) :=
  match term with
  | .required label payload =>
      [(label, some (pool.child _ member payload (by simp [subterms]))), (label, none)]
  | _ => []

def queries (pool : Pool m) : List (Query pool) :=
  pool.terms.attach.flatMap (fun term => ofTerm pool term.val term.property)

theorem ofTerm_length_le (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    (ofTerm pool term member).length ≤ 2 := by
  cases term <;> simp [ofTerm]

theorem queries_length_le (pool : Pool m) : (queries pool).length ≤ 2 * pool.size := by
  have bound (entries : List {term // term ∈ pool.terms}) :
      (entries.flatMap (fun term => ofTerm pool term.val term.property)).length ≤ 2 * entries.length := by
    induction entries with
    | nil => exact Nat.le_refl 0
    | cons term rest ih =>
        rw [List.flatMap_cons, List.length_append]
        have localBound := ofTerm_length_le pool term.val term.property
        simp only [List.length_cons]
        omega
  simpa only [queries, List.length_attach, Pool.size] using bound pool.terms.attach

theorem required_query (pool : Pool m) (label : Nat) (payload : TyTerm (Fin m))
    (member : TyTerm.required label payload ∈ pool.terms) :
    (label, some (pool.child _ member payload (by simp [subterms]))) ∈ queries pool := by
  apply List.mem_flatMap.mpr
  exact ⟨⟨.required label payload, member⟩, List.mem_attach _ _, List.mem_cons_self⟩

theorem required_top_query (pool : Pool m) (label : Nat) (payload : TyTerm (Fin m))
    (member : TyTerm.required label payload ∈ pool.terms) : (label, none) ∈ queries pool := by
  apply List.mem_flatMap.mpr
  exact ⟨⟨.required label payload, member⟩, List.mem_attach _ _,
    List.mem_cons_of_mem _ List.mem_cons_self⟩

/-- Every selected optional bound has its presence-test target in the very
same inventory. The payload type is never inspected to choose that target. -/
theorem top_query_closed (pool : Pool m) (query : Query pool) (member : query ∈ queries pool) :
    (query.1, none) ∈ queries pool := by
  obtain ⟨term, _, contributed⟩ := List.mem_flatMap.mp member
  rcases term with ⟨term, present⟩
  cases term with
  | required label payload =>
      have top := required_top_query pool label payload present
      rcases List.mem_cons.mp contributed with rfl | contributed
      · exact top
      · have same := List.mem_singleton.mp contributed
        subst query
        exact top
  | _ => cases contributed

/-- The pool extension is linear in the original shared-node count. -/
theorem extended_size_bound (pool : Pool m) :
    (CommonOptionalPool.extend pool (queries pool)).size ≤ 5 * pool.size + 3 := by
  have initial := CommonOptionalPool.size_bound pool (queries pool)
  have inventory := queries_length_le pool
  omega

end Yulang.CommonOptionalPoolQueries
