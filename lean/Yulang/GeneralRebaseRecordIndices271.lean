import Yulang.GeneralRebaseRecordOverwrite271

namespace Yulang.GeneralRebaseRecordIndices271
open GeneralRebaseRecordLookup271 (first)

/-- Whether the index is preceded by an already visible occurrence of
its label. The payloads themselves are irrelevant to this test. -/
def Shadowed (labels : List Nat) (i key : Nat) : Prop := key ∈ labels.take i

theorem first_at (keys : List Nat) (values : List α) (i key : Nat) (value : α)
 (located : keys[i]? = some key) (found : values[i]? = some value)
 (visible : ¬ Shadowed keys i key) :
 first key (keys.zip values) = some value := by
 induction i generalizing keys values with
 | zero =>
   cases keys <;> cases values <;> simp_all [first]
 | succ i ih =>
   cases keys with
   | nil => cases located
   | cons k rest =>
     cases values with
     | nil => cases found
     | cons v data =>
       have nk : key ≠ k := by
         intro eq
         apply visible
         exact List.mem_cons.mpr (Or.inl eq)
       have tail : ¬ Shadowed rest i key := by
         intro h
         apply visible
         exact List.mem_cons.mpr (Or.inr h)
       simpa only [List.zip_cons_cons,first,nk,ite_false] using ih rest data located found tail

theorem set_other (keys : List Nat) (values : List α) (i key other : Nat) (new : α)
 (located : keys[i]? = some key) (different : other ≠ key) :
 first other (keys.zip (values.set i new)) = first other (keys.zip values) := by
 induction i generalizing keys values with
 | zero =>
   cases keys with
   | nil => cases located
   | cons k rest =>
     have eq : k = key := Option.some.inj located
     subst k
     cases values <;> simp [first,different]
 | succ i ih =>
   cases keys with
   | nil => cases located
   | cons k rest =>
     cases values with
     | nil => rfl
     | cons v data =>
       by_cases hit : other = k
       · simp [first,hit]
       · simpa only [List.set_cons_succ,List.zip_cons_cons,first,hit,ite_false] using ih rest data located

theorem set_hidden (keys : List Nat) (values : List α) (i key : Nat) (new : α)
 (located : keys[i]? = some key) (shadowed : Shadowed keys i key) :
 ∀ other, first other (keys.zip (values.set i new)) = first other (keys.zip values) := by
 intro other
 by_cases different : other ≠ key
 · exact set_other keys values i key other new located different
 have same : other = key := Classical.byContradiction different
 subst other
 induction i generalizing keys values with
 | zero => cases shadowed
 | succ i ih =>
   cases keys with
   | nil => cases located
   | cons k rest =>
     cases values with
     | nil => rfl
     | cons v data =>
       by_cases hit : key = k
       · simp [first,hit]
       · have tail : Shadowed rest i key := (List.mem_cons.mp shadowed).resolve_left hit
         simpa only [List.set_cons_succ,List.zip_cons_cons,first,hit,ite_false] using ih rest data located tail

theorem index_visible (keys : List Nat) (i key : Nat)
 (located : keys[i]? = some key) (unique : keys.Nodup) :
 ¬ Shadowed keys i key := by
 induction i generalizing keys with
 | zero => intro missing; cases missing
 | succ i ih =>
   cases keys with
   | nil => cases located
   | cons k rest =>
     intro prior
     rcases List.mem_cons.mp prior with rfl | later
     · have notSeen := (List.nodup_cons.mp unique).1
       obtain ⟨valid,atValue⟩ := List.getElem?_eq_some_iff.mp (show rest[i]? = some key from located)
       exact notSeen (atValue ▸ List.getElem_mem valid)
     · exact ih rest located (List.nodup_cons.mp unique).2 later

end Yulang.GeneralRebaseRecordIndices271
