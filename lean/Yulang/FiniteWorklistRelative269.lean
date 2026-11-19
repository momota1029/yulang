import Yulang.FiniteWorklist

namespace Yulang.FiniteWorklistRelative269
open FiniteWorklist (Path Invariant explore scan explore_cons)

variable {Vertex : Type}

def Closed (successors : Vertex → List Vertex) (scope : List Vertex) : Prop :=
 ∀ source ∈ scope, successors source ⊆ scope

theorem scope_exhausted [DecidableEq Vertex] (scope seen : List Vertex)
 (within : seen ⊆ scope) (distinct : seen.Nodup) (enough : scope.length ≤ seen.length)
 (target : Vertex) (allowed : target ∈ scope) : target ∈ seen := by
 by_cases has : target ∈ seen
 · exact has
 · exfalso
   have enlarged : (target :: seen).Nodup := List.nodup_cons.mpr ⟨has,distinct⟩
   have subset : (target :: seen) ⊆ scope := by
     intro vertex seenAt
     rcases List.mem_cons.mp seenAt with rfl | remaining
     · exact allowed
     · exact within remaining
   have impossible := enlarged.length_le_of_subset subset
   simp only [List.length_cons] at impossible
   omega

theorem explore_exact [DecidableEq Vertex] (successors : Vertex → List Vertex) (scope : List Vertex)
 (closed : Closed successors scope) (initial : Vertex) (started : initial ∈ scope)
 (capacity : Nat) (seen pending : List Vertex)
 (inv : Invariant successors initial seen pending) (seenIn : seen ⊆ scope) (todoIn : pending ⊆ scope)
 (enough : scope.length ≤ seen.length+capacity) (target : Vertex) :
 target ∈ explore successors capacity seen pending ↔ Path successors initial target := by
 induction capacity generalizing seen pending with
 | zero =>
   simp only [explore]
   refine ⟨inv.seen_sound target,fun path => ?_⟩
   exact scope_exhausted scope seen seenIn inv.distinct (by simpa using enough) target
     (FiniteWorklist.closed_path successors scope (fun src hs _ ht => closed src hs ht) path started)
 | succ capacity capacityIH =>
   induction pending generalizing seen with
   | nil =>
       simp only [explore,scan]
       have start : initial ∈ seen := inv.initial_present.resolve_right (by simp)
       have adjClosed : ∀ source ∈ seen, ∀ target ∈ successors source, target ∈ seen :=
         fun source hs target ht => (inv.frontier source hs target ht).resolve_right (by simp)
       exact ⟨inv.seen_sound target,fun p => FiniteWorklist.closed_path successors seen adjClosed p start⟩
   | cons fresh rest pendingIH =>
       have tailIn : rest ⊆ scope := fun _ h => todoIn (List.mem_cons_of_mem _ h)
       by_cases prior : fresh ∈ seen
       · rw [explore_cons,ite_eq_left prior]
         exact pendingIH seen (inv.skip prior) seenIn tailIn enough
       · rw [explore_cons,ite_eq_right prior]
         have freshIn := todoIn List.mem_cons_self
         apply capacityIH (fresh :: seen) (successors fresh ++ rest) (inv.visit prior)
         · intro vertex entry
           rcases List.mem_cons.mp entry with rfl | earlier
           · exact freshIn
           · exact seenIn earlier
         · intro vertex entry
           rcases List.mem_append.mp entry with next | later
           · exact closed fresh freshIn next
           · exact tailIn later
         · simp only [List.length_cons]
           omega

theorem reachable_exact [DecidableEq Vertex] (successors : Vertex → List Vertex) (scope : List Vertex)
 (closed : Closed successors scope) (start target : Vertex) (started : start ∈ scope) :
 target ∈ FiniteWorklist.reachable successors scope.length start ↔ Path successors start target := by
 apply explore_exact successors scope closed start started scope.length [] [start]
 · refine ⟨by simp,by simp,?_,by simp,by simp⟩
   intro x pending
   cases List.mem_singleton.mp pending
   exact .nil _
 · simp
 · intro x pending
   cases List.mem_singleton.mp pending
   exact started
 · simp

end Yulang.FiniteWorklistRelative269
