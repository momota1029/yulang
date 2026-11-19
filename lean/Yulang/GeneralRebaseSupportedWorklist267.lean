import Yulang.FiniteWorklist

namespace Yulang.GeneralRebaseSupportedWorklist267
open FiniteWorklist
variable {Vertex : Type}

/-- A finite locally closed support, not a finite ambient type, suffices for
the existing executable worklist. The closure witness is used only in proofs. -/
theorem path_supported (next : Vertex → List Vertex) (support : List Vertex)
 (closed : ∀ a ∈ support, next a ⊆ support)
 (path : Path next a b) (start : a ∈ support) : b ∈ support :=
 closed_path next support (fun x hx _ hy => closed x hx hy) path start

theorem saturated (support seen : List Vertex) (contained : seen ⊆ support)
 (distinct : seen.Nodup) (full : support.length ≤ seen.length) : support ⊆ seen := by
 intro x inSupport
 by_cases present : x ∈ seen
 · exact present
 · have nodup := List.nodup_cons.mpr ⟨present,distinct⟩
   have included : x :: seen ⊆ support := by
     intro y present
     rcases List.mem_cons.mp present with rfl | member
     · exact inSupport
     · exact contained member
   have bound := nodup.length_le_of_subset included
   simp only [List.length_cons] at bound
   omega

variable [DecidableEq Vertex]

theorem exact_with_invariant (next : Vertex → List Vertex) (support : List Vertex)
 (closed : ∀ a ∈ support, next a ⊆ support) (start : initial ∈ support)
 (capacity : Nat) (seen pending : List Vertex)
 (invariant : Invariant next initial seen pending)
 (enough : support.length ≤ seen.length + capacity) (target : Vertex) :
 target ∈ explore next capacity seen pending ↔ Path next initial target := by
 induction capacity generalizing seen pending with
 | zero =>
   exact ⟨invariant.seen_sound target,fun path =>
     saturated support seen (fun v hv => path_supported next support closed (invariant.seen_sound v hv) start)
       invariant.distinct (by simpa using enough) (path_supported next support closed path start)⟩
 | succ capacity capacityIH =>
   induction pending generalizing seen with
   | nil =>
     simp only [explore,scan]
     have initialSeen : initial ∈ seen := invariant.initial_present.resolve_right (by simp)
     have allSeen : ∀ source ∈ seen, ∀ dest ∈ next source, dest ∈ seen :=
       fun source member dest edge => (invariant.frontier source member dest edge).resolve_right (by simp)
     exact ⟨invariant.seen_sound target,fun path => closed_path next seen allSeen path initialSeen⟩
   | cons current rest pendingIH =>
     by_cases known : current ∈ seen
     · simp only [explore_cons,known,↓reduceIte]
       exact pendingIH seen (invariant.skip known) enough
     · simp only [explore_cons,known,↓reduceIte]
       apply capacityIH (current :: seen) (next current ++ rest) (invariant.visit known)
       simp only [List.length_cons]
       omega

theorem reachable_exact (next : Vertex → List Vertex) (support : List Vertex)
 (closed : ∀ a ∈ support, next a ⊆ support) (start : initial ∈ support)
 (target : Vertex) :
 target ∈ reachable next support.length initial ↔ Path next initial target := by
 apply exact_with_invariant next support closed start support.length [] [initial]
 · refine ⟨by simp,by simp,?_,by simp,by simp⟩
   intro vertex member
   cases List.mem_singleton.mp member
   exact .nil _
 · simp

end Yulang.GeneralRebaseSupportedWorklist267
