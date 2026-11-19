import Std

namespace Yulang.GeneralRebaseFiniteSlices268

def slices : List α → List (List α)
 | [] => [[]]
 | head :: rest => slices rest ++ (slices rest).map (head :: ·)

theorem exact_slices (known chosen : List α) : chosen ∈ slices known ↔ chosen.Sublist known := by
 induction known generalizing chosen with
 | nil => simp [slices]
 | cons head tail ih =>
   simp only [slices,List.mem_append,List.mem_map,ih]
   constructor
   · rintro (skip | ⟨rest,listed,rfl⟩)
     · exact .cons _ skip
     · exact .cons_cons _ listed
   · intro contained
     cases contained with
     | cons _ h => exact Or.inl h
     | cons_cons _ h => exact Or.inr ⟨_,h,rfl⟩

/-- Even an unordered list containing arbitrary duplicate multiplicities
has a membership-equivalent member of the executable sublist enumeration. -/
theorem membership_cover (allowed : chosen ⊆ present) :
 ∃ representative ∈ slices present, ∀ a, a ∈ representative ↔ a ∈ chosen := by
 classical
 refine ⟨present.filter (fun a => decide (a ∈ chosen)),(exact_slices ..).mpr (List.filter_sublist ..),?_⟩
 intro a
 simp only [List.mem_filter,decide_eq_true_eq]
 exact ⟨fun both => both.2,fun yes => ⟨allowed yes,yes⟩⟩

end Yulang.GeneralRebaseFiniteSlices268
