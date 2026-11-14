import Yulang.GeneralPatternVariableProvenance

/-! Normalization may leave joins for another observation, but every covered
result is already stable. This includes joins erased by record hiding. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralPatternCoveredResult
open GeneralDeclarationPatterns GeneralPatternNormalForm

def Prepared : Pattern → Prop
  | .var _ => True
  | .app _ arguments => ∀ p ∈ arguments, Prepared p
  | .variant _ payload => Prepared payload
  | .record label payload tail => Prepared payload ∧ Prepared tail ∧ label ∉ fields tail
  | .join first last => Prepared first ∧ Prepared last

theorem hide_prepared (label : Nat) (pattern : Pattern) (known : Prepared pattern) : Prepared (hide label pattern) := by
  cases pattern with
  | record key payload tail =>
    simp only [Prepared] at known
    by_cases same : label = key
    · simpa only [hide,same,ite_true] using hide_prepared label tail known.2.1
    · simp only [hide,same,ite_false,Prepared]
      refine ⟨known.1,hide_prepared label tail known.2.1,?_⟩
      rw [fields_hide]
      exact fun member => known.2.2 ((List.mem_filter.mp member).1)
  | _ => exact known

theorem variant_row (pattern : Pattern) (known : Prepared pattern)
    (found : variantRow pattern = some entries) : ∀ entry ∈ entries, Prepared entry.2 := by
  cases pattern with
  | variant tag payload => simp only [Prepared] at known; cases Option.some.inj found; intro entry member; cases List.mem_singleton.mp member; exact known
  | join first last =>
    simp only [Prepared] at known
    simp only [variantRow] at found
    cases one : variantRow first <;> simp only [one] at found
    · cases found
    · rename_i xs
      cases two : variantRow last <;> simp only [two] at found
      · cases found
      · rename_i ys
        cases Option.some.inj found
        intro entry member
        rcases List.mem_append.mp member with a | b
        · exact variant_row first known.1 one entry a
        · exact variant_row last known.2 two entry b
  | _ => cases found
  termination_by sizeOf pattern

theorem payload (first : Prepared a) (last : Prepared b) : Prepared (mergePayload a b) := by
  unfold mergePayload
  split
  · exact first
  · simpa only [Prepared] using (show Prepared a ∧ Prepared b from ⟨first,last⟩)

variable {entries : List (Nat × Pattern)} {tag : Nat}

theorem insert (known : Prepared p) (rest : ∀ entry ∈ entries, Prepared entry.2) :
    ∀ entry ∈ Variants.Merged.Raw.insert mergePayload tag p entries, Prepared entry.2 := by
  induction entries with
  | nil => intro entry member; cases List.mem_singleton.mp member; exact known
  | cons head tail ih =>
    simp only [Variants.Merged.Raw.insert]
    split
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact payload known (rest head (List.mem_cons_self ..))
      · exact rest entry (List.mem_cons_of_mem _ member)
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact rest head (List.mem_cons_self ..)
      · exact ih (fun entry member => rest entry (List.mem_cons_of_mem _ member)) entry member

theorem rows (known : ∀ entry ∈ entries, Prepared entry.2) :
    ∀ entry ∈ (Variants.Merged.normalize mergePayload entries).entries, Prepared entry.2 := by
  induction entries with
  | nil => intro entry member; cases member
  | cons head tail ih =>
    exact insert (known head (List.mem_cons_self ..))
      (ih (fun entry member => known entry (List.mem_cons_of_mem _ member)))

theorem row_pattern (entries : List (Nat × Pattern)) (known : ∀ entry ∈ entries, Prepared entry.2) : Prepared (rowPattern entries) := by
  cases entries with
  | nil => simp only [rowPattern, Prepared]; intro _ member; cases member
  | cons head tail =>
    cases tail with
    | nil => simp only [rowPattern, Prepared]; exact known head (List.mem_singleton_self _)
    | cons second rest =>
      simp only [rowPattern, Prepared]
      exact ⟨known head (List.mem_cons_self ..),
        row_pattern _ (fun entry member => known entry (List.mem_cons_of_mem _ member))⟩
  termination_by entries.length

theorem merged (first : Prepared a) (last : Prepared b) : Prepared (merge a b) := by
  unfold merge
  split
  · exact first
  · split
    · rename_i xs ys one two
      apply row_pattern
      intro entry member
      apply rows (entries := xs ++ ys) ?_ entry (List.mem_mergeSort.mp member)
      intro part present
      rcases List.mem_append.mp present with left | right
      · exact variant_row a first one part left
      · exact variant_row b last two part right
    · simpa only [Prepared] using (show Prepared a ∧ Prepared b from ⟨first,last⟩)

mutual
  theorem normalize_prepared (pattern : Pattern) : Prepared (normalize pattern) := by
    cases pattern with
    | var => simp only [normalize, Prepared]
    | app key arguments => simp only [normalize, Prepared]; exact args_prepared arguments
    | variant tag payload => simp only [normalize, Prepared]; exact normalize_prepared payload
    | record label payload tail =>
      simp only [normalize, Prepared]
      refine ⟨normalize_prepared payload,hide_prepared label _ (normalize_prepared tail),?_⟩
      rw [fields_hide]
      simp
    | join first last => exact merged (normalize_prepared first) (normalize_prepared last)
  theorem args_prepared (patterns : List Pattern) : ∀ p ∈ normalizeArgs patterns, Prepared p := by
    cases patterns with
    | nil => intro _ member; cases member
    | cons head tail =>
      intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact normalize_prepared head
      · exact args_prepared tail p member
end

mutual
  theorem prepared_normal (pattern : Pattern) (prepared : Prepared pattern) (complete : covered pattern = true) : Normal pattern := by
    cases pattern with
    | var => simp only [Normal]
    | app key arguments => simp only [Prepared] at prepared; simp only [Normal]; exact prepared_args_normal arguments prepared complete
    | variant tag payload => simp only [Prepared] at prepared; simp only [Normal]; exact prepared_normal payload prepared complete
    | record label payload tail =>
      simp only [Prepared] at prepared
      simp only [Normal]
      have parts := (Bool.and_eq_true ..).mp complete
      exact ⟨prepared_normal payload prepared.1 parts.1,prepared_normal tail prepared.2.1 parts.2,prepared.2.2⟩
    | join => cases complete
  theorem prepared_args_normal (patterns : List Pattern) (prepared : ∀ p ∈ patterns, Prepared p)
      (complete : coveredArgs patterns = true) : ∀ p ∈ patterns, Normal p := by
    cases patterns with
    | nil => intro _ member; cases member
    | cons head tail =>
      have parts := (Bool.and_eq_true ..).mp complete
      intro p member
      rcases List.mem_cons.mp member with equal | member
      · subst p
        exact prepared_normal head (prepared head (List.mem_cons_self ..)) parts.1
      · exact prepared_args_normal tail (fun p member => prepared p (List.mem_cons_of_mem _ member)) parts.2 p member
end

theorem covered_result_normal (pattern : Pattern) (complete : covered (normalize pattern) = true) : Normal (normalize pattern) :=
  prepared_normal _ (normalize_prepared pattern) complete

theorem covered_result_fixed (pattern : Pattern) (complete : covered (normalize pattern) = true) :
    normalize (normalize pattern) = normalize pattern := fixed _ (covered_result_normal pattern complete)

end Yulang.GeneralPatternCoveredResult
