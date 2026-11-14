import Yulang.GeneralNominalCenteredHeadMatGroundCover

/-! Pattern meanings on the general carrier. Record tails and variant rows
retain their ordinary constructor meanings; counting is a separate operation. -/
namespace Yulang.GeneralNominalCenteredHeadMatPatternSemantics
open GeneralDeclarationPatterns CommonNominalFullCarrier
open GeneralNominalMatchedAssembly (Aligned)
set_option linter.unusedSimpArgs false

structure Algebra where
  application : Nat → List Ty → Ty
  congruent : ∀ name {first last}, Aligned Equivalent first last →
    Equivalent (application name first) (application name last)

theorem eqv_refl (value : Ty) : Equivalent value value := ⟨subtype_refl _,subtype_refl _⟩
theorem eqv_symm (same : Equivalent first last) : Equivalent last first := ⟨same.2,same.1⟩
theorem eqv_trans (one : Equivalent first middle) (two : Equivalent middle last) : Equivalent first last :=
  ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩
theorem record_congr (label : Nat) (one : Equivalent first last) (two : Equivalent rest tail) :
    Equivalent (record label first rest) (record label last tail) :=
  ⟨common_record_mono label one.1 two.1,common_record_mono label one.2 two.2⟩
theorem variant_congr (tag : Nat) (same : Equivalent first last) : Equivalent (variant tag first) (variant tag last) :=
  ⟨(common_variant_iff ..).mpr same.1,(common_variant_iff ..).mpr same.2⟩
theorem union_congr (one : Equivalent first last) (two : Equivalent rest tail) :
    Equivalent (.union first rest) (.union last tail) :=
  ⟨common_union_mono one.1 two.1,common_union_mono one.2 two.2⟩
theorem eqv_le (same : Equivalent first last) (target) : Subtype first target ↔ Subtype last target :=
  ⟨fun below => subtype_trans same.2 below,fun below => subtype_trans same.1 below⟩

mutual
  def eval (algebra : Algebra) (variables : Nat → Ty) : Pattern → Ty
    | .var name => variables name
    | .app name arguments => algebra.application name (evals algebra variables arguments)
    | .record label payload tail => record label (eval algebra variables payload) (eval algebra variables tail)
    | .variant tag payload => variant tag (eval algebra variables payload)
    | .join first last => .union (eval algebra variables first) (eval algebra variables last)
  def evals (algebra : Algebra) (variables : Nat → Ty) : List Pattern → List Ty
    | [] => []
    | head :: tail => eval algebra variables head :: evals algebra variables tail
end

variable {algebra : Algebra} {variables : Nat → Ty}

theorem hide_sound (label : Nat) (value : Ty) (pattern : Pattern) :
    Equivalent (record label value (eval algebra variables pattern))
      (record label value (eval algebra variables (hide label pattern))) := by
  cases pattern with
  | record key payload tail =>
    by_cases equal : label = key
    · subst key
      simp only [hide,ite_true,eval]
      exact eqv_trans (GeneralNominalCommonBridge.shadow ..) (hide_sound label value tail)
    · simp only [hide,equal,ite_false,eval]
      exact eqv_trans (GeneralNominalCommonBridge.swap label key equal ..)
        (eqv_trans (record_congr key (eqv_refl _) (hide_sound label value tail))
          (eqv_symm (GeneralNominalCommonBridge.swap label key equal ..)))
  | _ => exact eqv_refl _

private theorem merged_payload (tag : Nat) (first last : Pattern) :
    Equivalent (variant tag (eval algebra variables (mergePayload first last)))
      (.union (variant tag (eval algebra variables first)) (variant tag (eval algebra variables last))) := by
  unfold mergePayload
  split
  · rename_i same
    subst last
    exact ⟨(common_union_is_join ..).mp (subtype_refl _) |>.1,
      (common_union_is_join ..).mpr ⟨subtype_refl _,subtype_refl _⟩⟩
  · exact eqv_symm (GeneralNominalCommonBridge.variant_merge ..)

private def Upper (algebra : Algebra) (variables : Nat → Ty) (row : List (Nat × Pattern)) (target : Ty) : Prop :=
  ∀ entry ∈ row, Subtype (variant entry.1 (eval algebra variables entry.2)) target

private theorem upper_cons (entry : Nat × Pattern) (row : List (Nat × Pattern)) :
    Upper algebra variables (entry :: row) target ↔
      Subtype (variant entry.1 (eval algebra variables entry.2)) target ∧ Upper algebra variables row target := by
  simp only [Upper,List.mem_cons,forall_eq_or_imp]

private theorem upper_append (first last : List (Nat × Pattern)) :
    Upper algebra variables (first ++ last) target ↔
      Upper algebra variables first target ∧ Upper algebra variables last target := by
  simp only [Upper,List.mem_append,or_imp,forall_and]

private theorem upper_insert (tag : Nat) (payload : Pattern) (row : List (Nat × Pattern)) :
    Upper algebra variables (Variants.Merged.Raw.insert mergePayload tag payload row) target ↔
      Subtype (variant tag (eval algebra variables payload)) target ∧ Upper algebra variables row target := by
  induction row with
  | nil => simp [Variants.Merged.Raw.insert,Upper]
  | cons entry rest ih =>
    obtain ⟨key,value⟩ := entry
    by_cases same : tag = key
    · subst key
      simp only [Variants.Merged.Raw.insert,ite_true,upper_cons]
      rw [eqv_le (merged_payload tag payload value),common_union_is_join]
      exact and_assoc
    · simp only [Variants.Merged.Raw.insert,same,ite_false,upper_cons,ih]
      exact and_left_comm

private theorem upper_normalize (row : List (Nat × Pattern)) :
    Upper algebra variables (Variants.Merged.normalize mergePayload row).entries target ↔
      Upper algebra variables row target := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Variants.Merged.normalize,upper_insert,upper_cons,ih]

private theorem upper_sorted (row : List (Nat × Pattern)) :
    Upper algebra variables
      (row.mergeSort (fun a b => a.1 ≤ b.1)) target ↔ Upper algebra variables row target := by
  simp only [Upper,List.mem_mergeSort]

private theorem variant_row_nonempty (pattern : Pattern) (found : variantRow pattern = some row) : row ≠ [] := by
  cases pattern with
  | variant => cases Option.some.inj found; simp
  | join first last =>
      cases one : variantRow first <;> simp only [variantRow,one,Option.bind_none,Option.bind_some] at found
      · cases found
      · cases two : variantRow last <;> simp only [two,Option.bind_none,Option.bind_some,Option.pure_def] at found
        · cases found
        · cases Option.some.inj found
          exact List.append_ne_nil_of_left_ne_nil (variant_row_nonempty first one) _
  | _ => cases found

private theorem variant_row_below (pattern : Pattern) (found : variantRow pattern = some row) :
    Subtype (eval algebra variables pattern) target ↔ Upper algebra variables row target := by
  cases pattern with
  | variant tag payload => cases Option.some.inj found; simp [eval,Upper]
  | join first last =>
      cases one : variantRow first <;> simp only [variantRow,one,Option.bind_none,Option.bind_some] at found
      · cases found
      · cases two : variantRow last <;> simp only [two,Option.bind_none,Option.bind_some,Option.pure_def] at found
        · cases found
        · cases Option.some.inj found
          exact (common_union_is_join ..).trans
            ((and_congr (variant_row_below first one) (variant_row_below last two)).trans (upper_append _ _).symm)
  | _ => cases found

private theorem row_pattern_below (row : List (Nat × Pattern)) (nonempty : row ≠ []) :
    Subtype (eval algebra variables (rowPattern row)) target ↔ Upper algebra variables row target := by
  cases row with
  | nil => exact False.elim (nonempty rfl)
  | cons entry rest =>
      cases rest with
      | nil => simp [rowPattern,eval,Upper]
      | cons next rest =>
          exact (common_union_is_join ..).trans
            ((and_congr Iff.rfl (row_pattern_below (next :: rest) (by simp))).trans (upper_cons _ _).symm)

private theorem normalized_nonempty (row : List (Nat × Pattern)) (nonempty : row ≠ []) :
    (Variants.Merged.normalize mergePayload row).entries ≠ [] := by
  obtain ⟨entry,member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have present := (Variants.Merged.tags_normalize mergePayload entry.1 row).mpr (List.mem_map.mpr ⟨entry,member,rfl⟩)
  intro empty
  rw [empty] at present
  cases present

theorem merge_sound (first last : Pattern) :
    Equivalent (eval algebra variables (merge first last))
      (.union (eval algebra variables first) (eval algebra variables last)) := by
  have bound (target : Ty) : Subtype (eval algebra variables (merge first last)) target ↔
      Subtype (.union (eval algebra variables first) (eval algebra variables last)) target := by
    unfold merge
    split
    · rename_i same
      subst last
      simp only [common_union_is_join,and_self]
    · cases one : variantRow first <;> cases two : variantRow last
      all_goals try exact Iff.rfl
      rename_i left right
      have nonempty := normalized_nonempty (left ++ right)
        (List.append_ne_nil_of_left_ne_nil (variant_row_nonempty first one) _)
      rw [row_pattern_below _ (by
        intro empty
        apply nonempty
        apply List.eq_nil_of_length_eq_zero
        simpa only [List.length_mergeSort,List.length_nil] using congrArg List.length empty),upper_sorted,upper_normalize,
        upper_append,← variant_row_below first one,← variant_row_below last two,common_union_is_join]
  exact ⟨(bound _).mpr (subtype_refl _),(bound _).mp (subtype_refl _)⟩

mutual
  theorem normalize_sound (pattern : Pattern) :
      Equivalent (eval algebra variables pattern) (eval algebra variables (normalize pattern)) := by
    cases pattern with
    | var => exact eqv_refl _
    | app name arguments => exact algebra.congruent name (normalizes_sound arguments)
    | record label payload tail =>
        exact eqv_trans (record_congr label (normalize_sound payload) (normalize_sound tail)) (hide_sound ..)
    | variant tag payload => exact variant_congr tag (normalize_sound payload)
    | join first last =>
        exact eqv_trans (union_congr (normalize_sound first) (normalize_sound last)) (eqv_symm (merge_sound ..))
    termination_by sizeOf pattern
  theorem normalizes_sound (patterns : List Pattern) :
      Aligned Equivalent (evals algebra variables patterns) (evals algebra variables (normalizeArgs patterns)) := by
    cases patterns with
    | nil => exact .nil
    | cons head tail => exact .cons (normalize_sound head) (normalizes_sound tail)
    termination_by sizeOf patterns
end

end Yulang.GeneralNominalCenteredHeadMatPatternSemantics
