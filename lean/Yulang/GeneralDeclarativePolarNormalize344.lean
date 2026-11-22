import Yulang.GeneralDeclarativeCommitPort344
import Yulang.GeneralNominalCenteredHeadMatPatternSemantics

set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDeclarativePolarNormalize344
open GeneralDeclarationPatterns (Pattern Constructors normalize normalizeArgs hide merge mergePayload rowPattern variantRow)
open GeneralNominalInspection (Interpretation)
open GeneralNominalMaterialization (Mode)
open CommonNominalFullCarrier
open GeneralNominalMatchedAssembly (Aligned)
open GeneralNominalCenteredHeadMatCompilerSemantics (application algebra)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans record_congr variant_congr union_congr eqv_le)

def argMode (i : Interpretation) (mode : Mode) (name : Nat) : Mode :=
  if (i.primitives name).isSome then mode else .actual

mutual
  def eval (c : Constructors) (i : Interpretation) (variables : Mode → Nat → Ty) (mode : Mode) : Pattern → Ty
    | .var name => variables mode name
    | .app name args => application c i name (evals c i variables (argMode i mode name) args)
    | .record label payload tail => record label (eval c i variables mode payload) (eval c i variables mode tail)
    | .variant tag payload => variant tag (eval c i variables mode payload)
    | .join first last => .union (eval c i variables mode first) (eval c i variables mode last)
  def evals (c : Constructors) (i : Interpretation) (variables : Mode → Nat → Ty) (mode : Mode) : List Pattern → List Ty
    | [] => []
    | head :: tail => eval c i variables mode head :: evals c i variables mode tail
end

variable {c : Constructors} {i : Interpretation} {variables : Mode → Nat → Ty} {mode : Mode}

/- The earlier normalization proof at actual mode uses the same
record and tag algebra. Keep the mode parameter at each recursive
descent: only a nominal application's arguments switch to actual. -/
theorem hide_sound (label : Nat) (value : Ty) (pattern : Pattern) :
    Equivalent (record label value (eval c i variables mode pattern))
      (record label value (eval c i variables mode (hide label pattern))) := by
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
    Equivalent (variant tag (eval c i variables mode (mergePayload first last)))
      (.union (variant tag (eval c i variables mode first)) (variant tag (eval c i variables mode last))) := by
  unfold mergePayload
  split
  · rename_i same
    subst last
    exact ⟨(common_union_is_join ..).mp (subtype_refl _) |>.1,
      (common_union_is_join ..).mpr ⟨subtype_refl _,subtype_refl _⟩⟩
  · exact eqv_symm (GeneralNominalCommonBridge.variant_merge ..)

private def Upper (c : Constructors) (i : Interpretation) (variables : Mode → Nat → Ty) (mode : Mode) (row : List (Nat × Pattern)) (target : Ty) : Prop :=
  ∀ entry ∈ row, Subtype (variant entry.1 (eval c i variables mode entry.2)) target

private theorem upper_cons (entry : Nat × Pattern) (row : List (Nat × Pattern)) :
    Upper c i variables mode (entry :: row) target ↔
      Subtype (variant entry.1 (eval c i variables mode entry.2)) target ∧ Upper c i variables mode row target := by
  simp only [Upper,List.mem_cons,forall_eq_or_imp]

private theorem upper_append (first last : List (Nat × Pattern)) :
    Upper c i variables mode (first ++ last) target ↔
      Upper c i variables mode first target ∧ Upper c i variables mode last target := by
  simp only [Upper,List.mem_append,or_imp,forall_and]

private theorem upper_insert (tag : Nat) (payload : Pattern) (row : List (Nat × Pattern)) :
    Upper c i variables mode (Variants.Merged.Raw.insert mergePayload tag payload row) target ↔
      Subtype (variant tag (eval c i variables mode payload)) target ∧ Upper c i variables mode row target := by
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
    Upper c i variables mode (Variants.Merged.normalize mergePayload row).entries target ↔
      Upper c i variables mode row target := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Variants.Merged.normalize,upper_insert,upper_cons,ih]

private theorem upper_sorted (row : List (Nat × Pattern)) :
    Upper c i variables mode
      (row.mergeSort (fun a b => a.1 ≤ b.1)) target ↔ Upper c i variables mode row target := by
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
    Subtype (eval c i variables mode pattern) target ↔ Upper c i variables mode row target := by
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
    Subtype (eval c i variables mode (rowPattern row)) target ↔ Upper c i variables mode row target := by
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
    Equivalent (eval c i variables mode (merge first last))
      (.union (eval c i variables mode first) (eval c i variables mode last)) := by
  have bound (target : Ty) : Subtype (eval c i variables mode (merge first last)) target ↔
      Subtype (.union (eval c i variables mode first) (eval c i variables mode last)) target := by
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
  theorem normalize_sound (mode : Mode) (pattern : Pattern) :
      Equivalent (eval c i variables mode pattern) (eval c i variables mode (normalize pattern)) := by
    cases pattern with
    | var => exact eqv_refl _
    | app name arguments => exact (algebra c i).congruent name (normalizes_sound (argMode i mode name) arguments)
    | record label payload tail =>
        exact eqv_trans (record_congr label (normalize_sound mode payload) (normalize_sound mode tail)) (hide_sound ..)
    | variant tag payload => exact variant_congr tag (normalize_sound mode payload)
    | join first last =>
        exact eqv_trans (union_congr (normalize_sound mode first) (normalize_sound mode last)) (eqv_symm (merge_sound ..))
    termination_by sizeOf pattern
  theorem normalizes_sound (mode : Mode) (patterns : List Pattern) :
      Aligned Equivalent (evals c i variables mode patterns) (evals c i variables mode (normalizeArgs patterns)) := by
    cases patterns with
    | nil => exact .nil
    | cons head tail => exact .cons (normalize_sound mode head) (normalizes_sound mode tail)
    termination_by sizeOf patterns
end

end Yulang.GeneralDeclarativePolarNormalize344
