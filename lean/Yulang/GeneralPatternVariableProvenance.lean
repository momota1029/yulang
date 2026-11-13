import Yulang.GeneralPatternNormalForm

/-! Normalization cannot create a declaration variable. This connects the
lexical output-only restriction to normalized child templates. -/
namespace Yulang.GeneralPatternVariableProvenance
open GeneralDeclarationPatterns

def Uses (allowed : Nat → Prop) (pattern : Pattern) : Prop := ∀ name ∈ pattern.variables, allowed name

variable {allowed : Nat → Prop} {entries : List (Nat × Pattern)} {tag : Nat}

theorem hide_uses (known : Uses allowed pattern) : Uses allowed (hide label pattern) := by
  cases pattern with
  | record key payload tail =>
    have first : Uses allowed payload := fun name member => known name (List.mem_append_left _ member)
    have last : Uses allowed tail := fun name member => known name (List.mem_append_right _ member)
    by_cases same : label = key
    · simpa only [hide,same,ite_true] using hide_uses last
    · simp only [hide,same,ite_false]
      intro name member
      rcases List.mem_append.mp member with one | two
      · exact first name one
      · exact hide_uses last name two
  | _ => exact known

theorem variant_row_uses (pattern : Pattern) {entries : List (Nat × Pattern)} (known : Uses allowed pattern)
    (found : variantRow pattern = some entries) : ∀ entry ∈ entries, Uses allowed entry.2 := by
  cases pattern with
  | variant tag payload => cases Option.some.inj found; intro entry member; cases List.mem_singleton.mp member; exact known
  | join first last =>
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
        · exact variant_row_uses first (fun name member => known name (List.mem_append_left _ member)) one entry a
        · exact variant_row_uses last (fun name member => known name (List.mem_append_right _ member)) two entry b
  | _ => cases found
  termination_by sizeOf pattern

theorem payload_uses (first : Uses allowed a) (last : Uses allowed b) : Uses allowed (mergePayload a b) := by
  unfold mergePayload
  split
  · exact first
  · intro name member
    rcases List.mem_append.mp member with a | b
    · exact first name a
    · exact last name b

theorem insert_uses (known : Uses allowed payload) (rest : ∀ entry ∈ entries, Uses allowed entry.2) :
    ∀ entry ∈ Variants.Merged.Raw.insert mergePayload tag payload entries, Uses allowed entry.2 := by
  induction entries with
  | nil => intro entry member; cases List.mem_singleton.mp member; exact known
  | cons head tail ih =>
    simp only [Variants.Merged.Raw.insert]
    split
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact payload_uses known (rest head (List.mem_cons_self ..))
      · exact rest entry (List.mem_cons_of_mem _ member)
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact rest head (List.mem_cons_self ..)
      · exact ih (fun entry member => rest entry (List.mem_cons_of_mem _ member)) entry member

theorem rows_uses (known : ∀ entry ∈ entries, Uses allowed entry.2) :
    ∀ entry ∈ (Variants.Merged.normalize mergePayload entries).entries, Uses allowed entry.2 := by
  induction entries with
  | nil => intro entry member; cases member
  | cons head tail ih =>
    exact insert_uses (known head (List.mem_cons_self ..))
      (ih (fun entry member => known entry (List.mem_cons_of_mem _ member)))

theorem row_pattern_uses (entries : List (Nat × Pattern)) (known : ∀ entry ∈ entries, Uses allowed entry.2) : Uses allowed (rowPattern entries) := by
  cases entries with
  | nil => intro name member; cases member
  | cons head tail =>
    cases tail with
    | nil => exact known head (List.mem_singleton_self _)
    | cons second rest =>
      intro name member
      rcases List.mem_append.mp member with first | last
      · exact known head (List.mem_cons_self ..) name first
      · exact row_pattern_uses _ (fun entry member => known entry (List.mem_cons_of_mem _ member)) name last
  termination_by entries.length

theorem merge_uses (first : Uses allowed a) (last : Uses allowed b) : Uses allowed (merge a b) := by
  unfold merge
  split
  · exact first
  · split
    · rename_i xs ys one two
      apply row_pattern_uses
      intro entry member
      apply rows_uses (allowed := allowed) (entries := xs ++ ys) ?_ entry (List.mem_mergeSort.mp member)
      intro part present
      rcases List.mem_append.mp present with left | right
      · exact variant_row_uses a first one part left
      · exact variant_row_uses b last two part right
    · intro name member
      rcases List.mem_append.mp member with a | b
      · exact first name a
      · exact last name b

mutual
  theorem normalize_uses (pattern : Pattern) (known : Uses allowed pattern) : Uses allowed (normalize pattern) := by
    cases pattern with
    | var => exact known
    | app key arguments => exact normalize_args_uses arguments known
    | variant tag payload => exact normalize_uses payload known
    | record label payload tail =>
      have first := normalize_uses payload (fun name member => known name (List.mem_append_left _ member))
      have last := hide_uses (label := label) (normalize_uses tail (fun name member => known name (List.mem_append_right _ member)))
      intro name member
      rcases List.mem_append.mp member with a | b
      · exact first name a
      · exact last name b
    | join first last =>
      exact merge_uses (normalize_uses first (fun name member => known name (List.mem_append_left _ member)))
        (normalize_uses last (fun name member => known name (List.mem_append_right _ member)))
  theorem normalize_args_uses (patterns : List Pattern) (known : ∀ name ∈ variablesArgs patterns, allowed name) :
      ∀ name ∈ variablesArgs (normalizeArgs patterns), allowed name := by
    cases patterns with
    | nil => exact known
    | cons head tail =>
      intro name member
      rcases List.mem_append.mp member with a | b
      · exact normalize_uses head (fun name member => known name (List.mem_append_left _ member)) name a
      · exact normalize_args_uses tail (fun name member => known name (List.mem_append_right _ member)) name b
end

theorem normalize_variables (pattern : Pattern) : (normalize pattern).variables ⊆ pattern.variables :=
  normalize_uses pattern (fun _ member => member)

theorem normalize_args_variables (patterns : List Pattern) : variablesArgs (normalizeArgs patterns) ⊆ variablesArgs patterns :=
  normalize_args_uses patterns (fun _ member => member)

theorem needed_input (packet : GeneralNominalSaturationState.Packet roles)
    (needed : GeneralNominalSharedCaptures.Needed packet name) : name ∉ packet.declaration.outputNames := by
  obtain ⟨clause,present,member⟩ := needed
  exact fun output => packet.checked.outputOnly.2 clause present name output (normalize_args_variables clause.arguments member)

end Yulang.GeneralPatternVariableProvenance
