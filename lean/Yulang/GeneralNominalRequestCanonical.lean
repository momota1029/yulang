import Yulang.GeneralNominalRequestTemplates

/-! Record normalization is canonical independently of coverage. Residual
joins can stay unsupported while their supported surrounding tests are valid. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalRequestCanonical
open GeneralDeclarationPatterns GeneralPatternNormalForm GeneralNominalInspection
open GeneralNominalSchemaVocabulary GeneralNominalReadbackFunctionality
open GeneralNominalRequestTemplates

def Tidy : Pattern → Prop
  | .var _ => True
  | .app _ arguments => ∀ pattern ∈ arguments, Tidy pattern
  | .variant _ payload => Tidy payload
  | .record label payload tail => Tidy payload ∧ Tidy tail ∧ label ∉ fields tail
  | .join first last => Tidy first ∧ Tidy last

theorem tidy_hide (label : Nat) (pattern : Pattern) (tidy : Tidy pattern) : Tidy (hide label pattern) := by
  cases pattern with
  | record key payload tail =>
    simp only [Tidy] at tidy
    by_cases same : label = key
    · simpa only [hide,same,ite_true] using tidy_hide label tail tidy.2.1
    · simp only [hide,same,ite_false,Tidy]
      exact ⟨tidy.1,tidy_hide label tail tidy.2.1,by
        rw [fields_hide]; exact fun h => tidy.2.2 (List.mem_filter.mp h).1⟩
  | _ => exact tidy

theorem tidy_variant_row (pattern : Pattern) (tidy : Tidy pattern)
    (found : variantRow pattern = some entries) : ∀ entry ∈ entries, Tidy entry.2 := by
  cases pattern with
  | variant tag payload =>
    simp only [Tidy] at tidy
    cases found
    intro entry member; cases List.mem_singleton.mp member; exact tidy
  | join first last =>
    simp only [Tidy] at tidy
    simp only [variantRow] at found
    cases one : variantRow first <;> simp only [one] at found
    · cases found
    · cases two : variantRow last <;> simp only [two] at found
      · cases found
      · cases found
        intro entry member
        rcases List.mem_append.mp member with h | h
        · exact tidy_variant_row first tidy.1 one entry h
        · exact tidy_variant_row last tidy.2 two entry h
  | _ => cases found

theorem tidy_payload (first : Tidy a) (last : Tidy b) : Tidy (mergePayload a b) := by
  unfold mergePayload; split
  · exact first
  · simp only [Tidy]; exact ⟨first,last⟩

theorem tidy_insert {entries : List (Nat × Pattern)} {tag : Nat} (known : Tidy payload) (rest : ∀ entry ∈ entries, Tidy entry.2) :
    ∀ entry ∈ Variants.Merged.Raw.insert mergePayload tag payload entries, Tidy entry.2 := by
  induction entries with
  | nil => intro entry member; cases List.mem_singleton.mp member; exact known
  | cons head tail ih =>
    simp only [Variants.Merged.Raw.insert]
    split
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact tidy_payload known (rest head (List.mem_cons_self ..))
      · exact rest entry (List.mem_cons_of_mem _ member)
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact rest head (List.mem_cons_self ..)
      · exact ih (fun entry member => rest entry (List.mem_cons_of_mem _ member)) entry member

theorem tidy_rows {entries : List (Nat × Pattern)} (known : ∀ entry ∈ entries, Tidy entry.2) :
    ∀ entry ∈ (Variants.Merged.normalize mergePayload entries).entries, Tidy entry.2 := by
  induction entries with
  | nil => intro entry member; cases member
  | cons head tail ih =>
    exact tidy_insert (known head (List.mem_cons_self ..))
      (ih (fun entry member => known entry (List.mem_cons_of_mem _ member)))

theorem tidy_row_pattern (entries : List (Nat × Pattern))
    (known : ∀ entry ∈ entries, Tidy entry.2) : Tidy (rowPattern entries) := by
  cases entries with
  | nil => simp only [rowPattern,Tidy,List.not_mem_nil,false_implies,implies_true]
  | cons head tail =>
    cases tail with
    | nil => simpa only [rowPattern,Tidy] using known head (List.mem_singleton_self _)
    | cons second rest =>
      simp only [rowPattern,Tidy]
      exact ⟨known head (List.mem_cons_self ..),
        tidy_row_pattern _ (fun entry member => known entry (List.mem_cons_of_mem _ member))⟩
  termination_by entries.length

theorem tidy_merge (first : Tidy a) (last : Tidy b) : Tidy (merge a b) := by
  unfold merge
  split
  · exact first
  · split
    · rename_i xs ys one two
      apply tidy_row_pattern
      intro entry member
      apply tidy_rows (entries := xs ++ ys) ?_ entry (List.mem_mergeSort.mp member)
      intro part present
      rcases List.mem_append.mp present with left | right
      · exact tidy_variant_row a first one part left
      · exact tidy_variant_row b last two part right
    · simp only [Tidy]; exact ⟨first,last⟩

mutual
  theorem normalized_tidy (pattern : Pattern) : Tidy (normalize pattern) := by
    cases pattern with
    | var => simp only [normalize,Tidy]
    | app key arguments => simpa only [normalize,Tidy] using normalized_args_tidy arguments
    | variant tag payload => simpa only [normalize,Tidy] using normalized_tidy payload
    | record label payload tail =>
      simp only [normalize,Tidy]
      exact ⟨normalized_tidy payload,tidy_hide label _ (normalized_tidy tail),by
        rw [fields_hide]; simp⟩
    | join first last => exact tidy_merge (normalized_tidy first) (normalized_tidy last)
  theorem normalized_args_tidy (patterns : List Pattern) :
      ∀ pattern ∈ normalizeArgs patterns, Tidy pattern := by
    cases patterns with
    | nil => intro pattern member; cases member
    | cons head tail =>
      intro pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact normalized_tidy head
      · exact normalized_args_tidy tail pattern member
end

theorem tidy_fields (pattern : Pattern) (tidy : Tidy pattern) : (fields pattern).Nodup := by
  cases pattern with
  | record label payload tail =>
    simp only [Tidy] at tidy
    exact List.nodup_cons.mpr ⟨tidy.2.2,tidy_fields tail tidy.2.1⟩
  | _ => exact List.nodup_nil

theorem sorted_canonical (label : Nat) (payload : Query) (labels : List Nat) (children : List Query)
    (length : children.length = labels.length) (unique : (label :: labels).Nodup) :
    ((((label,payload) :: labels.zip children).mergeSort (fun a b => a.1 ≤ b.1)).map Prod.fst).Pairwise (· < ·) := by
  have perm := (List.mergeSort_perm ((label,payload) :: labels.zip children) (fun a b => a.1 ≤ b.1)).map Prod.fst
  simp only [List.map_cons,List.map_fst_zip (Nat.le_of_eq length.symm)] at perm
  have distinct := perm.nodup_iff.mpr unique
  have sorted := List.pairwise_mergeSort (le := fun a b : Nat × Query => a.1 ≤ b.1)
    (fun a b c ab bc => by simp only [decide_eq_true_eq] at *; exact Nat.le_trans ab bc)
    (fun a b => by simp only [Bool.or_eq_true,decide_eq_true_eq]; exact Nat.le_total _ _) ((label,payload) :: labels.zip children)
  have ordered : (((label,payload) :: labels.zip children).mergeSort (fun a b => a.1 ≤ b.1)).map Prod.fst |>.Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact sorted.imp (fun h => of_decide_eq_true h)
  exact (ordered.and distinct).imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)

theorem translated_canonical (pattern : Pattern) (tidy : Tidy pattern) :
    ∀ test ∈ vocabulary (translate constructors interpretation pattern), TestCanonical test := by
  intro test member
  cases pattern with
  | var | join => simp only [translate,vocabulary] at member; cases member
  | variant tag payload =>
    simp only [Tidy] at tidy
    simp only [translate,vocabulary,vocabularies,List.append_nil] at member
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · split at member
      · cases member
      · exact translated_canonical payload tidy test member
  | app key arguments =>
    simp only [Tidy] at tidy
    rw [translate.eq_def] at member
    dsimp only at member
    split at member
    · cases List.mem_singleton.mp member; trivial
    · cases List.mem_singleton.mp member; exact List.Pairwise.nil
    · cases List.mem_singleton.mp member; trivial
    · rename_i first last primitive
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · simp only [vocabularies,List.append_nil] at member
        rcases List.mem_append.mp member with firstMember | lastMember
        · exact translated_canonical first (tidy _ (List.mem_cons_self ..)) test firstMember
        · exact translated_canonical last (tidy _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) test lastMember
    · split at member
      · split at member
        · rcases List.mem_cons.mp member with rfl | member
          · trivial
          · rw [vocabularies_flatMap] at member
            obtain ⟨child,present,member⟩ := List.mem_flatMap.mp member
            obtain ⟨⟨part,partMember⟩,_,rfl⟩ := List.mem_map.mp present
            have partSize := List.sizeOf_lt_of_mem partMember
            exact translated_canonical part (tidy part partMember) test member
        · cases member
      · cases member
  | record label payload tail =>
    simp only [Tidy] at tidy
    simp only [translate] at member
    split at member
    · rename_i labels children tailQuery
      rcases List.mem_cons.mp member with rfl | member
      · exact sorted_canonical label _ labels children
          (GeneralNominalOpenPatternLabels.record_length tail tailQuery)
          ((List.Perm.cons label (GeneralNominalCanonicalTemplates.record_fields tail tailQuery)).nodup_iff.mpr
            (List.nodup_cons.mpr ⟨tidy.2.2,tidy_fields tail tidy.2.1⟩))
      · rw [vocabularies_flatMap] at member
        obtain ⟨child,present,member⟩ := List.mem_flatMap.mp member
        obtain ⟨field,fieldMember,rfl⟩ := List.mem_map.mp present
        rcases List.mem_cons.mp (List.mem_mergeSort.mp fieldMember) with rfl | rest
        · exact translated_canonical payload tidy.1 test member
        · apply translated_canonical tail tidy.2.1 test
          rw [tailQuery]
          exact List.mem_cons_of_mem _ (by
            rw [vocabularies_flatMap]
            exact List.mem_flatMap.mpr ⟨field.2,(List.of_mem_zip rest).2,member⟩)
    · cases member
  termination_by sizeOf pattern
  decreasing_by all_goals simp_all; omega

theorem request_canonical (context : GeneralNominalCandidates.Context)
    (requests : List GeneralNominalMaterialization.Request) :
    GeneralNominalSourceProducerHandoff.RequestCanonical context requests := by
  intro entry member
  have mem : entry.2 ∈ (GeneralNominalMaterialization.generated context.state context.interpretation requests).tests.map Prod.snd :=
    List.mem_map.mpr ⟨entry,member,rfl⟩
  rw [generated_vocabulary] at mem
  obtain ⟨request,present,mem⟩ := List.mem_flatMap.mp mem
  exact translated_canonical _ (normalized_tidy request.pattern) _ mem

end Yulang.GeneralNominalRequestCanonical
