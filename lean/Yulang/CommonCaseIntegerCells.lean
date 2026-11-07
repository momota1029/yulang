import Std

/-! Finite representatives for every comparison against a finite list of
integer pattern endpoints. No bounded search over integer subjects is used. -/

namespace Yulang.CommonCaseIntegerCells

def belowMax (subject : Int) : List Int → Option Int
  | [] => none
  | first :: rest =>
      if first < subject then
        match belowMax subject rest with
        | none => some first
        | some last => some (if first ≤ last then last else first)
      else belowMax subject rest

def BelowSpec (subject : Int) (bounds : List Int) : Option Int → Prop
  | none => ∀ bound ∈ bounds, subject ≤ bound
  | some selected => selected ∈ bounds ∧ selected < subject ∧
      ∀ bound ∈ bounds, bound < subject → bound ≤ selected

theorem belowMax_spec (subject : Int) (bounds : List Int) : BelowSpec subject bounds (belowMax subject bounds) := by
  induction bounds with
  | nil => intro bound member; cases member
  | cons first rest ih =>
      cases found : belowMax subject rest with
      | none =>
          rw [found] at ih
          by_cases before : first < subject
          · simp only [belowMax, before, ↓reduceIte, found]
            refine ⟨List.mem_cons_self, before, ?_⟩
            intro bound member less
            rcases List.mem_cons.mp member with same | tail
            · subst bound; omega
            · have later := ih bound tail; omega
          · simp only [belowMax, before, ↓reduceIte, found]
            intro bound member
            rcases List.mem_cons.mp member with same | tail
            · subst bound; omega
            · exact ih bound tail
      | some selected =>
          rw [found] at ih
          rcases ih with ⟨member, before, greatest⟩
          by_cases headBefore : first < subject
          · by_cases chooseTail : first ≤ selected
            · simp only [belowMax, headBefore, ↓reduceIte, found, chooseTail]
              refine ⟨List.mem_cons_of_mem _ member, before, ?_⟩
              intro bound present less
              rcases List.mem_cons.mp present with same | tail
              · subst bound; exact chooseTail
              · exact greatest bound tail less
            · simp only [belowMax, headBefore, ↓reduceIte, found, chooseTail]
              refine ⟨List.mem_cons_self, headBefore, ?_⟩
              intro bound present less
              rcases List.mem_cons.mp present with same | tail
              · subst bound; omega
              · have earlier := greatest bound tail less; omega
          · simp only [belowMax, headBefore, ↓reduceIte, found]
            refine ⟨List.mem_cons_of_mem _ member, before, ?_⟩
            intro bound present less
            rcases List.mem_cons.mp present with same | tail
            · subst bound; omega
            · exact greatest bound tail less

def least (initial : Int) : List Int → Int
  | [] => initial
  | first :: rest => min initial (least first rest)

theorem least_spec (initial : Int) (rest : List Int) :
    least initial rest ∈ initial :: rest ∧ ∀ bound ∈ initial :: rest, least initial rest ≤ bound := by
  induction rest generalizing initial with
  | nil =>
      refine ⟨List.mem_cons_self, ?_⟩
      intro bound member
      have same : bound = initial := by simpa using member
      subst bound
      exact Int.le_refl _
  | cons first rest ih =>
      have tail := ih first
      constructor
      · by_cases before : initial ≤ least first rest
        · simpa only [least, Int.min_eq_left before] using (List.mem_cons_self (a := initial) (l := first :: rest))
        · rw [least, Int.min_eq_right (by omega)]
          exact List.mem_cons_of_mem initial tail.1
      · intro bound member
        rcases List.mem_cons.mp member with same | member
        · subst bound; exact Int.min_le_left _ _
        · exact Int.le_trans (Int.min_le_right _ _) (tail.2 bound member)

def representatives (bounds : List Int) : List Int :=
  0 :: bounds.flatMap (fun bound => [bound - 1, bound, bound + 1])

def SameComparisons (bounds : List Int) (first last : Int) : Prop :=
  ∀ bound ∈ bounds, (bound ≤ first ↔ bound ≤ last) ∧ (first ≤ bound ↔ last ≤ bound)

/-- Every integer, not only the tested points, has a finite representative
with exactly the same lower/upper comparisons against all pattern bounds. -/
theorem representative_exact (bounds : List Int) (subject : Int) :
    ∃ representative ∈ representatives bounds, SameComparisons bounds representative subject := by
  by_cases endpoint : subject ∈ bounds
  · exact ⟨subject, List.mem_cons_of_mem _ (List.mem_flatMap_of_mem endpoint (by simp)), fun _ _ => ⟨Iff.rfl, Iff.rfl⟩⟩
  · have spec := belowMax_spec subject bounds
    cases found : belowMax subject bounds with
    | some selected =>
        rw [found] at spec
        rcases spec with ⟨member, before, greatest⟩
        refine ⟨selected + 1, List.mem_cons_of_mem _ (List.mem_flatMap_of_mem member (by simp)), ?_⟩
        intro bound present
        have different : bound ≠ subject := fun same => endpoint (same ▸ present)
        by_cases less : bound < subject
        · have maximal := greatest bound present less
          constructor <;> omega
        · constructor <;> omega
    | none =>
        rw [found] at spec
        cases bounds with
        | nil => exact ⟨0, List.mem_cons_self, by intro bound member; cases member⟩
        | cons first rest =>
            have minimum := least_spec first rest
            have before := spec _ minimum.1
            have different : least first rest ≠ subject := fun same => endpoint (same ▸ minimum.1)
            refine ⟨least first rest - 1, List.mem_cons_of_mem _ (List.mem_flatMap_of_mem minimum.1 (by simp)), ?_⟩
            intro bound present
            have later := minimum.2 bound present
            have boundDifferent : bound ≠ subject := fun same => endpoint (same ▸ present)
            have boundAfter := spec bound present
            constructor <;> omega

end Yulang.CommonCaseIntegerCells
