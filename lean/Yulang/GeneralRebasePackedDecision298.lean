import Yulang.GeneralRebasePackedSource298

namespace Yulang.GeneralRebasePackedDecision298
open GeneralRebasePartialBool268 (Answer Reflect either)
open GeneralRebasePackedAnswers298 (Vector pack fill)
open GeneralRebaseQuestionFootprint298 (question)
open GeneralRebaseSymbolicQuestions298 (Body)
open GeneralNominalRebaseJournalView243 (Journal)
open GeneralNominalCommonBridge (Assignment)

def reduce (probe : α → Answer) : List α → Answer
 | [] => some false
 | a :: tail => either (probe a) (reduce probe tail)

def Covered (P : α → Prop) (rows : List α) : Prop :=
  (∃ a, P a) → ∃ a ∈ rows, P a

theorem included_sound (P : α → Prop) (probe : α → Answer) (rows : List α)
    (checked : ∀ a ∈ rows, Reflect (P a) (probe a)) :
    Reflect (∃ a ∈ rows, P a) (reduce probe rows) := by
  induction rows with
  | nil => exact fun ⟨_,impossible,_⟩ => List.not_mem_nil impossible
  | cons a tail ih =>
    have h : (P a ∨ ∃ b ∈ tail, P b) ↔ ∃ b ∈ a :: tail, P b := by
      constructor
      · rintro (yes | ⟨b,listed,given⟩)
        · exact ⟨a,List.mem_cons_self ..,yes⟩
        · exact ⟨b,List.mem_cons_of_mem _ listed,given⟩
      · rintro ⟨b,listed,yes⟩
        rcases List.mem_cons.mp listed with rfl | suffix
        · exact Or.inl yes
        · exact Or.inr ⟨b,suffix,yes⟩
    exact GeneralRebasePartialFinite268.transfer h (GeneralRebasePartialBool268.either_sound
      (checked a (List.mem_cons_self ..)) (ih (fun b hm => checked b (List.mem_cons_of_mem _ hm))))

theorem sound (P : α → Prop) (probe : α → Answer) (rows : List α)
    (checked : ∀ a ∈ rows, Reflect (P a) (probe a))
    (yes : reduce probe rows = some true) : ∃ a, P a := by
  have h := included_sound P probe rows checked
  rw [yes] at h
  obtain ⟨a,_,ok⟩ := h
  exact ⟨a,ok⟩

theorem total (probe : α → Answer) (rows : List α)
    (decided : ∀ a ∈ rows, probe a ≠ none) : reduce probe rows ≠ none := by
  induction rows with
  | nil => intro h; cases h
  | cons a tail ih =>
    exact GeneralRebasePartialBool268.total_either (decided a (List.mem_cons_self ..))
      (ih (fun b hm => decided b (List.mem_cons_of_mem _ hm)))

theorem exact_if_covered (P : α → Prop) (probe : α → Answer) (rows : List α)
    (checked : ∀ a ∈ rows, Reflect (P a) (probe a)) (cover : Covered P rows) :
    Reflect (∃ a, P a) (reduce probe rows) :=
  GeneralRebasePartialFinite268.transfer ⟨fun ⟨a,_,ok⟩ => ⟨a,ok⟩,cover⟩
    (included_sound P probe rows checked)

theorem complete (P : α → Prop) (probe : α → Answer) (rows : List α)
    (checked : ∀ a ∈ rows, Reflect (P a) (probe a)) (cover : Covered P rows)
    (decided : ∀ a ∈ rows, probe a ≠ none) :
    reduce probe rows = some true ↔ ∃ a, P a :=
  GeneralRebasePartialBool268.true_iff (exact_if_covered P probe rows checked cover) (total probe rows decided)

abbrev Judge (j : Journal) (q : Body) (pad : Assignment) :=
  fun v : Vector (question j q) => q.Holds j (fill (question j q) v pad)

def encode (j : Journal) (q : Body) (rows : List Assignment) : List (Vector (question j q)) :=
  rows.map (pack (question j q))

theorem covered_encoding (j : Journal) (q : Body) (pad : Assignment) (rows : List Assignment)
    (cover : Covered (q.Holds j) rows) :
    Covered (Judge j q pad) (encode j q rows) := by
  rintro ⟨v,h⟩
  refine ?_
  obtain ⟨a,listed,ok⟩ := cover ⟨fill _ v pad,h⟩
  exact ⟨pack _ a,List.mem_map_of_mem listed,
    (GeneralRebasePackedAnswers298.check_same j q a pad).mpr ok⟩

theorem answer (j : Journal) (q : Body) (pad : Assignment) (xs : List Assignment)
    (probe : Vector (question j q) → Answer)
    (covered : Covered (q.Holds j) xs)
    (reflect : ∀ v ∈ encode j q xs, Reflect (Judge j q pad v) (probe v)) :
    Reflect (∃ m, q.Holds j m) (reduce probe (encode j q xs)) :=
  GeneralRebasePartialFinite268.transfer (GeneralRebasePackedAnswers298.asked_iff j q pad).symm
    (exact_if_covered (Judge j q pad) probe (encode j q xs) reflect (covered_encoding j q pad xs covered))

theorem unknown_control : reduce (fun _ : Unit => none) [()] = none := rfl

end Yulang.GeneralRebasePackedDecision298
