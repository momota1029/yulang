import Yulang.GeneralRebasePartialBool268

namespace Yulang.GeneralRebasePartialFinite268
open GeneralRebasePartialBool268 (Answer Reflect either neg both)

def any (answer : Element → Answer) : List Element → Answer
 | [] => some false
 | first :: tail => either (answer first) (any answer tail)

theorem any_sound (prop : Element → Prop) (answer : Element → Answer) (entries : List Element)
 (cert : ∀ item ∈ entries, Reflect (prop item) (answer item)) :
 Reflect (∃ item ∈ entries, prop item) (any answer entries) := by
 induction entries with
 | nil => intro h; obtain ⟨_,empty,_⟩ := h; cases empty
 | cons first tail ih =>
   have localCert := GeneralRebasePartialBool268.either_sound (cert first List.mem_cons_self)
     (ih (fun x hx => cert x (List.mem_cons_of_mem _ hx)))
   cases h : any answer (first :: tail) with
   | none => trivial
   | some b =>
     change Reflect (prop first ∨ ∃ item ∈ tail, prop item) (any answer (first :: tail)) at localCert
     rw [h] at localCert
     cases b with
     | false =>
       intro detected
       obtain ⟨item,found,holds⟩ := detected
       rcases List.mem_cons.mp found with rfl | stay
       · exact localCert (Or.inl holds)
       · exact localCert (Or.inr ⟨item,stay,holds⟩)
     | true =>
       rcases localCert with firstHolds | ⟨item,found,holds⟩
       · exact ⟨first,List.mem_cons_self,firstHolds⟩
       · exact ⟨item,List.mem_cons_of_mem _ found,holds⟩

def all (answer : Element → Answer) (entries : List Element) : Answer :=
 neg (any (fun item => neg (answer item)) entries)

theorem all_sound (prop : Element → Prop) (answer : Element → Answer) (entries : List Element)
 (cert : ∀ item ∈ entries, Reflect (prop item) (answer item)) :
 Reflect (∀ item ∈ entries, prop item) (all answer entries) := by
 have valid := GeneralRebasePartialBool268.neg_sound (any_sound (fun x => ¬ prop x) (fun x => neg (answer x))
   entries (fun x hx => GeneralRebasePartialBool268.neg_sound (cert x hx)))
 change Reflect (¬ (∃ x ∈ entries, ¬ prop x)) (all answer entries) at valid
 cases h : all answer entries with
 | none => trivial
 | some b =>
   rw [h] at valid
   cases b with
   | false => exact fun each => valid (fun ⟨x,member,no⟩ => no (each x member))
   | true => exact fun x member => Classical.byContradiction (fun no => valid ⟨x,member,no⟩)

theorem any_total (answer : Element → Answer) (entries : List Element)
 (cert : ∀ item ∈ entries, answer item ≠ none) : any answer entries ≠ none := by
 induction entries with
 | nil => simp [any]
 | cons first tail ih =>
   exact GeneralRebasePartialBool268.total_either (cert first List.mem_cons_self)
     (ih (fun x hx => cert x (List.mem_cons_of_mem _ hx)))

theorem all_total (answer : Element → Answer) (entries : List Element)
 (cert : ∀ item ∈ entries, answer item ≠ none) : all answer entries ≠ none :=
 GeneralRebasePartialBool268.total_neg (any_total (fun x => neg (answer x)) entries
   (fun x hx => GeneralRebasePartialBool268.total_neg (cert x hx)))

theorem transfer {p q : Prop} {answer : Answer} (equal : p ↔ q) (cert : Reflect p answer) :
 Reflect q answer := by
 cases answer with
 | none => trivial
 | some b =>
   cases b
   · exact fun h => cert (equal.mpr h)
   · exact equal.mp cert

end Yulang.GeneralRebasePartialFinite268
