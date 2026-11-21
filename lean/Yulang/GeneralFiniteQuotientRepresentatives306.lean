import Yulang.GeneralFiniteColoredEquivalence306

namespace Yulang.GeneralFiniteQuotientRepresentatives306
variable {α : Type}

def representatives (rel : α → α → Bool) : List α → List α
  | [] => []
  | x::rest =>
    let suffix := representatives rel rest
    if suffix.any (rel x) then suffix else x::suffix

theorem sublist (rel : α → α → Bool) (nodes : List α) :
    List.Sublist (representatives rel nodes) nodes := by
  induction nodes with
  | nil => exact .slnil
  | cons x rest ih =>
    simp only [representatives]
    split
    · exact ih.cons x
    · exact ih.cons_cons x

theorem covers (rel : α → α → Bool) (nodes : List α)
    (reflexive : ∀ x ∈ nodes, rel x x = true) (x : α) (xm : x ∈ nodes) :
    ∃ c ∈ representatives rel nodes, rel x c = true := by
  induction nodes with
  | nil => cases xm
  | cons head rest ih =>
    have prop : ∀ a ∈ rest, rel a a = true :=
      fun a listed => reflexive a (List.mem_cons_of_mem _ listed)
    rcases List.mem_cons.mp xm with rfl|inside
    · simp only [representatives]
      split
      · rename_i yes
        exact List.any_eq_true.mp yes
      · exact ⟨x,List.mem_cons_self ..,reflexive x (List.mem_cons_self ..)⟩
    · obtain ⟨c,mem,related⟩ := ih prop inside
      refine ⟨c,?_,related⟩
      simp only [representatives]
      split
      · exact mem
      · exact List.mem_cons_of_mem _ mem

theorem distinct (rel : α → α → Bool) (nodes : List α) :
    (representatives rel nodes).Pairwise (fun x y => rel x y = false) := by
  induction nodes with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [representatives]
    split
    · exact ih
    · rename_i no
      apply List.Pairwise.cons _ ih
      intro y mem
      cases value : rel x y
      · rfl
      · exact False.elim (no (List.any_eq_true.mpr ⟨y,mem,value⟩))

theorem no_two (rel : α → α → Bool) (nodes : List α)
    (symm : ∀ a ∈ nodes, ∀ b ∈ nodes, rel a b = true → rel b a = true)
    (pairwise : nodes.Pairwise (fun x y => rel x y = false))
    (a b : α) (am : a ∈ nodes) (bm : b ∈ nodes) (related : rel a b = true) : a = b := by
  induction nodes with
  | nil => cases am
  | cons x xs ih =>
    rw [List.pairwise_cons] at pairwise
    have symmRest : ∀ g ∈ xs, ∀ h ∈ xs, rel g h = true → rel h g = true :=
      fun g gm h hm => symm g (List.mem_cons_of_mem _ gm) h (List.mem_cons_of_mem _ hm)
    rcases List.mem_cons.mp am with rfl|ata <;> rcases List.mem_cons.mp bm with rfl|atb
    · rfl
    · have no := pairwise.1 b atb
      rw [related] at no
      cases no
    · have direction := symm a am b bm related
      have no := pairwise.1 a ata
      rw [direction] at no
      cases no
    · exact ih symmRest pairwise.2 ata atb

def select (rel : α → α → Bool) (nodes : List α) (x : α) : Option α :=
  (representatives rel nodes).find? (rel x)

theorem selected {rel : α → α → Bool} {nodes : List α} {x a : α}
    (hit : select rel nodes x = some a) :
    a ∈ representatives rel nodes ∧ rel x a = true :=
  ⟨List.mem_of_find?_eq_some hit,List.find?_some hit⟩

theorem select_exists {rel : α → α → Bool} {nodes : List α}
    (reflexive : ∀ x ∈ nodes, rel x x = true) {x : α} (xm : x ∈ nodes) :
    ∃ a, select rel nodes x = some a := by
  cases h : select rel nodes x with
  | none =>
    obtain ⟨a,found,pass⟩ := covers rel nodes reflexive x xm
    exact ((List.find?_eq_none.mp h) a found pass).elim
  | some a => exact ⟨a,rfl⟩

end Yulang.GeneralFiniteQuotientRepresentatives306
