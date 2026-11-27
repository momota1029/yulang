import Yulang.GeneralDeclarativeI65I74PreparationFootprint467

namespace Yulang.GeneralDeclarativeI65.I72.PreparationTagScope467
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeLowerKnown321 (Alias Tag Knows constructorTag)
open PreparationFootprint467 (OrdinaryRetraction observedFootprint)

def tagOwner (e : Equation) : List Nat :=
  if (constructorTag e.right).isSome then [e.left] else []

def tagFootprint (s : State) : List Nat :=
  s.equations.flatMap tagOwner

theorem tag_footprint_covers_every_known_constructor_row
    {s : State} {e : Equation} {tag : Tag}
    (present : e ∈ s.equations) (visible : constructorTag e.right = some tag) :
    e.left ∈ tagFootprint s := by
  exact List.mem_flatMap.mpr ⟨e,present,by simp [tagOwner,visible]⟩

theorem original_lower_constructor_knowledge_preserved_at_all_pinned_names
    {s t : State} {p : Nat → Nat} (r : OrdinaryRetraction s t p)
    (sameRows : s.equations = t.equations)
    (tagFixed : ∀ n ∈ tagFootprint s, p n = n)
    {n : Nat} (fixed : p n = n) (tag : Tag) :
    Knows s n tag ↔ Knows t n tag := by
  constructor
  · rintro ⟨e,present,link,known⟩
    exact ⟨e,sameRows ▸ present,r.alias_forward link,known⟩
  · rintro ⟨e,present,link,known⟩
    have inOld : e ∈ s.equations := sameRows.symm ▸ present
    have pin := tagFixed e.left (tag_footprint_covers_every_known_constructor_row inOld known)
    exact ⟨e,inOld,by simpa [fixed,pin] using r.alias_back link,known⟩

theorem finite_combined_graph_and_tag_scope_preserves_K2_and_knowledge
    {s t : State} {p : Nat → Nat} (r : OrdinaryRetraction s t p)
    (sameRows : s.equations = t.equations) {root : Nat}
    (check : (root :: observedFootprint s ++ tagFootprint s).all (fun n => decide (p n = n)) = true) :
    (GeneralDeclarativeK2Alias321.AliasCycle s (GeneralDeclarativeGraphRows321.observed s) root ↔
      GeneralDeclarativeK2Alias321.AliasCycle t (GeneralDeclarativeGraphRows321.observed t) root) ∧
    (∀ tag, Knows s root tag ↔ Knows t root tag) := by
  have all : ∀ n ∈ root :: observedFootprint s ++ tagFootprint s, p n = n := by
    intro n present
    exact of_decide_eq_true ((List.all_eq_true.mp check) n present)
  refine ⟨PreparationFootprint467.actual_original_cycle_same_if_finite_pinned_names_fixed r sameRows ?_,?_⟩
  · apply List.all_eq_true.mpr
    intro n present
    exact decide_eq_true (all n (by simpa [List.cons_append] using
      (List.mem_append.mpr (Or.inl present) : n ∈ (root :: observedFootprint s) ++ tagFootprint s)))
  · exact original_lower_constructor_knowledge_preserved_at_all_pinned_names r sameRows
      (fun n hn => all n (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hn))))
      (all root List.mem_cons_self)

end Yulang.GeneralDeclarativeI65.I72.PreparationTagScope467
