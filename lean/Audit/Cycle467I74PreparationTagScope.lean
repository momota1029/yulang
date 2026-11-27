import Yulang.GeneralDeclarativeI65I74PreparationTagScope467

namespace Yulang.GeneralDeclarativeI65.I72.C467Independent
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeLowerKnown321 (Alias Tag Knows constructorTag)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open PreparationFootprint467 (OrdinaryRetraction observedFootprint fixesNamedScope)

private def inlineRow : Equation := ⟨1,.variant 12 (.primitive .emptyRecord [])⟩
private def grows : List (PresenceNormalForm.Atom Nat) := [.tyLe (.var 0) (.var 1),.tyLe (.var 1) (.var 0)]
private def first : State := ⟨⟨[],[]⟩,[inlineRow]⟩
private def second : State := ⟨⟨grows,[]⟩,[inlineRow]⟩
private def forgetExtra (n : Nat) : Nat := if n = 1 then 0 else n

private theorem firstAliasEq {a b : Nat} (h : Alias first a b) : a = b := by
  have onlyRefl {u v : Nat} (it : Bound first.normal u v) : u = v := by
    induction it with
    | interval mem => simp [first] at mem
    | constraint mem => simp [first] at mem
    | refl _ => rfl
    | trans _ _ ab bc => exact ab.trans bc
  induction h with
  | bounds into _ => exact onlyRefl into
  | forward mem => simp [first,inlineRow] at mem
  | backward mem => simp [first,inlineRow] at mem
  | trans _ _ ab bc => exact ab.trans bc

private theorem realRetraction : OrdinaryRetraction first second forgetExtra := by
  apply PreparationFootprint467.ordinary_retraction_of_collapsing_appended_atoms
    (s := first) (t := second) (added := grows) rfl rfl rfl
  · intro a b mem
    simp [first] at mem
  · intro a b mem
    simp [first] at mem
  · intro a b mem
    simp [first,inlineRow] at mem
  · intro a b mem
    simp [grows] at mem
    rcases mem with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl

theorem exact_pin_of_graph_scope_alone_does_not_preserve_inline_tag :
    fixesNamedScope first forgetExtra 0 = true ∧
    (AliasCycle first (observed first) 0 ↔ AliasCycle second (observed second) 0) ∧
    ¬ Knows first 0 (.variant 12) ∧ Knows second 0 (.variant 12) := by
  have check : fixesNamedScope first forgetExtra 0 = true := by rfl
  refine ⟨check,PreparationFootprint467.actual_original_cycle_same_if_finite_pinned_names_fixed
    realRetraction rfl check,?_,?_⟩
  · rintro ⟨e,mem,found,_⟩
    have eq : e = inlineRow := List.mem_singleton.mp mem
    subst e
    have no : (0 : Nat) = 1 := firstAliasEq found
    exact Nat.zero_ne_one no
  · have links : Alias second 0 1 := .bounds
      (.constraint (by simp [second,grows])) (.constraint (by simp [second,grows]))
    exact ⟨inlineRow,by simp [second],links,rfl⟩

end Yulang.GeneralDeclarativeI65.I72.C467Independent

open Yulang.GeneralDeclarativeI65.I72.PreparationTagScope467
#print axioms tag_footprint_covers_every_known_constructor_row
#print axioms original_lower_constructor_knowledge_preserved_at_all_pinned_names
#print axioms finite_combined_graph_and_tag_scope_preserves_K2_and_knowledge
#print axioms Yulang.GeneralDeclarativeI65.I72.C467Independent.exact_pin_of_graph_scope_alone_does_not_preserve_inline_tag
