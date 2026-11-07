import Yulang.CommonCaseIntegerCells
import Yulang.LiteralValues

/-! Complete finite cells for every inhabited literal in the current Common
carrier. Strings use queried constants and one fresh decoded string; no finite
sample of ordinary strings is assumed to stand for all remaining strings. -/

namespace Yulang.CommonCaseLiteralCells

open LiteralValues (Literal)
open CommonCaseIntegerCells (SameComparisons)

def freshText : List String → String
  | [] => ""
  | first :: rest => first ++ freshText rest ++ "x"

theorem freshText_longer (texts : List String) (text : String) (member : text ∈ texts) :
    text.length < (freshText texts).length := by
  induction texts with
  | nil => cases member
  | cons first rest ih =>
      simp only [freshText, String.length_append]
      have one : ("x" : String).length = 1 := rfl
      rw [one]
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have shorter := ih member; omega

theorem freshText_not_mem (texts : List String) : freshText texts ∉ texts := by
  intro member
  have impossible := freshText_longer texts _ member
  exact Nat.lt_irrefl _ impossible

def SameTexts (texts : List String) (first last : String) : Prop :=
  ∀ text ∈ texts, (text = first ↔ text = last)

def textRepresentatives (texts : List String) : List String := freshText texts :: texts

theorem text_representative_complete (texts : List String) (subject : String) :
    ∃ representative ∈ textRepresentatives texts, SameTexts texts representative subject := by
  by_cases known : subject ∈ texts
  · exact ⟨subject, List.mem_cons_of_mem _ known, fun _ _ => Iff.rfl⟩
  · refine ⟨freshText texts, List.mem_cons_self, ?_⟩
    intro text member
    have fresh : text ≠ freshText texts := fun equal => freshText_not_mem texts (equal ▸ member)
    have other : text ≠ subject := fun equal => known (equal ▸ member)
    exact ⟨fun equal => (fresh equal).elim, fun equal => (other equal).elim⟩

inductive Equivalent (bounds : List Int) (texts : List String) : Literal Empty → Literal Empty → Prop where
  | integer : SameComparisons bounds first last → Equivalent bounds texts (.int first) (.int last)
  | string : SameTexts texts first last → Equivalent bounds texts (.str first) (.str last)
  | boolean : Equivalent bounds texts (.bool value) (.bool value)
  | unit : Equivalent bounds texts .unit .unit

def representatives (bounds : List Int) (texts : List String) : List (Literal Empty) :=
  (CommonCaseIntegerCells.representatives bounds).map .int ++
    (textRepresentatives texts).map .str ++ [.bool false, .bool true, .unit]

theorem representative_complete (bounds : List Int) (texts : List String) (subject : Literal Empty) :
    ∃ representative ∈ representatives bounds texts, Equivalent bounds texts representative subject := by
  cases subject with
  | int value =>
      obtain ⟨sample, member, same⟩ := CommonCaseIntegerCells.representative_exact bounds value
      exact ⟨.int sample, List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨sample, member, rfl⟩)), .integer same⟩
  | str value =>
      obtain ⟨sample, member, same⟩ := text_representative_complete texts value
      exact ⟨.str sample, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨sample, member, rfl⟩)), .string same⟩
  | bool value =>
      refine ⟨.bool value, List.mem_append_right _ ?_, .boolean⟩
      cases value <;> simp
  | unit => exact ⟨.unit, List.mem_append_right _ (by simp), .unit⟩
  | float value => exact value.elim

end Yulang.CommonCaseLiteralCells
