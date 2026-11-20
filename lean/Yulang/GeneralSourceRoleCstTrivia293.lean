import Yulang.GeneralSourceRoleCstOccurrenceControls293

/-! Filtering trivia is only a semantic projection. The stored raw child
ordinals are still computed from the input including those trivia tokens. -/
namespace Yulang.GeneralSourceRoleCstTrivia293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstShapes293 (visible)

theorem erase_indices (start : Nat) (children : List Tree) :
    (((indexedFrom start children).filter (fun p => !(trivia p.2))).map Prod.snd) =
      children.filter (fun t => !(trivia t)) := by
  induction children generalizing start with
  | nil => rfl
  | cons c cs ih =>
    cases h : trivia c <;> simp [indexedFrom,h,ih]

theorem visible_filter (children : List Tree) :
    visible children = children.filter (fun t => !(trivia t)) :=
  erase_indices 0 children

theorem insert_one_trivia (before after : List Tree) (tok : Tree) (trivial : trivia tok = true) :
    visible (before ++ tok::after) = visible (before ++ after) := by
  simp [visible_filter,List.filter_append,trivial]

theorem statements_shift_labels_not_spelling :
    visible [.token .whitespace " ",.token .identifier "x"] =
      visible [.token .identifier "x"] ∧
    ((significant [.token .whitespace " ",.token .identifier "x"]).map Prod.fst) = [1] ∧
    ((significant [.token .identifier "x"]).map Prod.fst) = [0] := ⟨rfl,rfl,rfl⟩

end Yulang.GeneralSourceRoleCstTrivia293
