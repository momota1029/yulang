import Yulang.GeneralDeclarativeWitnessSelectedNonpointChild363

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOrderedDictionary363
open CommonRoleOutermostResolver (Frontier Tree Dictionary Result All₂ Resolves Summarizes Classify)
universe u

inductive Evidence {α : Type u} (withMeaning : α → Nat → List α → Prop) : α → Dictionary → Prop where
  | node : withMeaning request chosen sources →
      All₂ (Evidence withMeaning) sources children →
      Evidence withMeaning request (.node chosen children)

variable {α : Type u} {rule : α → Frontier α → Prop} {meaning : α → Nat → List α → Prop}

mutual
theorem selected_tree_sound
    (localSound : ∀ d key children,rule d (.selected key children) → meaning d key children)
    (trace : Tree) (selected : Resolves rule d trace)
    (summarizes : Summarizes trace (.selected dict)) : Evidence meaning d dict := by
  cases selected with
  | pending _ => cases summarizes
  | rejected _ => cases summarizes
  | ambiguous _ => cases summarizes
  | selected atRoot emitted =>
    cases summarizes with
    | selected summaries folded =>
      cases folded with
      | selected senses =>
        subst_vars
        exact .node (localSound _ _ _ atRoot) (selected_children_sound localSound _ _ emitted summaries)
termination_by sizeOf trace

theorem selected_children_sound
    (localSound : ∀ d key children,rule d (.selected key children) → meaning d key children)
    (trees : List Tree) (ds : List Dictionary)
    (selected : All₂ (Resolves rule) children trees)
    (summarizes : All₂ Summarizes trees (ds.map Result.selected)) :
    All₂ (Evidence meaning) children ds := by
  cases ds with
  | nil =>
    cases summarizes
    cases selected
    exact .nil
  | cons item rest =>
    cases summarizes with
    | cons first more =>
      cases selected with
      | cons a b =>
        exact .cons (selected_tree_sound localSound _ a first) (selected_children_sound localSound _ _ b more)
termination_by sizeOf trees
end

/-- The ordered finite bridge does not choose a root or claim termination.
The same local theorem (in one fixed model when instantiated) is used
at every node; the recursive shape comes from the actual ordered trace. -/
theorem dictionary_sound
    (localSound : ∀ d key children,rule d (.selected key children) → meaning d key children)
    (success : Classify rule d (.selected dict)) : Evidence meaning d dict := by
  obtain ⟨tree,actual,summary⟩ := success
  exact selected_tree_sound localSound tree actual summary

end Yulang.GeneralDeclarativeWitnessOrderedDictionary363
