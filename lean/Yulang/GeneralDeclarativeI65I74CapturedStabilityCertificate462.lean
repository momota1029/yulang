import Yulang.GeneralDeclarativeI65I74CapturedNormalForm462
import Yulang.GeneralDeclarativeI65I74RecordWrittenTree455
import Yulang.GeneralDeclarativeI65I74IdenticalTagProjection459

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CapturedNormalForm462
open GeneralDeclarationPatterns
open RecordTree455 (WrittenArgs checkTrees checkTrees_exact written_tree_paterson_stable_under_all_captures455)
open IdenticalTagProjection459 (identity_args_capture_spells_original459)

mutual
  inductive Projection : Pattern → Pattern → Prop where
    | var : Projection (.var n) (.var n)
    | app : ProjectionArgs as bs → Projection (.app k as) (.app k bs)
    | record : Projection p q → Projection t u →
        Projection (.record label p t) (.record label q (hide label u))
    | variant : Projection p q → Projection (.variant k p) (.variant k q)
    | keepJoin : Projection p left → Projection q right → left ≠ right →
        Projection (.join p q) (.join left right)
    | equalJoin : Projection p u → Projection q u → Projection (.join p q) u

  inductive ProjectionArgs : List Pattern → List Pattern → Prop where
    | nil : ProjectionArgs [] []
    | cons : Projection p q → ProjectionArgs ps qs → ProjectionArgs (p::ps) (q::qs)
end

mutual
  theorem reflection_of_original_tree {p q : Pattern} : Projection p q → simplify p = q
    | .var => rfl
    | .app as => by simp [simplify,reflection_of_original_args as]
    | .record component rest => by simp [simplify,reflection_of_original_tree component,reflection_of_original_tree rest]
    | .variant component => by simp [simplify,reflection_of_original_tree component]
    | .keepJoin first last different => by
      simp [simplify,reflection_of_original_tree first,reflection_of_original_tree last,different]
    | .equalJoin first last => by
      simp [simplify,reflection_of_original_tree first,reflection_of_original_tree last]

  theorem reflection_of_original_args {ps qs : List Pattern} : ProjectionArgs ps qs → simplifyArgs ps = qs
    | .nil => rfl
    | .cons h t => by simp [simplifyArgs,reflection_of_original_tree h,reflection_of_original_args t]
end

mutual
  theorem reify_independent_original_tree : ∀ (p : Pattern), Projection p (simplify p)
    | .var _ => .var
    | .app _ as => .app (reify_independent_original_args as)
    | .record _ p t => .record (reify_independent_original_tree p) (reify_independent_original_tree t)
    | .variant _ p => .variant (reify_independent_original_tree p)
    | .join p q => by
      simp only [simplify]
      by_cases equal : simplify p = simplify q
      · rw [ite_eq_left equal]
        exact .equalJoin (reify_independent_original_tree p) (equal.symm ▸ reify_independent_original_tree q)
      · rw [ite_eq_right equal]
        exact .keepJoin (reify_independent_original_tree p) (reify_independent_original_tree q) equal

  theorem reify_independent_original_args : ∀ ps, ProjectionArgs ps (simplifyArgs ps)
    | [] => .nil
    | p::ps => .cons (reify_independent_original_tree p) (reify_independent_original_args ps)
end

theorem exact_structure_read_original_tree (p q : Pattern) : Projection p q ↔ simplify p = q :=
  ⟨reflection_of_original_tree,fun h => h ▸ reify_independent_original_tree p⟩

def SupportsStable (key : Nat) (head child : List Pattern) : Prop :=
  ∃ ps qs, ProjectionArgs head ps ∧ ProjectionArgs child qs ∧
    WrittenArgs key ps ∧ WrittenArgs key qs ∧ Smaller head child

def verifiesStable (key : Nat) (head child : List Pattern) : Bool :=
  checkTrees key (simplifyArgs head) && checkTrees key (simplifyArgs child) && checkSmaller head child

theorem finite_projected_stability_check_exact (key : Nat) (head child : List Pattern) :
    verifiesStable key head child = true ↔ SupportsStable key head child := by
  simp only [verifiesStable,Bool.and_eq_true,checkTrees_exact,checkSmaller_exact]
  constructor
  · rintro ⟨⟨a,b⟩,s⟩
    exact ⟨_,_,reify_independent_original_args _,reify_independent_original_args _,a,b,s⟩
  · rintro ⟨ps,qs,a,b,headClosed,childClosed,small⟩
    rw [reflection_of_original_args a,reflection_of_original_args b]
    exact ⟨⟨headClosed,childClosed⟩,small⟩

theorem projection_transfers_original_all_captures
    (key : Nat) (head child : List Pattern) (finite : SupportsStable key head child) :
    StableSmaller head child := by
  obtain ⟨ps,qs,projHead,projChild,headClosed,childClosed,small⟩ := finite
  have keepHead (cap) : counted (substArgs cap ps) = counted (substArgs cap head) := by
    rw [← reflection_of_original_args projHead]
    exact same_original_captured_counts cap head
  have keepChild (cap) : counted (substArgs cap qs) = counted (substArgs cap child) := by
    rw [← reflection_of_original_args projChild]
    exact same_original_captured_counts cap child
  have smallProjected : Smaller ps qs := by
    have h := keepHead Pattern.var
    have c := keepChild Pattern.var
    simp only [identity_args_capture_spells_original459] at h c
    simpa only [Smaller,h,c] using small
  have always := written_tree_paterson_stable_under_all_captures455 headClosed childClosed smallProjected
  intro cap
  simpa only [Smaller,keepChild cap,keepHead cap] using always cap

end Yulang.GeneralDeclarativeI65.I72.CapturedNormalForm462
