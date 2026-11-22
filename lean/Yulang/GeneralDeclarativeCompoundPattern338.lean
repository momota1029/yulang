import Yulang.GeneralDeclarativeCompoundEndpoints338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundPattern338
open GeneralDeclarationPatterns (Pattern normalize hide)
open CommonRoleCanonicalRows (Row)

def peel : Pattern → Row Pattern × Pattern
  | .record k p tail => ((k,p) :: (peel tail).1,(peel tail).2)
  | leaf => ([],leaf)

def rebuild : Row Pattern → Pattern → Pattern
  | [], p => p
  | (k,p)::rest, t => .record k p (rebuild rest t)

theorem rebuild_peel (p : Pattern) : rebuild (peel p).1 (peel p).2 = p := by
  refine Pattern.rec (motive_1 := fun pattern => rebuild (peel pattern).1 (peel pattern).2 = pattern)
    (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ trivial (fun _ _ _ _ => trivial) p
  · intros; rfl
  · intros; rfl
  · intro k p tail field next; simp [peel,rebuild,next]
  · intros; rfl
  · intros; rfl

def variables (r : Row Pattern) : List Nat := r.flatMap (fun x => x.2.variables)

theorem variables_rebuild (r : Row Pattern) (tail : Pattern) :
    (rebuild r tail).variables = variables r ++ tail.variables := by
  induction r with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨k,p⟩; simp [variables,rebuild,Pattern.variables,ih,List.append_assoc]

theorem variables_peel (p : Pattern) :
    p.variables = variables (peel p).1 ++ (peel p).2.variables := by
  simpa only [rebuild_peel] using variables_rebuild (peel p).1 (peel p).2

def labels (p : Pattern) : List Nat := (peel p).1.map Prod.fst

theorem labels_hide (k : Nat) (p : Pattern) :
    labels (hide k p) = (labels p).filter (fun x => x != k) := by
  refine Pattern.rec (motive_1 := fun pattern => labels (hide k pattern) =
    (labels pattern).filter (fun x => x != k)) (motive_2 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ trivial (fun _ _ _ _ => trivial) p
  · intros; rfl
  · intros; rfl
  · intro l p tl _ ih
    by_cases eq : k = l
    · subst l; simpa [hide,labels,peel] using ih
    · have away : l ≠ k := Ne.symm eq
      have step : hide k (.record l p tl) = .record l p (hide k tl) := by simp [hide,eq]
      rw [step]
      change l :: labels (hide k tl) = (l :: labels tl).filter (fun x => x != k)
      simp [away,ih]
  · intros; rfl
  · intros; rfl

/-- This is the production normalization, including first-label
visibility. No separate record shape admission condition is needed. -/
theorem normalized_labels (p : Pattern) : (labels (normalize p)).Nodup := by
  have mergeLabels (a b : Pattern) (already : (labels a).Nodup) : (labels (GeneralDeclarationPatterns.merge a b)).Nodup := by
    unfold GeneralDeclarationPatterns.merge
    split
    · exact already
    · split
      next xs ys _ _ =>
        classical
        generalize s : (Variants.Merged.normalize GeneralDeclarationPatterns.mergePayload (xs ++ ys)).entries.mergeSort
          (fun a b => a.1 ≤ b.1) = rs
        cases rs with
        | nil => simp [GeneralDeclarationPatterns.rowPattern,labels,peel]
        | cons h t =>
          cases t with
          | nil => cases h; simp [GeneralDeclarationPatterns.rowPattern,labels,peel]
          | cons j js => cases h; simp [GeneralDeclarationPatterns.rowPattern,labels,peel]
      all_goals simp [labels,peel]
  refine Pattern.rec (motive_1 := fun pattern => (labels (normalize pattern)).Nodup)
    (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ trivial (fun _ _ _ _ => trivial) p
  · intros; exact List.nodup_nil
  · intros; exact List.nodup_nil
  · intro k p tail hp ht
    change (k :: labels (hide k (normalize tail))).Nodup
    rw [labels_hide]
    refine List.nodup_cons.mpr ⟨?_,ht.filter _⟩
    intro has
    have no := (List.mem_filter.mp has).2
    simp at no
  · intros; exact List.nodup_nil
  · intro a b ha hb; exact mergeLabels _ _ ha

/-- Layout-only numbers route fresh triples. They are not occurrences
in the source declaration and never enter the I-58 equality batch. -/
def layout (r : Row Pattern) : List (Nat × Nat) := r.zipIdx.map (fun z => (z.1.1,z.2))

theorem layout_labels (r : Row Pattern) : (layout r).map Prod.fst = r.map Prod.fst := by
  simpa only [layout,List.map_map,Function.comp_def] using
    congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 r)

end Yulang.GeneralDeclarativeCompoundPattern338
