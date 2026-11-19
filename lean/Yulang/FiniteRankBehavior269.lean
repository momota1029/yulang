import Yulang.GeneralRebaseFiniteSlices268

namespace Yulang.FiniteRankBehavior269
open GeneralRebaseFiniteSlices268 (slices exact_slices)

inductive Code (Label : Type) where
 | node (label : Label) (children : List (Code Label))

def Code.label : Code Label → Label
 | .node label _ => label

def Code.children : Code Label → List (Code Label)
 | .node _ children => children

def catalogue (labels : List Label) : Nat → List (Code Label)
 | 0 => labels.map (fun x => .node x [])
 | d+1 => labels.flatMap fun x => (slices (catalogue labels d)).map (Code.node x)

def Tracks (label : Source → Label) (move : Source → Source → Prop) :
 Nat → Source → Code Label → Prop
 | 0,s,.node read next => label s = read ∧ next = [] ∧ ∀ after, ¬ move s after
 | d+1,s,.node read next =>
   label s = read ∧
   (∀ after, move s after → ∃ branch ∈ next, Tracks label move d after branch) ∧
   (∀ branch ∈ next, ∃ after, move s after ∧ Tracks label move d after branch)

theorem at_label (h : Tracks label move depth source code) : label source = code.label := by
 cases depth <;> cases code <;> exact h.1

theorem universe_zero (labels : List Label) (x : Label) :
 Code.node x [] ∈ catalogue labels 0 ↔ x ∈ labels := by simp [catalogue]

theorem universe_succ (labels : List Label) (depth : Nat) (x : Label) (branches : List (Code Label)) :
 Code.node x branches ∈ catalogue labels (depth+1) ↔
 x ∈ labels ∧ branches.Sublist (catalogue labels depth) := by
 simp only [catalogue,List.mem_flatMap,List.mem_map,Code.node.injEq,exact_slices]
 constructor
 · rintro ⟨a,listed,b,within,rfl,rfl⟩
   exact ⟨listed,within⟩
 · rintro ⟨listed,within⟩
   exact ⟨x,listed,branches,within,rfl,rfl⟩

/-- A finite global catalogue represents even a concrete system with
infinite branching, as long as observations and strict rank are bounded.
Choosing which branches truly occur here is classical, not executable. -/
theorem represented (label : Source → Label) (move : Source → Source → Prop) (rank : Source → Nat)
 (labels : List Label) (supported : ∀ source, label source ∈ labels)
 (decreases : ∀ before after, move before after → rank after < rank before) :
 ∀ depth source, rank source ≤ depth →
   ∃ code ∈ catalogue labels depth, Tracks label move depth source code := by
 classical
 intro depth
 induction depth with
 | zero =>
   intro source atZero
   exact ⟨.node (label source) [],(universe_zero ..).mpr (supported source),rfl,rfl,
     fun after advance => Nat.not_lt_zero _ ((Nat.eq_zero_of_le_zero atZero) ▸ decreases source after advance)⟩
 | succ depth ih =>
   intro source within
   let real : Code Label → Prop := fun branch => ∃ after, move source after ∧ Tracks label move depth after branch
   let branches := (catalogue labels depth).filter (fun t => decide (real t))
   refine ⟨.node (label source) branches,(universe_succ ..).mpr ⟨supported source,List.filter_sublist ..⟩,
     rfl,?_,?_⟩
   · intro after step
     have le := decreases source after step
     obtain ⟨branch,member,correct⟩ := ih after (by omega)
     exact ⟨branch,List.mem_filter.mpr ⟨member,decide_eq_true ⟨after,step,correct⟩⟩,correct⟩
   · intro branch included
     exact of_decide_eq_true (List.mem_filter.mp included).2

end Yulang.FiniteRankBehavior269
