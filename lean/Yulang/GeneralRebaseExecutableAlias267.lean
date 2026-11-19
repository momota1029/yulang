import Yulang.GeneralRebaseSupportedWorklist267
import Yulang.GeneralNominalSaturationState

namespace Yulang.GeneralRebaseExecutableAlias267
open GeneralNominalSaturationState (State Alias)
open FiniteWorklist (Path reachable)

def next (state : State roles) (id : Nat) : List Nat :=
 state.aliases.flatMap fun (a,b) =>
   (if id = a then [b] else []) ++ (if id = b then [a] else [])

def support (state : State roles) (start : Nat) : List Nat :=
 start :: state.aliases.flatMap fun (a,b) => [a,b]

theorem next_exact (state : State roles) (a b : Nat) :
 b ∈ next state a ↔ (a,b) ∈ state.aliases ∨ (b,a) ∈ state.aliases := by
 simp only [next,List.mem_flatMap]
 constructor
 · rintro ⟨⟨x,y⟩,present,inside⟩
   rcases List.mem_append.mp inside with front | back
   · split at front
     · rename_i same
       cases List.mem_singleton.mp front
       cases same
       exact Or.inl present
     · simp at front
   · split at back
     · rename_i same
       cases List.mem_singleton.mp back
       cases same
       exact Or.inr present
     · simp at back
 · rintro (forward | backward)
   · exact ⟨(a,b),forward,List.mem_append_left _ (by simp)⟩
   · exact ⟨(b,a),backward,List.mem_append_right _ (by simp)⟩

theorem support_closed (state : State roles) (start a : Nat) :
 next state a ⊆ support state start := by
 intro b edge
 apply List.mem_cons_of_mem
 rcases (next_exact state a b).mp edge with forward | backward
 · exact List.mem_flatMap.mpr ⟨(a,b),forward,by simp⟩
 · exact List.mem_flatMap.mpr ⟨(b,a),backward,by simp⟩

theorem path_symmetric (state : State roles) (path : Path (next state) a b) : Path (next state) b a := by
 induction path with
 | nil v => exact .nil v
 | cons edge _ ih =>
   have reverse := (next_exact state _ _).mpr ((next_exact state _ _).mp edge).symm
   exact ih.append (.cons reverse (.nil _))

theorem path_exact (state : State roles) (a b : Nat) : Path (next state) a b ↔ Alias state a b := by
 constructor
 · intro path
   induction path with
   | nil v => exact .refl v
   | cons edge _ ih =>
     rcases (next_exact state _ _).mp edge with forward | backward
     · exact .trans (.edge forward) ih
     · exact .trans (.symm (.edge backward)) ih
 · intro alias
   induction alias with
   | refl v => exact .nil v
   | edge edge => exact .cons ((next_exact state _ _).mpr (Or.inl edge)) (.nil _)
   | symm _ ih => exact path_symmetric state ih
   | trans _ _ left right => exact left.append right

def aliases (state : State roles) (a : Nat) : List Nat :=
 reachable (next state) (support state a).length a

theorem aliases_exact (state : State roles) (a b : Nat) : b ∈ aliases state a ↔ Alias state a b :=
 (GeneralRebaseSupportedWorklist267.reachable_exact (next state) (support state a)
   (fun x _ => support_closed state a x) List.mem_cons_self b).trans (path_exact state a b)

def aliased (state : State roles) (a b : Nat) : Bool := decide (b ∈ aliases state a)

theorem aliased_exact (state : State roles) (a b : Nat) :
 aliased state a b = true ↔ Alias state a b :=
 by simp only [aliased,decide_eq_true_eq,aliases_exact]

end Yulang.GeneralRebaseExecutableAlias267
