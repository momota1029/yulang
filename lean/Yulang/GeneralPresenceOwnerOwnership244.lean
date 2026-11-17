import Yulang.GeneralPresenceOwnerTable244
import Yulang.GeneralPresenceOwnerSequence244
namespace Yulang.GeneralPresenceOwnerOwnership244
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceOwnerRewrite244
open GeneralPresenceOwnerSequence244
open GeneralPresenceOwnerTable244
variable {Name Owner : Type} [DecidableEq Name] [DecidableEq Owner]

def TargetsWithin (fresh old : List (Entry Name)) : Prop :=
 ∀ entry ∈ fresh, ∃ original ∈ old, original.1 = entry.1

def DisjointState (state : State Name Owner) : Prop :=
 ∀ first ∈ state.owners, ∀ last ∈ state.owners, first ≠ last →
 DisjointTargets (state.entries first) (state.entries last)

omit [DecidableEq Name] [DecidableEq Owner] in
theorem disjoint_symm (given : DisjointTargets first last) : DisjointTargets last first :=
 fun entry member other included equal => given other included entry member equal.symm

omit [DecidableEq Name] [DecidableEq Owner] in
theorem disjoint_within (within : TargetsWithin fresh old) (given : DisjointTargets old other) :
 DisjointTargets fresh other := by
 intro entry member target targetMem
 obtain ⟨original,originalMem,equal⟩ := within entry member
 rw [← equal]
 exact given original originalMem target targetMem

omit [DecidableEq Name] [DecidableEq Owner] in
theorem disjoint_transform_both (first last : List (Entry Name)) (mapping : Name → CompTerm Name)
 (given : DisjointTargets first last) : DisjointTargets (transform mapping first) (transform mapping last) := by
 intro entry member target targetMem
 obtain ⟨original,originalMem,rfl⟩ := List.mem_map.mp member
 obtain ⟨other,otherMem,rfl⟩ := List.mem_map.mp targetMem
 exact given original originalMem other otherMem

theorem rebase_disjoint (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (given : DisjointState state) (within : TargetsWithin fresh (state.entries owner)) :
 DisjointState (rebase state owner fresh) := by
 intro first firstMem last lastMem different
 by_cases one : first = owner
 · subst first
   rw [rebase_at,rebase_other state owner last fresh (Ne.symm different)]
   exact disjoint_transform _ _ _ (disjoint_within within (given owner firstMem last lastMem different))
 · by_cases two : last = owner
   · subst last
     rw [rebase_other state owner first fresh one,rebase_at]
     apply disjoint_symm
     exact disjoint_transform _ _ _ (disjoint_within within (given owner lastMem first firstMem (Ne.symm different)))
   · rw [rebase_other state owner first fresh one,rebase_other state owner last fresh two]
     exact disjoint_transform_both _ _ _ (given first firstMem last lastMem different)
end Yulang.GeneralPresenceOwnerOwnership244
