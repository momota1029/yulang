import Yulang.GeneralFiniteAliasClosure262

/-! Finite frontier search. Every recursive call strictly removes frontier
vertices from the remaining list; repeated identities are removed together. -/
namespace Yulang.GeneralFiniteAliasSearch262
open GeneralNominalSaturationState (State Alias)

def adjacent (edges : List (Nat × Nat)) (visited : List Nat) (vertex : Nat) : Bool :=
 edges.any fun edge => decide
   ((edge.1 ∈ visited ∧ edge.2 = vertex) ∨ (edge.2 ∈ visited ∧ edge.1 = vertex))

theorem adjacent_iff (edges : List (Nat × Nat)) (visited : List Nat) (vertex : Nat) :
 adjacent edges visited vertex = true ↔ ∃ edge ∈ edges,
 (edge.1 ∈ visited ∧ edge.2 = vertex) ∨ (edge.2 ∈ visited ∧ edge.1 = vertex) := by
 simp only [adjacent,List.any_eq_true,decide_eq_true_eq]

def frontier (edges : List (Nat × Nat)) (remaining visited : List Nat) : List Nat :=
 remaining.filter (adjacent edges visited)

def rest (edges : List (Nat × Nat)) (remaining visited : List Nat) : List Nat :=
 remaining.filter fun vertex => !(adjacent edges visited vertex)

theorem filter_strict (values : List Nat) (keep : Nat → Bool)
 (changed : values.filter keep ≠ values) : (values.filter keep).length < values.length := by
 induction values with
 | nil => exact False.elim (changed rfl)
 | cons first rest ih =>
   by_cases kept : keep first = true
   · have tail : rest.filter keep ≠ rest := by
       intro equal
       apply changed
       simp only [List.filter_cons,kept,ite_true,equal]
     simpa only [List.filter_cons,kept,ite_true,List.length_cons] using Nat.succ_lt_succ (ih tail)
   · have small := List.length_filter_le keep rest
     simp only [List.filter_cons, kept, Bool.false_eq_true, ↓reduceIte, List.length_cons]
     omega

def search (edges : List (Nat × Nat)) (remaining visited : List Nat) : List Nat :=
 if _same : rest edges remaining visited = remaining then visited
 else search edges (rest edges remaining visited) (visited ++ frontier edges remaining visited)
termination_by remaining.length
decreasing_by exact filter_strict remaining _ _same

def Covered (edges : List (Nat × Nat)) (remaining visited : List Nat) : Prop :=
 ∀ edge ∈ edges, (edge.1 ∈ visited ∨ edge.1 ∈ remaining) ∧ (edge.2 ∈ visited ∨ edge.2 ∈ remaining)

theorem split_remaining (edges : List (Nat × Nat)) (remaining visited : List Nat) (vertex : Nat)
 (member : vertex ∈ remaining) : vertex ∈ frontier edges remaining visited ∨ vertex ∈ rest edges remaining visited := by
 by_cases near : adjacent edges visited vertex = true
 · exact Or.inl (List.mem_filter.mpr ⟨member,near⟩)
 · exact Or.inr (List.mem_filter.mpr ⟨member,by simpa using near⟩)

theorem covered_next (edges : List (Nat × Nat)) (remaining visited : List Nat)
 (covered : Covered edges remaining visited) :
 Covered edges (rest edges remaining visited) (visited ++ frontier edges remaining visited) := by
 intro edge member
 have move (vertex : Nat) : (vertex ∈ visited ∨ vertex ∈ remaining) →
     vertex ∈ visited ++ frontier edges remaining visited ∨ vertex ∈ rest edges remaining visited := by
   rintro (old | pending)
   · exact Or.inl (List.mem_append_left _ old)
   · rcases split_remaining edges remaining visited vertex pending with added | pending
     · exact Or.inl (List.mem_append_right _ added)
     · exact Or.inr pending
 exact ⟨move _ (covered edge member).1,move _ (covered edge member).2⟩

theorem frontier_sound (state : State roles) (root : Nat) (remaining visited : List Nat)
 (sound : ∀ vertex ∈ visited, Alias state root vertex) :
 ∀ vertex ∈ frontier state.aliases remaining visited, Alias state root vertex := by
 intro vertex member
 obtain ⟨_,near⟩ := List.mem_filter.mp member
 obtain ⟨edge,edgeMem,forward | reverse⟩ := (adjacent_iff ..).mp near
 · obtain ⟨previous,equal⟩ := forward
   rw [← equal]
   exact .trans (sound _ previous) (.edge edgeMem)
 · obtain ⟨previous,equal⟩ := reverse
   rw [← equal]
   exact .trans (sound _ previous) (.symm (.edge edgeMem))

theorem terminal_closed (edges : List (Nat × Nat)) (remaining visited : List Nat)
 (covered : Covered edges remaining visited) (same : rest edges remaining visited = remaining) :
 ∀ edge ∈ edges, edge.1 ∈ visited ↔ edge.2 ∈ visited := by
 have absent (vertex : Nat) (member : vertex ∈ remaining) : adjacent edges visited vertex ≠ true := by
   have kept : vertex ∈ rest edges remaining visited := by rw [same]; exact member
   simpa [rest] using (List.mem_filter.mp kept).2
 intro edge edgeMem
 constructor
 · intro first
   rcases (covered edge edgeMem).2 with present | pending
   · exact present
   · exact False.elim (absent _ pending ((adjacent_iff ..).mpr ⟨edge,edgeMem,Or.inl ⟨first,rfl⟩⟩))
 · intro last
   rcases (covered edge edgeMem).1 with present | pending
   · exact present
   · exact False.elim (absent _ pending ((adjacent_iff ..).mpr ⟨edge,edgeMem,Or.inr ⟨last,rfl⟩⟩))

theorem search_correct (state : State roles) (root : Nat) (remaining visited : List Nat)
 (rootMem : root ∈ visited) (sound : ∀ vertex ∈ visited, Alias state root vertex)
 (covered : Covered state.aliases remaining visited) :
 root ∈ search state.aliases remaining visited ∧
 (∀ vertex ∈ search state.aliases remaining visited, Alias state root vertex) ∧
 (∀ edge ∈ state.aliases, edge.1 ∈ search state.aliases remaining visited ↔
    edge.2 ∈ search state.aliases remaining visited) := by
 rw [search]
 split
 · rename_i same
   exact ⟨rootMem,sound,terminal_closed _ _ _ covered same⟩
 · rename_i changed
   apply search_correct state root
   · exact List.mem_append_left _ rootMem
   · intro vertex member
     rcases List.mem_append.mp member with old | new
     · exact sound vertex old
     · exact frontier_sound state root remaining visited sound vertex new
   · exact covered_next _ _ _ covered
termination_by remaining.length
decreasing_by exact filter_strict remaining _ (by assumption)

def allVertices (edges : List (Nat × Nat)) : List Nat :=
 edges.flatMap fun edge => [edge.1,edge.2]

def component (edges : List (Nat × Nat)) (root : Nat) : List Nat :=
 search edges (allVertices edges) [root]

theorem component_exact (state : State roles) (root vertex : Nat) :
 vertex ∈ component state.aliases root ↔ Alias state root vertex := by
 have cover : Covered state.aliases (allVertices state.aliases) [root] := by
   intro edge member
   exact ⟨Or.inr (List.mem_flatMap.mpr ⟨edge,member,by simp⟩),
     Or.inr (List.mem_flatMap.mpr ⟨edge,member,by simp⟩)⟩
 obtain ⟨rootMem,sound,closed⟩ := search_correct state root (allVertices state.aliases) [root]
   (by simp) (by intro vertex member; cases List.mem_singleton.mp member; exact .refl _) cover
 constructor
 · exact sound vertex
 · intro related
   have same := GeneralFiniteAliasClosure262.alias_preserves_cut state
     (component state.aliases root) ((GeneralFiniteAliasClosure262.closed_iff ..).mpr closed) related
   exact same.mp rootMem

def connected (edges : List (Nat × Nat)) (root target : Nat) : Bool :=
 (component edges root).contains target

theorem exact (state : State roles) (root target : Nat) :
 connected state.aliases root target = true ↔ Alias state root target := by
 simp only [connected,List.contains_iff_mem,component_exact]
theorem reference_eq (state : State roles) (root target : Nat) :
 connected state.aliases root target = GeneralFiniteAliasClosure262.connected state.aliases root target := by
 apply Bool.eq_iff_iff.mpr
 rw [exact,GeneralFiniteAliasClosure262.exact]

end Yulang.GeneralFiniteAliasSearch262
