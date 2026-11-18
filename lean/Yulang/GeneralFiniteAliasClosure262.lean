import Yulang.GeneralNominalSaturationState

/-! An executable, exponential reference decision procedure for a finite alias
snapshot. It enumerates cuts by structural recursion on the remaining vertices.
This is a baseline for correctness, not a claim of efficient graph search. -/
namespace Yulang.GeneralFiniteAliasClosure262
open GeneralNominalSaturationState (State Alias)

/-- Every iteration removes the head of the remaining finite vertex list. -/
def cuts : List Nat → List (List Nat)
 | [] => [[]]
 | vertex :: rest => cuts rest ++ (cuts rest).map (vertex :: ·)

/-- The reference procedure deliberately enumerates exponentially many cuts.
Repeated vertex names are retained, so this bound includes redundant cuts. -/
theorem cuts_length (remaining : List Nat) : (cuts remaining).length = 2 ^ remaining.length := by
 induction remaining with
 | nil => simp [cuts]
 | cons first rest ih =>
   simp only [cuts,List.length_append,List.length_map,ih,List.length_cons,Nat.pow_succ]
   omega

theorem filtered_is_cut (vertices : List Nat) (keep : Nat → Bool) :
 vertices.filter keep ∈ cuts vertices := by
 induction vertices with
 | nil => simp [cuts]
 | cons first rest ih =>
   by_cases retained : keep first = true
   · simp only [List.filter_cons,retained,ite_true,cuts,List.mem_append]
     exact Or.inr (List.mem_map.mpr ⟨rest.filter keep,ih,rfl⟩)
   · simp only [List.filter_cons,retained,Bool.false_eq_true,↓reduceIte,cuts,List.mem_append]
     exact Or.inl ih

/-- Query endpoints are included even when isolated and absent from all edges. -/
def vertices (edges : List (Nat × Nat)) (root target : Nat) : List Nat :=
 root :: target :: edges.flatMap (fun edge => [edge.1,edge.2])

def closed (edges : List (Nat × Nat)) (cut : List Nat) : Bool :=
 edges.all fun edge => decide (edge.1 ∈ cut ↔ edge.2 ∈ cut)

def passes (edges : List (Nat × Nat)) (root target : Nat) (cut : List Nat) : Bool :=
 decide (root ∈ cut → closed edges cut = true → target ∈ cut)

def connected (edges : List (Nat × Nat)) (root target : Nat) : Bool :=
 (cuts (vertices edges root target)).all (passes edges root target)

theorem closed_iff (edges : List (Nat × Nat)) (cut : List Nat) :
 closed edges cut = true ↔ ∀ edge ∈ edges, edge.1 ∈ cut ↔ edge.2 ∈ cut := by
 simp only [closed,List.all_eq_true,decide_eq_true_eq]

theorem connected_iff_cuts (edges : List (Nat × Nat)) (root target : Nat) :
 connected edges root target = true ↔
 ∀ cut ∈ cuts (vertices edges root target), root ∈ cut → closed edges cut = true → target ∈ cut := by
 simp only [connected,List.all_eq_true,passes,decide_eq_true_eq]

theorem alias_preserves_cut (state : State roles) (cut : List Nat)
 (isClosed : closed state.aliases cut = true) (related : Alias state first last) :
 first ∈ cut ↔ last ∈ cut := by
 induction related with
 | refl => exact Iff.rfl
 | edge member => exact (closed_iff _ _).mp isClosed _ member
 | symm _ ih => exact ih.symm
 | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem sound (state : State roles) (root target : Nat) (related : Alias state root target) :
 connected state.aliases root target = true := by
 apply (connected_iff_cuts ..).mpr
 intro cut _ member isClosed
 exact (alias_preserves_cut state cut isClosed related).mp member

theorem edge_first_vertex (edges : List (Nat × Nat)) (root target : Nat)
 (edge : Nat × Nat) (member : edge ∈ edges) : edge.1 ∈ vertices edges root target := by
 simp only [vertices,List.mem_cons]
 exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨edge,member,by simp⟩))

theorem edge_last_vertex (edges : List (Nat × Nat)) (root target : Nat)
 (edge : Nat × Nat) (member : edge ∈ edges) : edge.2 ∈ vertices edges root target := by
 simp only [vertices,List.mem_cons]
 exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨edge,member,by simp⟩))

theorem complete (state : State roles) (root target : Nat)
 (accepted : connected state.aliases root target = true) : Alias state root target := by
 classical
 let domain := vertices state.aliases root target
 let cut := domain.filter (fun vertex => decide (Alias state root vertex))
 have cut_mem : cut ∈ cuts domain := filtered_is_cut ..
 have cut_exact (vertex : Nat) : vertex ∈ cut ↔ vertex ∈ domain ∧ Alias state root vertex := by
   simp only [cut,List.mem_filter,decide_eq_true_eq]
 have root_mem : root ∈ cut := (cut_exact root).mpr ⟨by simp [domain,vertices],.refl _⟩
 have isClosed : closed state.aliases cut = true := by
   apply (closed_iff ..).mpr
   intro edge member
   constructor
   · intro included
     exact (cut_exact edge.2).mpr ⟨edge_last_vertex _ _ _ _ member,
       .trans ((cut_exact edge.1).mp included).2 (.edge member)⟩
   · intro included
     exact (cut_exact edge.1).mpr ⟨edge_first_vertex _ _ _ _ member,
       .trans ((cut_exact edge.2).mp included).2 (.symm (.edge member))⟩
 have target_mem := (connected_iff_cuts ..).mp accepted cut cut_mem root_mem isClosed
 exact ((cut_exact target).mp target_mem).2

/-- Exact for all states and all natural-number identities, with no coverage
assumption. Only the finite edge list is read; packets and contexts are irrelevant. -/
theorem exact (state : State roles) (root target : Nat) :
 connected state.aliases root target = true ↔ Alias state root target :=
 ⟨complete state root target,sound state root target⟩
end Yulang.GeneralFiniteAliasClosure262
