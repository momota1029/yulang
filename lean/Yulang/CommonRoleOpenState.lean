import Yulang.CommonRoleOpenConstraints

/-! Retaining and recollecting actual open capture updates. These operations
thread the ordinary constraint state, rather than silently dropping child
constraints. Source frontier production remains a separate obligation. -/
namespace Yulang.CommonRoleOpenState
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateConstraints (Bindings Compatible generate)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

/-- Keep the complete prior state, then append every generated self/cross atom. -/
def add (s : State n) (bindings : Bindings n) : State n :=
  let grammar := CommonRoleCandidateConstraints.generated_grammar bindings
  ⟨s.atoms ++ generate bindings, s.child.append grammar.1,
    s.width.append grammar.2.1, s.rows.append grammar.2.2⟩

theorem add_exact (s : State n) (bindings : Bindings n)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (add s bindings).atoms ↔
      All Common.model assignment s.atoms ∧ Compatible bindings assignment := by
  exact (PresenceNormalForm.all_append _ _ _ _).trans
    (and_congr Iff.rfl (CommonRoleCandidateConstraints.generate_exact bindings assignment))

/-- Accumulate an already supplied ordered update list. This does not yet
re-run a sibling producer or recollect the parent frontier after an update. -/
def recollect (s : State n) : List (Bindings n) → State n
  | [] => s
  | first :: rest => recollect (add s first) rest

/-- Independent state transition: no reference to `recollect`. -/
inductive Recollect : State n → List (Bindings n) → List (PresenceNormalForm.Atom (Fin n)) → Prop where
  | nil : Recollect s [] s.atoms
  | cons : Recollect (add s first) rest atoms → Recollect s (first :: rest) atoms

theorem recollect_sound (s : State n) (updates : List (Bindings n)) :
    Recollect s updates (recollect s updates).atoms := by
  induction updates generalizing s with
  | nil => exact .nil
  | cons first rest ih => exact .cons (ih (add s first))

theorem recollect_complete (h : Recollect s updates atoms) :
    (recollect s updates).atoms = atoms := by
  induction h with
  | nil => rfl
  | cons _ ih => exact ih

theorem recollect_exact (s : State n) (updates : List (Bindings n)) (atoms) :
    (recollect s updates).atoms = atoms ↔ Recollect s updates atoms :=
  ⟨fun h => h ▸ recollect_sound s updates, recollect_complete⟩

/-- All parent and sibling constraints are retained at the SAME assignment.
No fresh independent valuation is chosen for each child. -/
theorem recollect_models (s : State n) (updates : List (Bindings n))
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (recollect s updates).atoms ↔
      All Common.model assignment s.atoms ∧ ∀ bindings ∈ updates, Compatible bindings assignment := by
  induction updates generalizing s with
  | nil => simp [recollect]
  | cons first rest ih =>
    rw [recollect, ih, add_exact]
    simp only [List.forall_mem_cons]
    exact and_assoc

/-- The complete generated atom stream is retained literally, in order. -/
theorem recollect_atoms (s : State n) (updates : List (Bindings n)) :
    (recollect s updates).atoms = s.atoms ++ updates.flatMap generate := by
  induction updates generalizing s with
  | nil => simp [recollect]
  | cons first rest ih =>
    simp only [recollect, ih, add, List.flatMap_cons, List.append_assoc]

/-- Appending later sibling updates never discards a parent's earlier facts. -/
theorem recollect_preserves_prefix (s : State n) (before after : List (Bindings n))
    (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment (recollect s (before ++ after)).atoms) :
    All Common.model assignment (recollect s before).atoms := by
  rw [recollect_models] at model ⊢
  exact ⟨model.1, fun binding member => model.2 binding (List.mem_append_left after member)⟩

/-- Re-run the actual unrestricted ordinary solver on the retained state. -/
def solve (s : State n) (updates : List (Bindings n)) :=
  CommonRoleCandidateConstraints.solve (recollect s updates).atoms []

theorem solve_all_instances_exact (s : State n) (updates : List (Bindings n))
    (assignment : Fin n → Comp Common.model) :
    (All Common.model assignment s.atoms ∧ ∀ bindings ∈ updates, Compatible bindings assignment) ↔
      ∃ scheme ∈ solve s updates, ∃ rows : Fin n → Common.Row,
        ∃ parameters : scheme.Parameters,
          CommonDeclaredNominalSourceFamily.AssignmentEquivalent
            (scheme.instantiate rows parameters) assignment := by
  have exactSolver := CommonRoleCandidateConstraints.solve_all_instances_exact
    (recollect s updates).atoms [] (recollect s updates).child
    (recollect s updates).width (recollect s updates).rows assignment
  have empty : Compatible ([] : Bindings n) assignment := by
    intro name member; simp [CommonRoleCandidateConstraints.names] at member
  simpa only [empty, and_true, solve, recollect_models] using exactSolver

/-- Contradicting siblings are checked together, not accepted using different
models. This uses the actual solver's empty-family characterization. -/
theorem solve_empty_exact (s : State n) (updates : List (Bindings n)) :
    solve s updates = [] ↔
      ¬ ∃ assignment, All Common.model assignment s.atoms ∧
        ∀ bindings ∈ updates, Compatible bindings assignment := by
  have exactSolver := CommonRoleCandidateConstraints.solve_empty_exact
    (recollect s updates).atoms [] (recollect s updates).child
    (recollect s updates).width (recollect s updates).rows
  have empty : ∀ assignment : Fin n → Comp Common.model, Compatible ([] : Bindings n) assignment := by
    intro assignment name member; simp [CommonRoleCandidateConstraints.names] at member
  simpa only [empty, and_true, solve, recollect_models] using exactSolver

end Yulang.CommonRoleOpenState
