import Yulang.CommonRoleIntervalCandidates

/-!
# Total finite structural expansion of centreless interval role goals

The declaration test is the existing stable Paterson checker. The actual
finite candidate scan retains both original endpoint bindings. A unique
candidate expands its entire original where list in order, including
duplicates; every child is justified by the checked endpoint decrease.

The output is a structural expansion trace, not a completed typed role
dictionary. In particular, original endpoints need not be consistent.
Outside leaves mark the explicit capture grammar boundary; they are neither
pending source goals nor language no-implementation errors. Keeping failure
leaves in the tree avoids inventing a priority among sibling diagnostics.
-/

namespace Yulang.CommonRoleIntervalExpansion

open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal child size)
open CommonRoleIntervalCapture (total)
open CommonRoleIntervalCandidates (Candidate Selection scan scan_exact accepted_child_decreases)

def Checked (declarations : List Declaration) : Prop :=
  ∀ declaration ∈ declarations, CommonRoleStablePaterson.check declaration = true

def checkDeclarations (declarations : List Declaration) : Bool :=
  declarations.all CommonRoleStablePaterson.check

theorem check_declarations_exact (declarations : List Declaration) :
    checkDeclarations declarations = true ↔ Checked declarations := by
  exact List.all_eq_true

/-- A finite trace retains original goals, original declarations, finite
endpoint bindings, and every child. Failure leaves do not discard siblings. -/
inductive Tree where
  | outside (goal : Goal)
  | noHead (goal : Goal)
  | overlap (goal : Goal) (first second : Candidate) (rest : List Candidate)
  | node (goal : Goal) (candidate : Candidate) (children : List Tree)
  deriving Repr

def Tree.goal : Tree → Goal
  | .outside goal | .noHead goal | .overlap goal _ _ _ | .node goal _ _ => goal

/-- No fuel, candidate callback, rank premise or solver-success premise.
The recursive argument uses the actual declaration checker and capture. -/
def expand (declarations : List Declaration) (checked : Checked declarations) (goal : Goal) : Tree :=
  match selected : scan goal (Roles.distinct declarations) with
  | none => .outside goal
  | some [] => .noHead goal
  | some [candidate] =>
      have _selected := ((scan_exact _ _ _).mp selected).member candidate (List.mem_singleton_self _)
      .node goal candidate (candidate.declaration.requirements.attach.map fun requirement =>
        expand declarations checked (child requirement.val (total candidate.bindings)))
  | some (first :: second :: rest) => .overlap goal first second rest
termination_by size goal.arguments
decreasing_by
  exact accepted_child_decreases candidate.declaration
    (checked _ ((Roles.mem_distinct _ _).mp _selected.1)) goal candidate.bindings _selected.2
    requirement.val requirement.property

theorem expand_outside (declarations : List Declaration) (checked : Checked declarations) (goal : Goal)
    (outside : scan goal (Roles.distinct declarations) = none) :
    expand declarations checked goal = .outside goal := by
  rw [expand]
  split <;> simp_all

theorem expand_noHead (declarations : List Declaration) (checked : Checked declarations) (goal : Goal)
    (absent : scan goal (Roles.distinct declarations) = some []) :
    expand declarations checked goal = .noHead goal := by
  rw [expand]
  split <;> simp_all

theorem expand_node (declarations : List Declaration) (checked : Checked declarations) (goal : Goal)
    (candidate : Candidate) (unique : scan goal (Roles.distinct declarations) = some [candidate]) :
    expand declarations checked goal = .node goal candidate
      (candidate.declaration.requirements.attach.map fun requirement =>
        expand declarations checked (child requirement.val (total candidate.bindings))) := by
  rw [expand]
  split <;> simp_all
  subst_vars
  rfl

theorem expand_overlap (declarations : List Declaration) (checked : Checked declarations) (goal : Goal)
    (first second : Candidate) (rest : List Candidate)
    (multiple : scan goal (Roles.distinct declarations) = some (first :: second :: rest)) :
    expand declarations checked goal = .overlap goal first second rest := by
  rw [expand]
  split <;> simp_all

/-- Independent traversal rules. Candidate evidence is the independent
structural capture judgment, not a call to `expand` or an external oracle. -/
inductive Traversal (declarations : List Declaration) : Goal → Tree → Prop where
  | outside (goal : Goal)
      (unclassified : ∀ selected, ¬ Selection goal (Roles.distinct declarations) selected) :
      Traversal declarations goal (.outside goal)
  | noHead (goal : Goal) (absent : Selection goal (Roles.distinct declarations) []) :
      Traversal declarations goal (.noHead goal)
  | overlap (goal : Goal) (first second : Candidate) (rest : List Candidate)
      (multiple : Selection goal (Roles.distinct declarations) (first :: second :: rest)) :
      Traversal declarations goal (.overlap goal first second rest)
  | node (goal : Goal) (candidate : Candidate)
      (unique : Selection goal (Roles.distinct declarations) [candidate])
      (children : ∀ requirement, requirement ∈ candidate.declaration.requirements → Tree)
      (allWhere : ∀ requirement member,
        Traversal declarations (child requirement (total candidate.bindings)) (children requirement member)) :
      Traversal declarations goal (.node goal candidate
        (candidate.declaration.requirements.attach.map fun requirement =>
          children requirement.val requirement.property))

theorem expand_traversal (declarations : List Declaration) (checked : Checked declarations) (goal : Goal) :
    Traversal declarations goal (expand declarations checked goal) := by
  cases selected : scan goal (Roles.distinct declarations) with
  | none =>
      rw [expand_outside declarations checked goal selected]
      apply Traversal.outside
      intro candidates derivation
      have returned := (scan_exact _ _ _).mpr derivation
      rw [selected] at returned
      cases returned
  | some candidates =>
      cases candidates with
      | nil =>
          rw [expand_noHead declarations checked goal selected]
          exact .noHead goal ((scan_exact _ _ _).mp selected)
      | cons candidate rest =>
          cases rest with
          | nil =>
              rw [expand_node declarations checked goal candidate selected]
              have selection := (scan_exact _ _ _).mp selected
              have _member := selection.member candidate (List.mem_singleton_self _)
              have allWhere := Traversal.node goal candidate selection
                (fun requirement _ => expand declarations checked (child requirement (total candidate.bindings)))
                (fun requirement _ => expand_traversal declarations checked (child requirement (total candidate.bindings)))
              exact allWhere
          | cons second later =>
              rw [expand_overlap declarations checked goal candidate second later selected]
              exact .overlap goal candidate second later ((scan_exact _ _ _).mp selected)
termination_by size goal.arguments
decreasing_by
  exact accepted_child_decreases candidate.declaration
    (checked _ ((Roles.mem_distinct _ _).mp _member.1)) goal candidate.bindings _member.2
    requirement ‹requirement ∈ candidate.declaration.requirements›

theorem Traversal.exact (declarations : List Declaration) (checked : Checked declarations)
    {goal : Goal} {tree : Tree} (traversal : Traversal declarations goal tree) :
    expand declarations checked goal = tree := by
  induction traversal with
  | outside goal unclassified =>
      apply expand_outside
      cases selected : scan goal (Roles.distinct declarations) with
      | none => rfl
      | some candidates => exact False.elim (unclassified candidates ((scan_exact _ _ _).mp selected))
  | noHead goal absent => exact expand_noHead declarations checked goal ((scan_exact _ _ _).mpr absent)
  | overlap goal first second rest multiple =>
      exact expand_overlap declarations checked goal first second rest ((scan_exact _ _ _).mpr multiple)
  | node goal candidate unique children allWhere ih =>
      rw [expand_node declarations checked goal candidate ((scan_exact _ _ _).mpr unique)]
      congr 1
      apply List.map_congr_left
      intro requirement member
      exact ih requirement.val requirement.property

/-- For every finite checked registry and every finite original endpoint
goal, actual terminating expansion is exactly the independent full traversal. -/
theorem expand_exact (declarations : List Declaration) (checked : Checked declarations) (goal : Goal) (tree : Tree) :
    expand declarations checked goal = tree ↔ Traversal declarations goal tree := by
  constructor
  · rintro rfl
    exact expand_traversal declarations checked goal
  · exact Traversal.exact declarations checked

inductive Answer where
  | invalidDeclarations
  | tree (trace : Tree)
  deriving Repr

/-- The public entry point computes declaration validity itself. -/
def run (declarations : List Declaration) (goal : Goal) : Answer :=
  if accepted : checkDeclarations declarations = true then
    .tree (expand declarations ((check_declarations_exact declarations).mp accepted) goal)
  else .invalidDeclarations

theorem run_tree_exact (declarations : List Declaration) (goal : Goal) (tree : Tree) :
    run declarations goal = .tree tree ↔ Checked declarations ∧ Traversal declarations goal tree := by
  unfold run
  split
  next accepted =>
    have checked := (check_declarations_exact declarations).mp accepted
    simp only [Answer.tree.injEq, expand_exact, checked, true_and]
  next rejected =>
    have unchecked : ¬ Checked declarations := fun checked =>
      rejected ((check_declarations_exact declarations).mpr checked)
    simp [unchecked]

end Yulang.CommonRoleIntervalExpansion
