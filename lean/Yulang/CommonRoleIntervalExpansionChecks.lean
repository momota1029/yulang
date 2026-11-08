import Yulang.CommonRoleIntervalExpansion

/-!
# Ordinary consistency obligations retained by finite interval expansion

Structural expansion does not decide lower <: upper. Every original goal
interval and every stored finite capture interval is returned as an existing
ordinary `.check` constraint. All children and all overlap capture tables are
retained. No centre, fresh slot, parameter restriction, or semantic oracle is
introduced. Repeated head captures remain outside the preceding grammar;
their general reconciliation/cross constraints are not replaced by this pass.
-/

namespace Yulang.CommonRoleIntervalExpansionChecks

open CommonRoleCaptureNormalization (Form)
open CommonRoleIntervalPaterson (Argument)
open CommonRoleIntervalCapture (Bindings)
open CommonRoleIntervalExpansion (Tree)
open LayerBoundTemplates (Problem)

def intervalChecks (arguments : List Argument) : Problem n Form :=
  arguments.map fun argument => .check argument.1 argument.2

def ConsistentArguments (evaluate : Form → Common.Ty) (arguments : List Argument) : Prop :=
  ∀ argument ∈ arguments, Common.Subtype (evaluate argument.1) (evaluate argument.2)

theorem interval_checks_exact (evaluate : Form → Common.Ty) (arguments : List Argument)
    (values : Fin n → Common.Ty) :
    CommonBoundCoalescing.Models evaluate (intervalChecks arguments) values ↔
      ConsistentArguments evaluate arguments := by
  constructor
  · intro model argument present
    exact model (.check argument.1 argument.2) (List.mem_map.mpr ⟨argument, present, rfl⟩)
  · intro valid constraint present
    obtain ⟨argument, member, rfl⟩ := List.mem_map.mp present
    exact valid argument member

def capturedArguments (bindings : Bindings) : List Argument := bindings.map Prod.snd

/-- Includes captures of every head-overlap candidate. A head-overlap trace
does not imply those ordinary obligations have already been discharged. -/
def localArguments : Tree → List Argument
  | .outside goal | .noHead goal => goal.arguments
  | .overlap goal first second rest => goal.arguments ++
      (first :: second :: rest).flatMap fun candidate => capturedArguments candidate.bindings
  | .node goal candidate _ => goal.arguments ++ capturedArguments candidate.bindings

def constraints : Tree → Problem n Form
  | .outside goal => intervalChecks goal.arguments
  | .noHead goal => intervalChecks goal.arguments
  | .overlap goal first second rest => intervalChecks (localArguments (.overlap goal first second rest))
  | .node goal candidate children =>
      intervalChecks (localArguments (.node goal candidate children)) ++ children.flatMap constraints

/-- Independent semantic consistency of each stored original interval.
This is the meaning of emitted obligations, not a condition on parameters. -/
def Consistent (evaluate : Form → Common.Ty) : Tree → Prop
  | .outside goal => ConsistentArguments evaluate goal.arguments
  | .noHead goal => ConsistentArguments evaluate goal.arguments
  | .overlap goal first second rest => ConsistentArguments evaluate (localArguments (.overlap goal first second rest))
  | .node goal candidate children =>
      ConsistentArguments evaluate (localArguments (.node goal candidate children)) ∧
        ∀ child ∈ children, Consistent evaluate child

theorem models_append (evaluate : Form → Common.Ty) (first last : Problem n Form)
    (values : Fin n → Common.Ty) :
    CommonBoundCoalescing.Models evaluate (first ++ last) values ↔
      CommonBoundCoalescing.Models evaluate first values ∧ CommonBoundCoalescing.Models evaluate last values := by
  simp [CommonBoundCoalescing.Models, List.mem_append, or_imp, forall_and]

theorem models_children (evaluate : Form → Common.Ty) (children : List Tree)
    (values : Fin n → Common.Ty) :
    CommonBoundCoalescing.Models evaluate (children.flatMap constraints) values ↔
      ∀ child ∈ children, CommonBoundCoalescing.Models evaluate (constraints child) values := by
  constructor
  · intro model child member constraint present
    exact model constraint (List.mem_flatMap.mpr ⟨child, member, present⟩)
  · intro all constraint present
    obtain ⟨child, member, included⟩ := List.mem_flatMap.mp present
    exact all child member constraint included

/-- All original goal and capture bounds survive as ordinary checks at
every visited node, for arbitrary interpretations of every free Form name. -/
theorem constraints_exact (evaluate : Form → Common.Ty) (tree : Tree) (values : Fin n → Common.Ty) :
    CommonBoundCoalescing.Models evaluate (constraints tree) values ↔ Consistent evaluate tree := by
  cases tree with
  | outside goal => simpa only [constraints, Consistent] using interval_checks_exact evaluate goal.arguments values
  | noHead goal => simpa only [constraints, Consistent] using interval_checks_exact evaluate goal.arguments values
  | overlap goal first second rest =>
      simpa only [constraints, Consistent] using
        interval_checks_exact evaluate (localArguments (.overlap goal first second rest)) values
  | node goal candidate children =>
      rw [constraints, Consistent, models_append, interval_checks_exact, models_children]
      apply and_congr_right
      intro _
      exact forall_congr' fun child => forall_congr' fun _ => constraints_exact evaluate child values
termination_by tree

theorem original_goal_checks (tree : Tree) (argument : Argument) (member : argument ∈ tree.goal.arguments) :
    (LayerBoundTemplates.Constraint.check argument.1 argument.2 : LayerBoundTemplates.Constraint n Form) ∈ constraints tree := by
  cases tree <;> simp only [Tree.goal] at member <;>
    simp only [constraints, intervalChecks, localArguments]
  case outside goal => exact List.mem_map.mpr ⟨argument, member, rfl⟩
  case noHead goal => exact List.mem_map.mpr ⟨argument, member, rfl⟩
  case overlap goal first second rest =>
      exact List.mem_map.mpr ⟨argument, List.mem_append_left _ member, rfl⟩
  case node goal candidate children =>
      exact List.mem_append_left _ (List.mem_map.mpr ⟨argument, List.mem_append_left _ member, rfl⟩)

end Yulang.CommonRoleIntervalExpansionChecks
