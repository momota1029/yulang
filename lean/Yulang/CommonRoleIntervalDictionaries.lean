import Yulang.CommonRoleIntervalExpansionChecks
import Yulang.RoleDictionaries

/-!
# Finite dictionaries for the checked interval expansion component

The evidence uses the independent finite capture judgment at every head and
the original complete `where` list at every node. Erasure reuses the existing
finite dictionary-plan format, preserving actual declaration identities.

This is the explicitly limited structural component of interval resolution.
An incomplete expansion remains a trace with its original failure leaves;
it is never relabelled as a pending source goal. Ordinary consistency checks
are still emitted obligations, not a success assumption or a hidden condition
on solver parameters.
-/

namespace Yulang.CommonRoleIntervalDictionaries

open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal child size)
open CommonRoleIntervalCapture (total)
open CommonRoleIntervalCandidates (Candidate Selection scan scan_exact accepted_child_decreases)
open CommonRoleIntervalExpansion (Tree Checked checkDeclarations check_declarations_exact expand)

/-- A dictionary requires the independently selected head and every original
where child, using one unchanged caller-visible registry throughout. -/
inductive Dictionary (declarations : List Declaration) : Goal → Type where
  | node {goal : Goal} (candidate : Candidate)
      (unique : Selection goal (Roles.distinct declarations) [candidate])
      (children : ∀ requirement, requirement ∈ candidate.declaration.requirements →
        Dictionary declarations (child requirement (total candidate.bindings))) :
      Dictionary declarations goal

def Dictionary.erase {declarations : List Declaration} {goal : Goal}
    (dictionary : Dictionary declarations goal) : RoleDictionaries.Plan :=
  match dictionary with
  | .node candidate _ children =>
      .node candidate.declaration.toImpl
        (candidate.declaration.requirements.attach.map fun requirement =>
          (children requirement.val requirement.property).erase)

def Dictionary.trace {declarations : List Declaration} {goal : Goal}
    (dictionary : Dictionary declarations goal) : Tree :=
  match dictionary with
  | .node candidate _ children =>
      .node goal candidate
        (candidate.declaration.requirements.attach.map fun requirement =>
          (children requirement.val requirement.property).trace)

theorem Dictionary.traversal {declarations : List Declaration} {goal : Goal}
    (dictionary : Dictionary declarations goal) :
    CommonRoleIntervalExpansion.Traversal declarations goal dictionary.trace := by
  induction dictionary with
  | node candidate unique children ih =>
      exact .node _ candidate unique (fun requirement member => (children requirement member).trace) ih

/-- This finite structural test has no interpretation or model oracle. -/
def complete : Tree → Bool
  | .node _ _ children => children.attach.all (fun child => complete child.val)
  | _ => false
termination_by tree => tree
decreasing_by
  simp_wf
  have smaller := List.sizeOf_lt_of_mem child.property
  omega

theorem Dictionary.trace_complete {declarations : List Declaration} {goal : Goal}
    (dictionary : Dictionary declarations goal) : complete dictionary.trace = true := by
  induction dictionary with
  | node candidate unique children ih =>
      simp only [Dictionary.trace, complete, List.all_eq_true]
      intro tree _
      obtain ⟨requirement, _, same⟩ := List.mem_map.mp tree.property
      rw [← same]
      exact ih requirement.val requirement.property

theorem Dictionary.expansion {declarations : List Declaration} (checked : Checked declarations)
    {goal : Goal} (dictionary : Dictionary declarations goal) :
    expand declarations checked goal = dictionary.trace :=
  (CommonRoleIntervalExpansion.expand_exact declarations checked goal dictionary.trace).mpr
    dictionary.traversal

theorem Dictionary.expansion_complete {declarations : List Declaration} (checked : Checked declarations)
    {goal : Goal} (dictionary : Dictionary declarations goal) :
    complete (expand declarations checked goal) = true := by
  rw [dictionary.expansion checked]
  exact dictionary.trace_complete

theorem child_complete (declarations : List Declaration) (checked : Checked declarations)
    (goal : Goal) (candidate : Candidate)
    (unique : scan goal (Roles.distinct declarations) = some [candidate])
    (finished : complete (expand declarations checked goal) = true)
    (requirement : Nat × List CommonRoleCaptureNormalization.Form)
    (member : requirement ∈ candidate.declaration.requirements) :
    complete (expand declarations checked (child requirement (total candidate.bindings))) = true := by
  rw [CommonRoleIntervalExpansion.expand_node declarations checked goal candidate unique] at finished
  simp only [complete, List.all_eq_true] at finished
  exact finished ⟨_, List.mem_map.mpr ⟨⟨requirement, member⟩, List.mem_attach _ _, rfl⟩⟩
    (List.mem_attach _ _)

/-- Successful extraction is executable. Its recursion decreases by the
declaration checker and the same actual endpoint capture, not by a fuel. -/
def build (declarations : List Declaration) (checked : Checked declarations) (goal : Goal)
    (finished : complete (expand declarations checked goal) = true) : Dictionary declarations goal :=
  match selected : scan goal (Roles.distinct declarations) with
  | none => False.elim (by
      rw [CommonRoleIntervalExpansion.expand_outside declarations checked goal selected] at finished
      simp only [complete] at finished
      cases finished)
  | some [] => False.elim (by
      rw [CommonRoleIntervalExpansion.expand_noHead declarations checked goal selected] at finished
      simp only [complete] at finished
      cases finished)
  | some [candidate] =>
      have _member := ((scan_exact _ _ _).mp selected).member candidate (List.mem_singleton_self _)
      .node candidate ((scan_exact _ _ _).mp selected) (fun requirement member =>
        build declarations checked (child requirement (total candidate.bindings))
          (child_complete declarations checked goal candidate selected finished requirement member))
  | some (first :: second :: rest) => False.elim (by
      rw [CommonRoleIntervalExpansion.expand_overlap declarations checked goal first second rest selected] at finished
      simp only [complete] at finished
      cases finished)
termination_by size goal.arguments
decreasing_by
  exact accepted_child_decreases candidate.declaration
    (checked _ ((Roles.mem_distinct _ _).mp _member.1)) goal candidate.bindings _member.2
    requirement member

/-- Both directions concern the original goal and all original where
children. Caller-supplied fuel, rank, child success, or a point assignment
is absent from this exactness statement. -/
theorem complete_iff_dictionary (declarations : List Declaration) (checked : Checked declarations)
    (goal : Goal) :
    complete (expand declarations checked goal) = true ↔ Nonempty (Dictionary declarations goal) := by
  exact ⟨fun finished => ⟨build declarations checked goal finished⟩,
    fun ⟨dictionary⟩ => dictionary.expansion_complete checked⟩

end Yulang.CommonRoleIntervalDictionaries
