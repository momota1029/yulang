import Yulang.ModuleVisibility
import Yulang.RoleDictionaries

/-!
# File-visible dictionary elaboration and transport

This module composes the existing file selector with the executable rigid-goal
dictionary elaborator. Every selected node has an accessible declaration in
the current or a loaded file. Hidden declarations cannot change the result,
and visible order or repeated imports cannot change the complete tree.

Compiled evidence retains the source file's chosen tree when passed to another
file, even when ordinary resolution there would choose another impl or report
ambiguity. Module access remains an input from name resolution. Impl keys are
the declaration identities supplied to `Roles`: distinct source declarations
must have distinct identities, while repeated imports preserve identity.
Source method bodies and unknown-type inference are outside this adapter.
-/

namespace Yulang.ModuleDictionaries

open Roles RoleDictionaries ModuleVisibility

def elaborateAt [DecidableEq File] (scope : FileScope File) (catalog : List (Declaration File))
    (wellFormed : WellFormed (scope.select catalog)) (goal : Goal) : Answer :=
  elaborate (scope.select catalog) wellFormed goal

@[simp] theorem elaborateAt_status [DecidableEq File] (scope : FileScope File)
    (catalog : List (Declaration File)) (wellFormed : WellFormed (scope.select catalog)) (goal : Goal) :
    (elaborateAt scope catalog wellFormed goal).status = resolveAt scope catalog wellFormed goal :=
  elaborate_status (scope.select catalog) wellFormed goal

theorem elaborateAt_success_iff [DecidableEq File] (scope : FileScope File)
    (catalog : List (Declaration File)) (wellFormed : WellFormed (scope.select catalog))
    (goal : Goal) (plan : Plan) :
    elaborateAt scope catalog wellFormed goal = .resolved plan ↔
      ∃ dictionary : Dictionary (scope.select catalog) goal, dictionary.erase = plan :=
  elaborate_success_iff (scope.select catalog) wellFormed goal plan

/-- This ranges over every node in the returned tree, not just the root impl. -/
theorem elaborateAt_all_origins [DecidableEq File] (scope : FileScope File)
    (catalog : List (Declaration File)) (wellFormed : WellFormed (scope.select catalog))
    (goal : Goal) (plan : Plan) (success : elaborateAt scope catalog wellFormed goal = .resolved plan) :
    ∀ implementation ∈ plan.declarations,
      ∃ entry ∈ catalog, entry.implementation = implementation ∧
        (entry.owner = scope.current ∨ entry.owner ∈ scope.loaded) ∧ scope.accessible entry = true := by
  intro implementation member
  exact scope.selected_origin catalog implementation
    (elaborate_all_visible (scope.select catalog) wellFormed goal plan success implementation member)

theorem elaborateAt_congr [DecidableEq File] (scope : FileScope File)
    {left right : List (Declaration File)} (same : SameVisible scope left right)
    (leftWellFormed : WellFormed (scope.select left)) (rightWellFormed : WellFormed (scope.select right))
    (goal : Goal) :
    elaborateAt scope left leftWellFormed goal = elaborateAt scope right rightWellFormed goal :=
  elaborate_congr (selected_membership_congr scope same) leftWellFormed rightWellFormed goal

theorem elaborateAt_append_hidden [DecidableEq File] (scope : FileScope File)
    (catalog hidden : List (Declaration File))
    (invisible : ∀ entry ∈ hidden, scope.visible entry = false)
    (wellFormed : WellFormed (scope.select catalog))
    (extendedWellFormed : WellFormed (scope.select (catalog ++ hidden))) (goal : Goal) :
    elaborateAt scope (catalog ++ hidden) extendedWellFormed goal =
      elaborateAt scope catalog wellFormed goal := by
  apply elaborate_congr
  intro implementation
  rw [scope.select_append_hidden catalog hidden invisible]

theorem elaborateAt_permutation [DecidableEq File] (scope : FileScope File)
    {left right : List (Declaration File)} (permutation : left.Perm right)
    (leftWellFormed : WellFormed (scope.select left)) (rightWellFormed : WellFormed (scope.select right))
    (goal : Goal) :
    elaborateAt scope left leftWellFormed goal = elaborateAt scope right rightWellFormed goal :=
  elaborateAt_congr scope (fun _ _ => permutation.mem_iff) leftWellFormed rightWellFormed goal

theorem elaborateAt_duplicate_catalog [DecidableEq File] (scope : FileScope File)
    (catalog : List (Declaration File)) (wellFormed : WellFormed (scope.select catalog))
    (duplicateWellFormed : WellFormed (scope.select (catalog ++ catalog))) (goal : Goal) :
    elaborateAt scope (catalog ++ catalog) duplicateWellFormed goal =
      elaborateAt scope catalog wellFormed goal :=
  elaborateAt_congr scope (fun _ _ => by simp) duplicateWellFormed wellFormed goal

def compileAt [DecidableEq File] (scope : FileScope File) (catalog : List (Declaration File))
    (wellFormed : WellFormed (scope.select catalog)) (goal : Goal)
    (success : resolveAt scope catalog wellFormed goal = .resolved) : Compiled goal :=
  compileResolved (scope.select catalog) wellFormed goal success

theorem compileAt_provenance [DecidableEq File] (scope : FileScope File)
    (catalog : List (Declaration File)) (wellFormed : WellFormed (scope.select catalog))
    (goal : Goal) (success : resolveAt scope catalog wellFormed goal = .resolved) :
    elaborateAt scope catalog wellFormed goal =
      .resolved (compileAt scope catalog wellFormed goal success).plan :=
  (compileAt scope catalog wellFormed goal success).provenance

theorem compileAt_all_origins [DecidableEq File] (scope : FileScope File)
    (catalog : List (Declaration File)) (wellFormed : WellFormed (scope.select catalog))
    (goal : Goal) (success : resolveAt scope catalog wellFormed goal = .resolved) :
    ∀ implementation ∈ (compileAt scope catalog wellFormed goal success).plan.declarations,
      ∃ entry ∈ catalog, entry.implementation = implementation ∧
        (entry.owner = scope.current ∨ entry.owner ∈ scope.loaded) ∧ scope.accessible entry = true :=
  elaborateAt_all_origins scope catalog wellFormed goal _
    (compileAt_provenance scope catalog wellFormed goal success)

def useEvidenceAt [DecidableEq File] {goals : List (RoleConstraints.Predicate Term)}
    (evidence : Evidence goals) (scope : FileScope File) (catalog : List (Declaration File))
    (wellFormed : WellFormed (scope.select catalog)) (goal : RoleConstraints.Predicate Term) : Answer :=
  useEvidence evidence (scope.select catalog) wellFormed goal

theorem useEvidenceAt_exact [DecidableEq File] {goals : List (RoleConstraints.Predicate Term)}
    (evidence : Evidence goals) (scope : FileScope File) (catalog : List (Declaration File))
    (wellFormed : WellFormed (scope.select catalog)) (goal : RoleConstraints.Predicate Term) :
    (useEvidenceAt evidence scope catalog wellFormed goal).status = .resolved ↔
      RoleConstraints.WithEvidence
        (fun predicate => RoleConstraints.Resolves (scope.select catalog) predicate.toGoal) goals goal :=
  useEvidence_exact evidence (scope.select catalog) wellFormed goal

theorem useEvidenceAt_preserves [DecidableEq File] {goals : List (RoleConstraints.Predicate Term)}
    (evidence : Evidence goals) (goal : RoleConstraints.Predicate Term) (compiled : Compiled goal.toGoal)
    (supplied : evidence.lookup goal = some compiled)
    (receiver : FileScope File) (catalog : List (Declaration File))
    (wellFormed : WellFormed (receiver.select catalog)) :
    useEvidenceAt evidence receiver catalog wellFormed goal = .resolved compiled.plan :=
  useEvidence_preserves evidence goal compiled supplied (receiver.select catalog) wellFormed

/-- Evidence produced in one file is used as the same tree in every receiving
file. The receiver's catalog is unrestricted and need not contain its impls. -/
theorem crossing_file_preserves_dictionary [DecidableEq Source] [DecidableEq Receiver]
    (source : FileScope Source) (sourceCatalog : List (Declaration Source))
    (sourceWellFormed : WellFormed (source.select sourceCatalog)) (goal : RoleConstraints.Predicate Term)
    (success : resolveAt source sourceCatalog sourceWellFormed goal.toGoal = .resolved)
    (receiver : FileScope Receiver) (receiverCatalog : List (Declaration Receiver))
    (receiverWellFormed : WellFormed (receiver.select receiverCatalog)) :
    let compiled := compileAt source sourceCatalog sourceWellFormed goal.toGoal success
    useEvidenceAt (Evidence.singleton goal compiled) receiver receiverCatalog receiverWellFormed goal =
      .resolved compiled.plan :=
  useEvidenceAt_preserves _ goal _ (Evidence.singleton_lookup _ _) receiver receiverCatalog receiverWellFormed

namespace Examples

open RoleVisibility.Examples

def source : FileScope Nat := ⟨0, [], fun _ => true⟩
def receiver : FileScope Nat := ⟨1, [], fun _ => true⟩
def jointlyLoaded : FileScope Nat := ⟨2, [0, 1], fun _ => true⟩
def catalog : List (Declaration Nat) := [⟨0, firstImpl⟩, ⟨1, secondImpl⟩]

theorem source_wellFormed : WellFormed (source.select catalog) := first_wellFormed
theorem receiver_wellFormed : WellFormed (receiver.select catalog) := second_wellFormed
theorem jointlyLoaded_wellFormed : WellFormed (jointlyLoaded.select catalog) := both_wellFormed

theorem source_chooses_first :
    elaborateAt source catalog source_wellFormed requirement = .resolved (.node firstImpl []) :=
  RoleDictionaries.Examples.first_caller_tree

theorem receiver_chooses_second :
    elaborateAt receiver catalog receiver_wellFormed requirement = .resolved (.node secondImpl []) :=
  RoleDictionaries.Examples.second_caller_tree

theorem jointly_loaded_is_ambiguous :
    elaborateAt jointlyLoaded catalog jointlyLoaded_wellFormed requirement = .ambiguous :=
  RoleDictionaries.Examples.both_callers_ambiguous

def compiledInSource : Compiled RoleDictionaries.Examples.givenGoal.toGoal :=
  compileAt source catalog source_wellFormed requirement separate_callers_resolve.1

theorem source_tree_retained : compiledInSource.plan = .node firstImpl [] :=
  RoleDictionaries.Examples.first_compiled_tree

theorem file_crossing_does_not_reselect :
    useEvidenceAt (Evidence.singleton RoleDictionaries.Examples.givenGoal compiledInSource)
      receiver catalog receiver_wellFormed RoleDictionaries.Examples.givenGoal =
        .resolved (.node firstImpl []) ∧
    elaborateAt receiver catalog receiver_wellFormed requirement = .resolved (.node secondImpl []) := by
  constructor
  · rw [useEvidenceAt_preserves _ _ compiledInSource (Evidence.singleton_lookup _ _), source_tree_retained]
  · exact receiver_chooses_second

theorem file_crossing_retains_evidence_despite_overlap :
    useEvidenceAt (Evidence.singleton RoleDictionaries.Examples.givenGoal compiledInSource)
      jointlyLoaded catalog jointlyLoaded_wellFormed RoleDictionaries.Examples.givenGoal =
        .resolved (.node firstImpl []) ∧
    elaborateAt jointlyLoaded catalog jointlyLoaded_wellFormed requirement = .ambiguous := by
  constructor
  · rw [useEvidenceAt_preserves _ _ compiledInSource (Evidence.singleton_lookup _ _), source_tree_retained]
  · exact jointly_loaded_is_ambiguous

end Examples

end Yulang.ModuleDictionaries
