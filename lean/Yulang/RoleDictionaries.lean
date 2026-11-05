import Yulang.RoleVisibility

/-!
# Executable caller-selected dictionary trees

A successful `Roles.resolve` run constructs the selected impl declaration and
every instantiated `where` child, using the same caller-visible impl set at
every node. The output contains declaration identities, not source method
bodies. Its correctness concerns the existing rigid-goal resolver; source
elaboration, unknown type variables and method execution are separate layers.

The indexed dictionary records the unique matching head and every child goal.
Erasing proof indices yields a finite executable tree. Resolution success is
equivalent to possessing such a tree. Under increased visibility, success
either preserves the whole tree or becomes ambiguous.
-/

namespace Yulang.RoleDictionaries

open Roles

/-- The visible set is fixed at the root and shared by all child dictionaries. -/
inductive Dictionary (visible : List Impl) : Goal → Type where
  | impl {goal : Goal} (implementation : Impl)
      (unique : candidates visible goal = [implementation])
      (children : ∀ constraint, constraint ∈ implementation.constraints →
        Dictionary visible
          (constraint.subst (matchingSubst implementation.head goal.args))) :
      Dictionary visible goal

/-- Runtime-independent dictionary payload: actual selected declarations and
one child for each `where` constraint, in declaration order. -/
inductive Plan where
  | node (implementation : Impl) (children : List Plan)
  deriving Repr

def Plan.declarations : Plan → List Impl
  | .node implementation children =>
      implementation :: children.flatMap Plan.declarations

def Dictionary.erase {visible : List Impl} {goal : Goal}
    (dictionary : Dictionary visible goal) : Plan :=
  match dictionary with
  | .impl implementation _ children =>
      .node implementation (implementation.constraints.attach.map fun constraint =>
        (children constraint.val constraint.property).erase)

@[simp] theorem Dictionary.erase_impl {visible : List Impl} {goal : Goal}
    (implementation : Impl) (unique : candidates visible goal = [implementation])
    (children : ∀ constraint, constraint ∈ implementation.constraints →
      Dictionary visible
        (constraint.subst (matchingSubst implementation.head goal.args))) :
    (Dictionary.impl implementation unique children).erase =
      .node implementation (implementation.constraints.attach.map fun constraint =>
        (children constraint.val constraint.property).erase) := rfl

theorem resolved_child (visible : List Impl) (wellFormed : WellFormed visible)
    (goal : Goal) (implementation : Impl)
    (unique : candidates visible goal = [implementation])
    (success : resolve visible wellFormed goal = .resolved)
    (constraint : Goal) (member : constraint ∈ implementation.constraints) :
    resolve visible wellFormed
      (constraint.subst (matchingSubst implementation.head goal.args)) = .resolved := by
  rw [resolve_one visible wellFormed goal implementation unique] at success
  exact (combine_eq_resolved _).mp success _ (List.mem_map.mpr ⟨constraint, member, rfl⟩)

/-- Total executable extraction from the actual resolver. The recursive calls
are justified by the existing Paterson decrease, without a fuel parameter. -/
def buildResolved (visible : List Impl) (wellFormed : WellFormed visible) (goal : Goal)
    (success : resolve visible wellFormed goal = .resolved) : Dictionary visible goal :=
  match unique : candidates visible goal with
  | [] => False.elim (by
      rw [resolve_none visible wellFormed goal unique] at success
      cases success)
  | [implementation] =>
      have _matching : implementation ∈ visible ∧ Matches implementation goal :=
        mem_candidates.mp (unique ▸ List.mem_singleton_self implementation)
      .impl implementation unique (fun constraint member =>
        buildResolved visible wellFormed
          (constraint.subst (matchingSubst implementation.head goal.args))
          (resolved_child visible wellFormed goal implementation unique success constraint member))
  | first :: second :: rest => False.elim (by
      rw [resolve_many visible wellFormed goal first second rest unique] at success
      cases success)
termination_by argsSize goal.args
decreasing_by
  have decrease := size_decreases (wellFormed implementation _matching.1) member
    (matchingSubst implementation.head goal.args)
  simpa only [Goal.subst, matched_head _matching.2] using decrease

theorem Dictionary.derives {visible : List Impl} {goal : Goal}
    (dictionary : Dictionary visible goal) : Derives visible goal := by
  induction dictionary with
  | @impl goal implementation unique children ih =>
      have matching := mem_candidates.mp (unique ▸ List.mem_singleton_self implementation)
      exact .impl implementation (matchingSubst implementation.head goal.args)
        matching.1 matching.2.1 (matched_head matching.2) ih

theorem Dictionary.resolved {visible : List Impl} (wellFormed : WellFormed visible)
    {goal : Goal} (dictionary : Dictionary visible goal) :
    resolve visible wellFormed goal = .resolved := by
  induction dictionary with
  | impl implementation unique children ih =>
      rw [resolve_one visible wellFormed _ implementation unique, combine_eq_resolved]
      intro result member
      obtain ⟨constraint, constraintMember, rfl⟩ := List.mem_map.mp member
      exact ih constraint constraintMember

theorem Dictionary.resolves {visible : List Impl} (wellFormed : WellFormed visible)
    {goal : Goal} (dictionary : Dictionary visible goal) :
    RoleConstraints.Resolves visible goal :=
  (RoleConstraints.resolve_exact visible wellFormed goal).mp (dictionary.resolved wellFormed)

theorem Dictionary.all_visible {visible : List Impl} {goal : Goal}
    (dictionary : Dictionary visible goal) :
    ∀ implementation ∈ dictionary.erase.declarations, implementation ∈ visible := by
  induction dictionary with
  | impl selected unique children ih =>
      intro implementation member
      simp only [Dictionary.erase_impl, Plan.declarations, List.mem_cons,
        List.mem_flatMap, List.mem_map] at member
      rcases member with same | ⟨child, ⟨constraint, _, childEqual⟩, childMember⟩
      · subst implementation
        exact (mem_candidates.mp (unique ▸ List.mem_singleton_self selected)).1
      · subst child
        exact ih constraint.val constraint.property implementation childMember

/-- If both scopes produce a dictionary, visibility growth preserves all
selected declarations, including every recursively resolved `where` child. -/
theorem Dictionary.erase_mono {smaller larger : List Impl}
    (included : RoleVisibility.Included smaller larger) {goal : Goal}
    (old : Dictionary smaller goal) :
    ∀ new : Dictionary larger goal, old.erase = new.erase := by
  induction old with
  | @impl goal implementation unique children ih =>
      intro new
      cases new with
      | impl other otherUnique otherChildren =>
          have same := RoleVisibility.unique_head_preserved included goal unique otherUnique
          subst other
          simp only [Dictionary.erase_impl]
          congr 1
          apply List.map_congr_left
          intro constraint member
          exact ih constraint.val constraint.property
            (otherChildren constraint.val constraint.property)

theorem Dictionary.erase_unique {visible : List Impl} {goal : Goal}
    (first second : Dictionary visible goal) : first.erase = second.erase :=
  first.erase_mono (fun _ member => member) second

inductive Answer where
  | resolved (plan : Plan)
  | noImpl
  | ambiguous
  deriving Repr

def Answer.status : Answer → Result
  | .resolved _ => .resolved
  | .noImpl => .noImpl
  | .ambiguous => .ambiguous

/-- An executable elaborator for rigid goals. Failure behavior is exactly the
existing resolver's behavior, and success carries its complete dictionary. -/
def elaborate (visible : List Impl) (wellFormed : WellFormed visible) (goal : Goal) : Answer :=
  match result : resolve visible wellFormed goal with
  | .resolved => .resolved (buildResolved visible wellFormed goal result).erase
  | .noImpl => .noImpl
  | .ambiguous => .ambiguous

@[simp] theorem elaborate_status (visible : List Impl) (wellFormed : WellFormed visible)
    (goal : Goal) : (elaborate visible wellFormed goal).status = resolve visible wellFormed goal := by
  unfold elaborate
  split <;> simp_all [Answer.status]

theorem elaborate_success_iff (visible : List Impl) (wellFormed : WellFormed visible)
    (goal : Goal) (plan : Plan) :
    elaborate visible wellFormed goal = .resolved plan ↔
      ∃ dictionary : Dictionary visible goal, dictionary.erase = plan := by
  constructor
  · intro success
    unfold elaborate at success
    split at success
    next result =>
      exact ⟨buildResolved visible wellFormed goal result, Answer.resolved.inj success⟩
    next => cases success
    next => cases success
  · rintro ⟨dictionary, rfl⟩
    have success := dictionary.resolved wellFormed
    unfold elaborate
    split
    next result =>
      exact congrArg Answer.resolved ((buildResolved visible wellFormed goal result).erase_unique dictionary)
    next result => rw [success] at result; cases result
    next result => rw [success] at result; cases result

theorem elaborate_all_visible (visible : List Impl) (wellFormed : WellFormed visible)
    (goal : Goal) (plan : Plan) (success : elaborate visible wellFormed goal = .resolved plan) :
    ∀ implementation ∈ plan.declarations, implementation ∈ visible := by
  obtain ⟨dictionary, rfl⟩ := (elaborate_success_iff visible wellFormed goal plan).mp success
  exact dictionary.all_visible

theorem elaborate_noImpl_iff (visible : List Impl) (wellFormed : WellFormed visible)
    (goal : Goal) :
    elaborate visible wellFormed goal = .noImpl ↔ resolve visible wellFormed goal = .noImpl := by
  unfold elaborate
  split <;> simp_all

theorem elaborate_ambiguous_iff (visible : List Impl) (wellFormed : WellFormed visible)
    (goal : Goal) :
    elaborate visible wellFormed goal = .ambiguous ↔ resolve visible wellFormed goal = .ambiguous := by
  unfold elaborate
  split <;> simp_all

theorem elaborate_mono {smaller larger : List Impl}
    (included : RoleVisibility.Included smaller larger)
    (smallWellFormed : WellFormed smaller) (largeWellFormed : WellFormed larger)
    (goal : Goal) (plan : Plan)
    (success : elaborate smaller smallWellFormed goal = .resolved plan) :
    elaborate larger largeWellFormed goal = .resolved plan ∨
      elaborate larger largeWellFormed goal = .ambiguous := by
  obtain ⟨old, oldPlan⟩ := (elaborate_success_iff smaller smallWellFormed goal plan).mp success
  rcases RoleVisibility.resolved_mono included smallWellFormed largeWellFormed goal
      (old.resolved smallWellFormed) with resolved | ambiguous
  · apply Or.inl
    apply (elaborate_success_iff larger largeWellFormed goal plan).mpr
    let new := buildResolved larger largeWellFormed goal resolved
    exact ⟨new, (old.erase_mono included new).symm.trans oldPlan⟩
  · exact Or.inr ((elaborate_ambiguous_iff larger largeWellFormed goal).mpr ambiguous)

theorem elaborate_congr {left right : List Impl}
    (same : ∀ implementation, implementation ∈ left ↔ implementation ∈ right)
    (leftWellFormed : WellFormed left) (rightWellFormed : WellFormed right) (goal : Goal) :
    elaborate left leftWellFormed goal = elaborate right rightWellFormed goal := by
  have status := RoleVisibility.resolve_congr same leftWellFormed rightWellFormed goal
  cases result : elaborate left leftWellFormed goal with
  | resolved plan =>
      obtain ⟨dictionary, erased⟩ :=
        (elaborate_success_iff left leftWellFormed goal plan).mp result
      have success : resolve right rightWellFormed goal = .resolved :=
        status.symm.trans (dictionary.resolved leftWellFormed)
      let other := buildResolved right rightWellFormed goal success
      apply Eq.symm
      apply (elaborate_success_iff right rightWellFormed goal plan).mpr
      exact ⟨other, (dictionary.erase_mono
        (fun implementation => (same implementation).mp) other).symm.trans erased⟩
  | noImpl =>
      exact ((elaborate_noImpl_iff right rightWellFormed goal).mpr
        (status.symm.trans ((elaborate_noImpl_iff left leftWellFormed goal).mp result))).symm
  | ambiguous =>
      exact ((elaborate_ambiguous_iff right rightWellFormed goal).mpr
        (status.symm.trans ((elaborate_ambiguous_iff left leftWellFormed goal).mp result))).symm

/-- Already compiled evidence retains its originating scope and typed tree.
The receiving scope is deliberately not part of this object's identity. -/
structure Compiled (goal : Goal) where
  origin : List Impl
  wellFormed : WellFormed origin
  dictionary : Dictionary origin goal

def Compiled.plan {goal : Goal} (compiled : Compiled goal) : Plan := compiled.dictionary.erase

def compileResolved (visible : List Impl) (wellFormed : WellFormed visible) (goal : Goal)
    (success : resolve visible wellFormed goal = .resolved) : Compiled goal :=
  ⟨visible, wellFormed, buildResolved visible wellFormed goal success⟩

theorem Compiled.provenance {goal : Goal} (compiled : Compiled goal) :
    elaborate compiled.origin compiled.wellFormed goal = .resolved compiled.plan :=
  (elaborate_success_iff compiled.origin compiled.wellFormed goal compiled.plan).mpr
    ⟨compiled.dictionary, rfl⟩

/-- A supplied dictionary environment. Lookup chooses already compiled values;
the domain equation prevents it from adding unsupplied qualifiers. No policy
for selecting between duplicate source binders is imposed here. -/
structure Evidence (goals : List (RoleConstraints.Predicate Term)) where
  lookup : (goal : RoleConstraints.Predicate Term) → Option (Compiled goal.toGoal)
  domain : ∀ goal, (lookup goal).isSome = true ↔ goal ∈ goals

/-- Concrete adapter for the existing `RoleConstraints.WithEvidence` theory.
Only an absent dictionary invokes impl resolution in the receiving scope. -/
def useEvidence {goals : List (RoleConstraints.Predicate Term)} (evidence : Evidence goals)
    (visible : List Impl) (wellFormed : WellFormed visible)
    (goal : RoleConstraints.Predicate Term) : Answer :=
  match evidence.lookup goal with
  | some compiled => .resolved compiled.plan
  | none => elaborate visible wellFormed goal.toGoal

theorem useEvidence_exact {goals : List (RoleConstraints.Predicate Term)} (evidence : Evidence goals)
    (visible : List Impl) (wellFormed : WellFormed visible)
    (goal : RoleConstraints.Predicate Term) :
    (useEvidence evidence visible wellFormed goal).status = .resolved ↔
      RoleConstraints.WithEvidence
        (fun predicate => RoleConstraints.Resolves visible predicate.toGoal) goals goal := by
  unfold useEvidence
  split
  next compiled found =>
    have member : goal ∈ goals := (evidence.domain goal).mp (by simp [found])
    simp [Answer.status, RoleConstraints.WithEvidence, member]
  next absent =>
    have notMember : goal ∉ goals := by
      intro member
      have present := (evidence.domain goal).mpr member
      simp [absent] at present
    simp only [elaborate_status, RoleConstraints.WithEvidence, notMember, or_false]
    exact RoleConstraints.resolve_exact visible wellFormed goal.toGoal

/-- Passing a dictionary preserves its whole selected tree even if the receiving
scope would choose a different impl, report no impl, or report ambiguity. -/
theorem useEvidence_preserves {goals : List (RoleConstraints.Predicate Term)} (evidence : Evidence goals)
    (goal : RoleConstraints.Predicate Term) (compiled : Compiled goal.toGoal)
    (supplied : evidence.lookup goal = some compiled)
    (receiver : List Impl) (receiverWellFormed : WellFormed receiver) :
    useEvidence evidence receiver receiverWellFormed goal = .resolved compiled.plan := by
  simp [useEvidence, supplied]

def Evidence.singleton (goal : RoleConstraints.Predicate Term) (compiled : Compiled goal.toGoal) :
    Evidence [goal] where
  lookup := fun query => if same : query = goal then some (same ▸ compiled) else none
  domain := by
    intro query
    by_cases same : query = goal <;> simp [same]

@[simp] theorem Evidence.singleton_lookup (goal : RoleConstraints.Predicate Term)
    (compiled : Compiled goal.toGoal) : (Evidence.singleton goal compiled).lookup goal = some compiled := by
  simp [Evidence.singleton]

namespace Examples

open RoleVisibility.Examples

def firstDictionary : Dictionary [firstImpl] requirement :=
  .impl firstImpl (by decide) (fun _ member => False.elim (by simp [firstImpl] at member))

def secondDictionary : Dictionary [secondImpl] requirement :=
  .impl secondImpl (by decide) (fun _ member => False.elim (by simp [secondImpl] at member))

theorem first_caller_tree :
    elaborate [firstImpl] first_wellFormed requirement = .resolved (.node firstImpl []) :=
  (elaborate_success_iff _ _ _ _).mpr ⟨firstDictionary, rfl⟩

theorem second_caller_tree :
    elaborate [secondImpl] second_wellFormed requirement = .resolved (.node secondImpl []) :=
  (elaborate_success_iff _ _ _ _).mpr ⟨secondDictionary, rfl⟩

theorem caller_trees_differ :
    elaborate [firstImpl] first_wellFormed requirement ≠
      elaborate [secondImpl] second_wellFormed requirement := by
  rw [first_caller_tree, second_caller_tree]
  intro equal
  have implEqual := Plan.node.inj (Answer.resolved.inj equal)
  have keyEqual := congrArg Impl.key implEqual.1
  contradiction

theorem both_callers_ambiguous :
    elaborate [firstImpl, secondImpl] both_wellFormed requirement = .ambiguous :=
  (elaborate_ambiguous_iff _ _ _).mpr jointly_visible_is_ambiguous

def givenGoal : RoleConstraints.Predicate Term := ⟨requirement.role, requirement.args⟩
def firstCompiled : Compiled givenGoal.toGoal :=
  compileResolved [firstImpl] first_wellFormed requirement separate_callers_resolve.1

theorem first_compiled_tree : firstCompiled.plan = .node firstImpl [] := by
  have equal := firstCompiled.provenance
  change elaborate [firstImpl] first_wellFormed requirement = .resolved firstCompiled.plan at equal
  have root := first_caller_tree
  have same := equal.symm.trans root
  exact Answer.resolved.inj same

/-- The receiving caller can see a distinct impl, but supplied evidence retains
the declaration selected before the value crossed the file boundary. -/
theorem receiving_scope_does_not_reselect :
    useEvidence (Evidence.singleton givenGoal firstCompiled)
      [secondImpl] second_wellFormed givenGoal = .resolved (.node firstImpl []) ∧
    elaborate [secondImpl] second_wellFormed requirement = .resolved (.node secondImpl []) := by
  constructor
  · rw [useEvidence_preserves _ givenGoal firstCompiled (Evidence.singleton_lookup _ _), first_compiled_tree]
  · exact second_caller_tree

theorem passed_evidence_survives_joint_visibility :
    useEvidence (Evidence.singleton givenGoal firstCompiled)
      [firstImpl, secondImpl] both_wellFormed givenGoal = .resolved (.node firstImpl []) ∧
    elaborate [firstImpl, secondImpl] both_wellFormed requirement = .ambiguous := by
  constructor
  · rw [useEvidence_preserves _ givenGoal firstCompiled (Evidence.singleton_lookup _ _), first_compiled_tree]
  · exact both_callers_ambiguous

open Roles.Examples in
def nestedDictionary : Dictionary goodImpls (display (list (list int))) :=
  .impl listImpl (by decide) (fun constraint member => by
    have same : constraint = display (.var 0) := by simpa [listImpl] using member
    subst constraint
    change Dictionary goodImpls (display (list int))
    exact .impl listImpl (by decide) (fun constraint member => by
      have same : constraint = display (.var 0) := by simpa [listImpl] using member
      subst constraint
      change Dictionary goodImpls (display int)
      exact .impl intImpl (by decide)
        (fun _ member => False.elim (by simp [intImpl] at member))))

open Roles.Examples in
theorem all_nested_children_use_caller_scope :
    elaborate goodImpls goodImpls_wellFormed (display (list (list int))) =
      .resolved (.node listImpl [.node listImpl [.node intImpl []]]) :=
  (elaborate_success_iff _ _ _ _).mpr ⟨nestedDictionary, rfl⟩

open Roles.Examples in
theorem definition_wellFormed : WellFormed [listImpl] := by
  simp [WellFormed, listImpl_wellFormed]

open Roles.Examples in
theorem definition_scope_alone_is_insufficient :
    elaborate [listImpl] definition_wellFormed (display (list int)) = .noImpl := by
  apply (elaborate_noImpl_iff _ _ _).mpr
  rw [resolve_one _ _ _ listImpl (by decide)]
  change combine [resolve [listImpl] _ (display int)] = .noImpl
  rw [combine_single, resolve_none _ _ _ (by decide)]

end Examples

end Yulang.RoleDictionaries
