import Yulang.CommonRolePackedHalting

/-!
# Arbitrary Common substitutions cannot add spurious packed successes

This deliberately larger independent judgment omits both root rejection and
candidate uniqueness, and permits arbitrary Common types/rows as substitution
images. It still reads the actual unary packed declaration fields. On the
counterfamily its existence is exactly halting, just as the smaller guarded
finite-description dictionary judgment is. Thus the obstruction does not
depend on excluding nonregular or nonrepresentable matching substitutions.
-/

namespace Yulang.CommonRolePackedSemanticReflection

open CommonRoleLinearClock
open CommonRolePackedRegistry (packImpl packGoal visible)

structure Goal where
  role : Nat
  argument : Common.Ty

def pairGoal (goal : SemanticGoal) : Goal :=
  ⟨goal.role, Common.pair goal.clock goal.value⟩

def interpretGoal (requirement : Roles.Goal) (assignment : Nat → Common.Ty) : Option Goal := do
  let [argument] := requirement.args | none
  return ⟨requirement.role, ← CommonRoleActualEvidence.interpretTerm argument assignment⟩

def Equivalent (first last : Goal) : Prop :=
  first.role = last.role ∧ Common.Equivalent first.argument last.argument

def Matches (implementation : Roles.Impl) (goal : Goal) (assignment : Nat → Common.Ty) : Prop :=
  ∃ head, interpretGoal ⟨implementation.role, implementation.head⟩ assignment = some head ∧
    Equivalent head goal

mutual
  inductive Derives (visible : List Roles.Impl) : Goal → Prop where
    | impl {goal} (implementation : Roles.Impl) (assignment : Nat → Common.Ty)
        (member : implementation ∈ visible) (matched : Matches implementation goal assignment)
        (children : Children visible assignment implementation.constraints) : Derives visible goal

  inductive Children (visible : List Roles.Impl) : (Nat → Common.Ty) → List Roles.Goal → Prop where
    | nil {assignment} : Children visible assignment []
    | cons {assignment} (requirement : Roles.Goal) (child : Goal) (rest : List Roles.Goal)
        (interpreted : interpretGoal requirement assignment = some child)
        (derivation : Derives visible child) (children : Children visible assignment rest) :
        Children visible assignment (requirement :: rest)
end

@[simp] theorem packed_head (key : Nat) (rule : Rule) (assignment : Nat → Common.Ty) :
    interpretGoal ⟨(packImpl (compile key rule)).role, (packImpl (compile key rule)).head⟩ assignment =
      some (pairGoal (headGoal rule assignment)) := by
  change interpretGoal
    ⟨rule.source, [(Pattern.pair (wrapPattern rule.padding (.var rule.fresh)) rule.left).encode]⟩ _ = _
  simp [interpretGoal, pairGoal, headGoal, Pattern.eval]

@[simp] theorem packed_child (rule : Rule) (assignment : Nat → Common.Ty) :
    interpretGoal (packGoal ⟨rule.target, [.var rule.fresh, rule.right.encode]⟩) assignment =
      some (pairGoal (childGoal rule assignment)) := by
  change interpretGoal ⟨rule.target, [(Pattern.pair (.var rule.fresh) rule.right).encode]⟩ _ = _
  simp [interpretGoal, pairGoal, childGoal, Pattern.eval]

@[simp] theorem terminal_head (key terminal : Nat) (assignment : Nat → Common.Ty) :
    interpretGoal ⟨(packImpl (terminalImpl key terminal)).role,
      (packImpl (terminalImpl key terminal)).head⟩ assignment =
      some (pairGoal ⟨terminal, assignment 0, assignment 1⟩) := by
  change interpretGoal ⟨terminal, [(Pattern.pair (.var 0) (.var 1)).encode]⟩ _ = _
  simp [interpretGoal, pairGoal, Pattern.eval]

@[simp] theorem matches_compile (key : Nat) (rule : Rule) (goal : SemanticGoal)
    (assignment : Nat → Common.Ty) :
    Matches (packImpl (compile key rule)) (pairGoal goal) assignment ↔ HeadMatches rule goal assignment := by
  simp [Matches, Equivalent, pairGoal, CommonCanonicalShapes.pair_equivalent_iff, HeadMatches, GoalEquivalent]

theorem matches_to_actual (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ CommonRoleLinearEvidence.visible (CommonRoleRegularRegistry.registry code) 0)
    (goal : SemanticGoal) (assignment : Nat → Common.Ty)
    (matched : Matches (packImpl implementation) (pairGoal goal) assignment) :
    CommonRoleActualEvidence.Matches implementation goal assignment := by
  rcases List.mem_cons.mp member with rfl | member
  · obtain ⟨head, interpreted, same⟩ := matched
    have equal := Option.some.inj ((terminal_head 0 0 assignment).symm.trans interpreted)
    subst head
    exact ⟨⟨0, assignment 0, assignment 1⟩, rfl, same.1,
      (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp same.2⟩
  · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    exact (CommonRoleActualEvidence.matches_compile _ _ _ _).mpr
      ((matches_compile _ _ _ _).mp matched)

def Unique (visible : List Roles.Impl) (implementation : Roles.Impl) (goal : Goal) : Prop :=
  ∀ other ∈ visible, (∃ assignment : Nat → Common.Ty, Matches other goal assignment) → other = implementation

theorem arbitrary_unique (code : CommonRoleComputation.Code) (implementation : Roles.Impl) (goal : SemanticGoal)
    (unique : CommonRoleActualEvidence.Unique
      (CommonRoleLinearEvidence.visible (CommonRoleRegularRegistry.registry code) 0) implementation goal) :
    Unique (visible code) (packImpl implementation) (pairGoal goal) := by
  intro other member matched
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨assignment, matched⟩ := matched
  exact congrArg packImpl (unique original originalMember
    ⟨assignment, matches_to_actual code original originalMember goal assignment matched⟩)

theorem unique_at_configuration (code : CommonRoleComputation.Code) (configuration : Configuration)
    (implementation : Roles.Impl) (member : implementation ∈ visible code)
    (matched : ∃ assignment : Nat → Common.Ty, Matches implementation (pairGoal (goalOf configuration)) assignment) :
    Unique (visible code) implementation (pairGoal (goalOf configuration)) := by
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨assignment, matched⟩ := matched
  apply arbitrary_unique
  have noOverlap := CommonRoleLinearEvidence.no_semantic_head_overlap
    (CommonRoleRegularRegistry.registry_linear code)
    (CommonRoleRegularRegistry.no_overlap code configuration) (GoalEquivalent.refl (goalOf configuration))
  rcases List.mem_cons.mp originalMember with rfl | originalMember
  · apply (CommonRoleActualEvidence.unique_terminal _ _ _).mpr
    have actual := matches_to_actual code _ (List.mem_cons_self ..) _ assignment matched
    have finished := (CommonRoleActualEvidence.matches_terminal _ _ _).mp ⟨_, actual⟩
    intro entry entryMember otherAssignment otherMatched
    exact noOverlap (Or.inl ⟨finished, entry, entryMember, otherAssignment, otherMatched⟩)
  · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp originalMember
    have rootMatched := (matches_compile _ _ _ _).mp matched
    apply (CommonRoleActualEvidence.unique_compile _ _ _ _).mpr
    constructor
    · intro finished
      exact noOverlap (Or.inl ⟨finished, entry, entryMember, assignment, rootMatched⟩)
    · intro other otherMember otherMatched
      by_cases equal : other = entry
      · exact equal
      · exact False.elim (noOverlap (Or.inr ⟨other, otherMember, entry, entryMember, equal,
          otherMatched, assignment, rootMatched⟩))

theorem reflect (code : CommonRoleComputation.Code) {goal : Goal}
    (derivation : Derives (visible code) goal) :
    ∀ original, goal = pairGoal original →
      CommonRoleLinearEvidence.Derives (CommonRoleRegularRegistry.registry code) 0 original := by
  induction derivation using Derives.rec (motive_2 := fun assignment requirements _ =>
    ∀ requirement ∈ requirements, ∃ child, interpretGoal requirement assignment = some child ∧
      ∀ original, child = pairGoal original →
        CommonRoleLinearEvidence.Derives (CommonRoleRegularRegistry.registry code) 0 original) with
  | @impl goal implementation assignment member matched children ih =>
      intro original equal
      subst goal
      obtain ⟨unpacked, originalMember, equal⟩ := List.mem_map.mp member
      subst implementation
      rcases List.mem_cons.mp originalMember with rfl | originalMember
      · obtain ⟨head, interpreted, same⟩ := matched
        have equal := Option.some.inj ((terminal_head 0 0 assignment).symm.trans interpreted)
        subst head
        exact .done same.1.symm
      · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp originalMember
        obtain ⟨child, interpreted, reflected⟩ := ih _ (List.mem_singleton_self _)
        have equal := Option.some.inj ((packed_child entry.2 assignment).symm.trans interpreted)
        exact .step entry assignment entryMember ((matches_compile _ _ _ _).mp matched)
          (reflected _ equal.symm)
  | nil => contradiction
  | cons requirement child rest interpreted derivation children ihChild ihRest =>
      rename_i wanted member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨child, interpreted, ihChild⟩
      · exact ihRest wanted member

theorem of_old (code : CommonRoleComputation.Code) {goal : SemanticGoal}
    (derivation : CommonRoleLinearEvidence.Derives (CommonRoleRegularRegistry.registry code) 0 goal) :
    Derives (visible code) (pairGoal goal) := by
  induction derivation with
  | @done goal finished =>
      let assignment : Nat → Common.Ty := fun name => if name = 0 then goal.clock else goal.value
      refine .impl (packImpl (terminalImpl 0 0)) assignment
        (List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩) ?_ .nil
      refine ⟨pairGoal ⟨0, goal.clock, goal.value⟩, ?_, finished.symm, Common.equivalent_refl _⟩
      simp [assignment]
  | step entry assignment member matched child ih =>
      exact .impl (packImpl (compile (entry.1 + 1) entry.2)) assignment
        (List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, member, rfl⟩), rfl⟩)
        ((matches_compile _ _ _ _).mpr matched)
        (.cons _ _ [] (packed_child entry.2 assignment) ih .nil)

theorem arbitrary_common_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Derives (visible code) (pairGoal (CommonRoleRegularHalting.goal code input)) ↔
      CommonRoleComputation.Halts code input := by
  constructor
  · intro derivation
    exact (CommonRoleRegularHalting.derives_exact code input).mp (reflect code derivation _ rfl)
  · intro halting
    exact of_old code ((CommonRoleRegularHalting.derives_exact code input).mpr halting)

theorem guarded_iff_arbitrary_common (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Nonempty (CommonRoleReachedRoot.Dictionary (visible code) (CommonRolePackedHalting.startGoal code input)) ↔
      Derives (visible code) (pairGoal (CommonRoleRegularHalting.goal code input)) :=
  (CommonRolePackedHalting.dictionary_exact code input).trans (arbitrary_common_exact code input).symm

end Yulang.CommonRolePackedSemanticReflection
