import Yulang.CommonRoleReachedRoot

/-! Packing two role arguments into one pair preserves the actual declaration
checker. The associated RHS stays int; the old semantic head condition is
therefore satisfied under arbitrary Common substitutions, not only finite
description substitutions. -/

namespace Yulang.CommonRolePackedRegistry

open CommonRoleLinearClock
open CommonRoleReachedRoot

def packGoal (goal : Roles.Goal) : Roles.Goal :=
  ⟨goal.role, [.app 1 goal.args]⟩

def packImpl (implementation : Roles.Impl) : Roles.Impl :=
  ⟨implementation.role, [.app 1 implementation.head], implementation.constraints.map packGoal,
    implementation.key⟩

theorem packGoal_injective {first last : Roles.Goal} (same : packGoal first = packGoal last) :
    first = last := by
  have roles := congrArg Roles.Goal.role same
  change first.role = last.role at roles
  have args := congrArg Roles.Goal.args same
  have equal : first.args = last.args := by simpa [packGoal] using args
  cases first; cases last; simp_all

theorem packImpl_injective {first last : Roles.Impl} (same : packImpl first = packImpl last) :
    first = last := by
  have roles := congrArg Roles.Impl.role same
  change first.role = last.role at roles
  have heads := congrArg Roles.Impl.head same
  have children := congrArg Roles.Impl.constraints same
  have keys := congrArg Roles.Impl.key same
  change first.key = last.key at keys
  have headEqual : first.head = last.head := by simpa [packImpl] using heads
  have childEqual : first.constraints = last.constraints := by
    exact (List.map_inj_right (fun _ _ => packGoal_injective)).mp children
  cases first; cases last; simp_all

theorem packImpl_wellFormed (implementation : Roles.Impl) (wf : implementation.WellFormed) :
    (packImpl implementation).WellFormed := by
  intro child member
  obtain ⟨requirement, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨smaller, occurrences⟩ := wf requirement present
  constructor
  · simpa [packImpl, packGoal, Roles.argsSize, Roles.Term.size] using Nat.add_lt_add_left smaller 1
  · intro name
    simpa [packImpl, packGoal, Roles.argsOccurrences, Roles.Term.occurrences] using occurrences name

def visible (code : CommonRoleComputation.Code) : List Roles.Impl :=
  (CommonRoleLinearEvidence.visible (CommonRoleRegularRegistry.registry code) 0).map packImpl

theorem declarations_wellFormed (code : CommonRoleComputation.Code) : Roles.WellFormed (visible code) := by
  intro implementation member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact packImpl_wellFormed original (CommonRoleRegularRegistry.declarations_wellFormed code original present)

theorem declarations_accepted (code : CommonRoleComputation.Code) :
    CheckedRoles.checkDatabase (visible code) = true :=
  (CheckedRoles.checkDatabase_exact _).mpr (declarations_wellFormed code)

def environment (code : CommonRoleComputation.Code) : Roles.AssocEnv where
  impls := (visible code).map CommonRoleRegularRegistry.annotate
  coherent := by
    intro first firstMember last lastMember _
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp lastMember
    rfl

theorem environment_cores (code : CommonRoleComputation.Code) :
    (environment code).cores = visible code := by
  simp [environment, Roles.AssocEnv.cores, List.map_map, Function.comp_def,
    CommonRoleRegularRegistry.annotate]

theorem environment_checked (code : CommonRoleComputation.Code) :
    CommonRoleRegularResolutionObstruction.checkEnvironment (environment code) = true := by
  apply List.all_eq_true.mpr
  intro annotated member
  obtain ⟨implementation, present, rfl⟩ := List.mem_map.mp member
  have checked := (CheckedRoles.checkImpl_exact implementation).mpr (declarations_wellFormed code _ present)
  simpa [CommonRoleRegularRegistry.annotate, CommonRoleRegularResolutionObstruction.checkAssociated] using checked

theorem head_determines_associated (code : CommonRoleComputation.Code) :
    CommonRoleRegularResolutionObstruction.HeadDeterminesAssociated (environment code) :=
  (CommonRoleRegularResolutionObstruction.checkEnvironment_sound _ (environment_checked code)).2

def requiredRole : Roles.RoleDecl := ⟨1, fun name => if name = 0 then some none else none,
  by intro name rhs member; split at member <;> cases member⟩

def roles : Roles.RoleDecls := fun name =>
  if name < 5 then requiredRole else CommonRoleRegularRegistry.undeclaredRole

theorem constraints_declared (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ visible code) (child : Roles.Goal)
    (required : child ∈ implementation.constraints) :
    child.role < 5 ∧ child.args.length = (roles child.role).arity := by
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨requirement, present, rfl⟩ := List.mem_map.mp required
  have declared := CommonRoleRegularRegistry.constraints_declared code originalMember present
  exact ⟨declared.1, by simp [packGoal, roles, declared.1, requiredRole]⟩

theorem associated_wellFormed (code : CommonRoleComputation.Code) :
    Roles.AssocWellFormed (environment code) roles := by
  intro annotated member
  obtain ⟨packed, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨implementation, original, rfl⟩ := List.mem_map.mp present
  have shape := CommonRoleRegularRegistry.visible_shape code original
  have signature : roles implementation.role = requiredRole := by simp [roles, shape.1]
  constructor
  · intro name rhs body varName occurs
    have pair : (name, rhs) = (0, Pattern.int.encode) := by
      simpa [CommonRoleRegularRegistry.annotate] using body
    cases pair
    simp [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] at occurs
  · constructor
    · constructor
      · change 1 = (roles implementation.role).arity
        rw [signature]; rfl
      · intro name default declared
        change (roles implementation.role).assoc name = some default at declared
        rw [signature] at declared
        by_cases same : name = 0
        · subst name
          exact Or.inl ⟨Pattern.int.encode, rfl⟩
        · simp [requiredRole, same] at declared
    · intro name rhs body
      have pair : (name, rhs) = (0, Pattern.int.encode) := by
        simpa [CommonRoleRegularRegistry.annotate] using body
      cases pair
      exact ⟨none, by change (roles implementation.role).assoc 0 = _; rw [signature]; rfl⟩

def pairGoal (role : Nat) (first last : Description) : CommonRoleReachedRoot.Goal :=
  ⟨role, .pair first last⟩

def semanticGoal (role : Nat) (first last : Description) : SemanticGoal :=
  ⟨role, first.eval, last.eval⟩

def assignmentEval (assignment : Nat → Description) : Nat → Common.Ty :=
  fun name => (assignment name).eval

@[simp] theorem packed_head (key : Nat) (rule : Rule) (assignment : Nat → Description) :
    CommonRoleReachedRoot.interpretGoal
      ⟨(packImpl (compile key rule)).role, (packImpl (compile key rule)).head⟩ assignment =
    some (pairGoal rule.source (instantiate (wrapPattern rule.padding (.var rule.fresh)) assignment)
      (instantiate rule.left assignment)) := by
  change CommonRoleReachedRoot.interpretGoal
    ⟨rule.source, [(Pattern.pair (wrapPattern rule.padding (.var rule.fresh)) rule.left).encode]⟩ _ = _
  simp [CommonRoleReachedRoot.interpretGoal, instantiate, pairGoal]

@[simp] theorem packed_child (rule : Rule) (assignment : Nat → Description) :
    CommonRoleReachedRoot.interpretGoal
      (packGoal ⟨rule.target, [.var rule.fresh, rule.right.encode]⟩) assignment =
    some (pairGoal rule.target (assignment rule.fresh) (instantiate rule.right assignment)) := by
  change CommonRoleReachedRoot.interpretGoal
    ⟨rule.target, [(Pattern.pair (.var rule.fresh) rule.right).encode]⟩ _ = _
  simp [CommonRoleReachedRoot.interpretGoal, instantiate, pairGoal]

@[simp] theorem matches_compile (key : Nat) (rule : Rule) (role : Nat)
    (first last : Description) (assignment : Nat → Description) :
    CommonRoleReachedRoot.Matches (packImpl (compile key rule)) (pairGoal role first last) assignment ↔
    HeadMatches rule (semanticGoal role first last) (assignmentEval assignment) := by
  simp only [CommonRoleReachedRoot.Matches, packed_head, Option.some.injEq, exists_eq_left',
    CommonRoleReachedRoot.Equivalent,
    pairGoal, Description.eval, CommonRoleReachedRoot.instantiate_eval,
    CommonCanonicalShapes.pair_equivalent_iff, HeadMatches, GoalEquivalent,
    headGoal, semanticGoal]
  rfl

@[simp] theorem terminal_head (key terminal : Nat) (assignment : Nat → Description) :
    CommonRoleReachedRoot.interpretGoal
      ⟨(packImpl (terminalImpl key terminal)).role, (packImpl (terminalImpl key terminal)).head⟩ assignment =
    some (pairGoal terminal (assignment 0) (assignment 1)) := by
  change CommonRoleReachedRoot.interpretGoal
    ⟨terminal, [(Pattern.pair (.var 0) (.var 1)).encode]⟩ _ = _
  simp [CommonRoleReachedRoot.interpretGoal, instantiate, pairGoal]

theorem matches_to_actual (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ CommonRoleLinearEvidence.visible (CommonRoleRegularRegistry.registry code) 0)
    (role : Nat) (first last : Description) (assignment : Nat → Description)
    (matched : CommonRoleReachedRoot.Matches (packImpl implementation) (pairGoal role first last) assignment) :
    CommonRoleActualEvidence.Matches implementation (semanticGoal role first last) (assignmentEval assignment) := by
  rcases List.mem_cons.mp member with rfl | member
  · obtain ⟨head, interpreted, same⟩ := matched
    have equal := Option.some.inj ((terminal_head 0 0 assignment).symm.trans interpreted)
    subst head
    refine ⟨⟨0, (assignment 0).eval, (assignment 1).eval⟩, rfl, same.1, ?_⟩
    exact (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp same.2
  · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    exact (CommonRoleActualEvidence.matches_compile _ _ _ _).mpr
      ((matches_compile _ _ _ _ _ _).mp matched)

theorem unique_of_actual (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (role : Nat) (first last : Description)
    (unique : CommonRoleActualEvidence.Unique
      (CommonRoleLinearEvidence.visible (CommonRoleRegularRegistry.registry code) 0)
      implementation (semanticGoal role first last)) :
    CommonRoleReachedRoot.Unique (visible code) (packImpl implementation) (pairGoal role first last) := by
  intro other member matched
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨assignment, matched⟩ := matched
  exact congrArg packImpl (unique original present
    ⟨assignmentEval assignment, matches_to_actual code original present role first last assignment matched⟩)

end Yulang.CommonRolePackedRegistry
