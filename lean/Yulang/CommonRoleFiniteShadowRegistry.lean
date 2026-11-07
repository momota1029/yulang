import Yulang.CommonRoleInspectedSemantics

/-!
# Raw Paterson size can be padded by semantically erased finite fields

Each actual head is {x:left,x:G^k int}; its actual where child is {x:right}.
The second x disappears in Common, but the existing declaration checker
counts it. All used variables occur in the visible data pattern.
-/

namespace Yulang.CommonRoleFiniteShadowRegistry

open CommonRoleLinearClock (Rule Linear Ground)
open CommonRoleInspectedSemantics
open CommonRoleRegularRegistry (registry)

def required (pattern : Pattern) : Pattern := .record pattern .empty

def headPattern (rule : Rule) : Pattern :=
  .record (liftPattern rule.left)
    (.record (liftPattern (CommonRoleLinearClock.wrapPattern rule.padding .int)) .empty)

def childPattern (rule : Rule) : Pattern := required (liftPattern rule.right)

def compile (key : Nat) (rule : Rule) : Roles.Impl :=
  ⟨rule.source, [(headPattern rule).encode], [⟨rule.target, [(childPattern rule).encode]⟩], key⟩

def terminalImpl : Roles.Impl := ⟨0, [(required (.var 0)).encode], [], 0⟩

theorem lift_size (pattern : CommonRoleLinearClock.Pattern) :
    (liftPattern pattern).encode.size = pattern.encode.size := by
  induction pattern <;> simp_all [liftPattern, Pattern.encode, CommonRoleLinearClock.Pattern.encode,
    Roles.Term.size, Roles.argsSize]

theorem lift_occurrences (pattern : CommonRoleLinearClock.Pattern) (name : Nat) :
    (liftPattern pattern).encode.occurrences name = pattern.encode.occurrences name := by
  induction pattern <;> simp_all [liftPattern, Pattern.encode, CommonRoleLinearClock.Pattern.encode,
    Roles.Term.occurrences, Roles.argsOccurrences]

theorem compile_wellFormed (key : Nat) (rule : Rule) (linear : Linear rule) :
    (compile key rule).WellFormed := by
  intro child member
  have same : child = ⟨rule.target, [(childPattern rule).encode]⟩ := by simpa [compile] using member
  subst child
  constructor
  · simp only [compile, childPattern, required, headPattern, Pattern.encode, Roles.Term.size,
      Roles.argsSize, lift_size, CommonRoleLinearClock.wrapPattern_size,
      CommonRoleLinearClock.Pattern.encode, CommonRoleLinearClock.Rule.padding]
    omega
  · intro name
    have counts := linear name
    simpa [compile, childPattern, required, headPattern, Pattern.encode, Roles.Term.occurrences,
      Roles.argsOccurrences, lift_occurrences, CommonRoleLinearClock.wrapPattern_occurrences,
      CommonRoleLinearClock.Pattern.encode] using counts

theorem compile_accepted (key : Nat) (rule : Rule) (linear : Linear rule) :
    CheckedRoles.checkImpl (compile key rule) = true :=
  (CheckedRoles.checkImpl_exact _).mpr (compile_wellFormed key rule linear)

def visible (code : CommonRoleComputation.Code) : List Roles.Impl :=
  terminalImpl :: (registry code).map (fun entry => compile (entry.1 + 1) entry.2)

theorem declarations_wellFormed (code : CommonRoleComputation.Code) : Roles.WellFormed (visible code) := by
  intro implementation member
  rcases List.mem_cons.mp member with rfl | member
  · intro child impossible
    cases impossible
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    exact compile_wellFormed _ _ (CommonRoleRegularRegistry.registry_linear code entry present)

theorem declarations_accepted (code : CommonRoleComputation.Code) :
    CheckedRoles.checkDatabase (visible code) = true :=
  (CheckedRoles.checkDatabase_exact _).mpr (declarations_wellFormed code)

def annotate (implementation : Roles.Impl) : Roles.AssocImpl :=
  ⟨implementation, [(0, Pattern.int.encode)], by decide⟩

def environment (code : CommonRoleComputation.Code) : Roles.AssocEnv where
  impls := (visible code).map annotate
  coherent := by
    intro first firstMember last lastMember _
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp lastMember
    rfl

theorem environment_cores (code : CommonRoleComputation.Code) : (environment code).cores = visible code := by
  simp [environment, Roles.AssocEnv.cores, List.map_map, Function.comp_def, annotate]

/-- Exactly the existing checker, not a normalization or stronger size gate. -/
theorem environment_checked (code : CommonRoleComputation.Code) :
    CommonRoleRegularResolutionObstruction.checkEnvironment (environment code) = true := by
  apply List.all_eq_true.mpr
  intro implementation member
  obtain ⟨core, present, rfl⟩ := List.mem_map.mp member
  have checked := (CheckedRoles.checkImpl_exact core).mpr (declarations_wellFormed code core present)
  simpa [CommonRoleRegularResolutionObstruction.checkAssociated, annotate,
    Pattern.encode, CommonRoleLinearClock.Pattern.encode] using checked

/-- The same approved semantic property, now using the extended fixed
int/pair/variant/record interpretation, including non-vacuous record heads. -/
def HeadDeterminesAssociated (declarations : Roles.AssocEnv) : Prop :=
  ∀ implementation ∈ declarations.impls, ∀ σ τ : Nat → Common.Ty,
    (∀ term ∈ implementation.impl.head, ∃ first last,
      interpretTerm term σ = some first ∧ interpretTerm term τ = some last ∧ Common.Equivalent first last) →
    ∀ name rhs, (name, rhs) ∈ implementation.assoc → ∃ first last,
      interpretTerm rhs σ = some first ∧ interpretTerm rhs τ = some last ∧ Common.Equivalent first last

theorem head_determines_associated (code : CommonRoleComputation.Code) :
    HeadDeterminesAssociated (environment code) := by
  intro implementation member σ τ _ name rhs body
  obtain ⟨core, _, rfl⟩ := List.mem_map.mp member
  have same : (name, rhs) = (0, Pattern.int.encode) := by simpa [annotate] using body
  cases same
  exact ⟨.base .int, .base .int, rfl, rfl, Common.equivalent_refl _⟩

abbrev roles := CommonRolePackedRegistry.roles

theorem visible_declared (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ visible code) : implementation.role < 5 ∧ implementation.head.length = 1 := by
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨by decide, rfl⟩
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    exact ⟨CommonRoleRegularRegistry.rule_source_bound code
      ((CommonRoleRegularRegistry.mem_registry code entry).mp present).1, rfl⟩

theorem constraints_declared (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ visible code) (child : Roles.Goal) (required : child ∈ implementation.constraints) :
    child.role < 5 ∧ child.args.length = (roles child.role).arity := by
  rcases List.mem_cons.mp member with rfl | member
  · cases required
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    have same : child = ⟨entry.2.target, [(childPattern entry.2).encode]⟩ := by simpa [compile] using required
    subst child
    have bound := CommonRoleRegularRegistry.rule_target_bound code
      ((CommonRoleRegularRegistry.mem_registry code entry).mp present).1
    exact ⟨bound, by simp [roles, CommonRolePackedRegistry.roles, bound, CommonRolePackedRegistry.requiredRole]⟩

theorem associated_wellFormed (code : CommonRoleComputation.Code) :
    Roles.AssocWellFormed (environment code) roles := by
  intro annotated member
  obtain ⟨implementation, present, rfl⟩ := List.mem_map.mp member
  have shape := visible_declared code implementation present
  have signature : roles implementation.role = CommonRolePackedRegistry.requiredRole := by
    simp [roles, CommonRolePackedRegistry.roles, shape.1]
  constructor
  · intro name rhs body variableName occurs
    have same : (name, rhs) = (0, Pattern.int.encode) := by simpa [annotate] using body
    cases same
    simp [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] at occurs
  · constructor
    · constructor
      · simpa [annotate, signature, CommonRolePackedRegistry.requiredRole] using shape.2
      · intro name default declared
        change (roles implementation.role).assoc name = some default at declared
        rw [signature] at declared
        by_cases same : name = 0
        · subst name
          exact Or.inl ⟨Pattern.int.encode, rfl⟩
        · simp [CommonRolePackedRegistry.requiredRole, same] at declared
    · intro name rhs body
      have same : (name, rhs) = (0, Pattern.int.encode) := by simpa [annotate] using body
      cases same
      exact ⟨none, by change (roles implementation.role).assoc 0 = _; rw [signature]; rfl⟩

def dataGoal (role : Nat) (value : Description) : Goal := ⟨role, .record value .empty⟩

theorem head_equivalent (rule : Rule) (assignment : Nat → Common.Ty) :
    Common.Equivalent ((headPattern rule).eval assignment) (Common.required 0 (rule.left.eval assignment)) := by
  simpa [headPattern, Pattern.eval, lift_eval, Common.required] using
    Common.common_shadowed_head_equivalent 0 (rule.left.eval assignment)
      ((CommonRoleLinearClock.wrapPattern rule.padding .int).eval assignment) Common.emptyRecord

theorem matches_compile (key : Nat) (rule : Rule) (role : Nat) (value : Description)
    (assignment : Nat → Common.Ty) :
    Matches (compile key rule) (dataGoal role value) assignment ↔
      rule.source = role ∧ Common.Equivalent (rule.left.eval assignment) value.eval := by
  constructor
  · rintro ⟨sameRole, term, type, head, interpreted, same⟩
    have termEqual : term = (headPattern rule).encode := (List.cons.inj head).1.symm
    subst term
    have typeEqual := Option.some.inj ((interpret_encode (headPattern rule) assignment).symm.trans interpreted)
    subst type
    refine ⟨sameRole, (CommonCanonicalShapes.required_equivalent_iff 0 _ _).mp ?_⟩
    exact Common.equivalent_trans (Common.equivalent_symm (head_equivalent rule assignment)) same
  · rintro ⟨sameRole, same⟩
    exact ⟨sameRole, _, _, rfl, interpret_encode (headPattern rule) assignment,
      Common.equivalent_trans (head_equivalent rule assignment)
        ((CommonCanonicalShapes.required_equivalent_iff 0 _ _).mpr same)⟩

theorem matches_terminal (role : Nat) (value : Description) (assignment : Nat → Common.Ty) :
    Matches terminalImpl (dataGoal role value) assignment ↔
      0 = role ∧ Common.Equivalent (assignment 0) value.eval := by
  constructor
  · rintro ⟨sameRole, term, type, head, interpreted, same⟩
    have termEqual : term = (required (.var 0)).encode := (List.cons.inj head).1.symm
    subst term
    have typeEqual := Option.some.inj ((interpret_encode (required (.var 0)) assignment).symm.trans interpreted)
    subst type
    exact ⟨sameRole, (CommonCanonicalShapes.required_equivalent_iff 0 _ _).mp same⟩
  · rintro ⟨sameRole, same⟩
    exact ⟨sameRole, _, _, rfl, interpret_encode (required (.var 0)) assignment,
      (CommonCanonicalShapes.required_equivalent_iff 0 _ _).mpr same⟩

@[simp] theorem child_interpreted (rule : Rule) (assignment : Nat → Description) :
    interpretGoal ⟨rule.target, [(childPattern rule).encode]⟩ assignment =
      some (dataGoal rule.target (instantiate (liftPattern rule.right) assignment)) := by
  simp [interpretGoal, childPattern, required, instantiate, dataGoal]

end Yulang.CommonRoleFiniteShadowRegistry
