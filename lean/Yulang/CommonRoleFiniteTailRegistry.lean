import Yulang.CommonRoleFiniteTailClock

/-! Finite registries fixed by duplicate-field normalization. All raw head and
where record spines have no repeated fields; repetition appears only after
substitution into an unknown tail. -/
namespace Yulang.CommonRoleFiniteTailRegistry
open CommonRoleInspectedSemantics
open CommonRoleFiniteTailClock
open CommonRoleRegularRegistry (registry)

def visible (code : CommonRoleComputation.Code) : List Roles.Impl :=
  terminalImpl :: (registry code).map (fun entry => compile (count code) (entry.1 + 1) entry.2)

theorem declarations_wellFormed (code : CommonRoleComputation.Code) : Roles.WellFormed (visible code) := by
  intro implementation member
  rcases List.mem_cons.mp member with rfl | member
  · intro child impossible
    cases impossible
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    exact compile_wellFormed (count code) _ _
      (member_below_capacity _ entry.2 ((CommonRoleRegularRegistry.mem_registry code entry).mp present).1)
      (CommonRoleRegularRegistry.registry_linear code entry present)

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

theorem environment_checked (code : CommonRoleComputation.Code) :
    CommonRoleNormalizedDeclarations.checkEnvironment (environment code) = true := by
  apply List.all_eq_true.mpr
  intro implementation member
  obtain ⟨core, present, rfl⟩ := List.mem_map.mp member
  have checked : CommonRoleNormalizedDeclarations.checkImpl core = true := by
    rcases List.mem_cons.mp present with rfl | present
    · decide +kernel
    · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp present
      exact compiled_checked (count code) _ _
        (member_below_capacity _ entry.2 ((CommonRoleRegularRegistry.mem_registry code entry).mp entryMember).1)
        (CommonRoleRegularRegistry.registry_linear code entry entryMember)
  simpa [annotate] using checked

theorem head_determines_associated (code : CommonRoleComputation.Code) :
    CommonRoleFiniteShadowRegistry.HeadDeterminesAssociated (environment code) :=
  (CommonRoleNormalizedDeclarations.checkEnvironment_sound _ (environment_checked code)).2

theorem normalized_wellFormed (code : CommonRoleComputation.Code) :
    CommonRoleNormalizedDeclarations.NormalizedWellFormed (environment code).cores :=
  (CommonRoleNormalizedDeclarations.checkEnvironment_sound _ (environment_checked code)).1

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
    have same : child = ⟨entry.2.target, [(childPattern (count code) entry.2).encode]⟩ := by simpa [compile] using required
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


theorem declarations_normal (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ visible code) : CommonRoleNormalizedDeclarations.normalizeImpl implementation = implementation := by
  rcases List.mem_cons.mp member with rfl | member
  · simp [CommonRoleNormalizedDeclarations.normalizeImpl, terminalImpl, Pattern.visible]
  · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    exact compile_normal _ _ _

def pairGoal (role : Nat) (clockType value : Description) : Goal := ⟨role, .pair clockType value⟩

theorem matches_compile (slots key : Nat) (rule : CommonRoleLinearClock.Rule) (role : Nat)
    (clockType value : Description) (assignment : Nat → Common.Ty) :
    Matches (compile slots key rule) (pairGoal role clockType value) assignment ↔
      rule.source = role ∧ Common.Equivalent ((clockHead slots rule.fresh).eval assignment) clockType.eval ∧
        Common.Equivalent (rule.left.eval assignment) value.eval := by
  constructor
  · rintro ⟨sameRole, term, type, head, interpreted, same⟩
    have termEqual : term = (headPattern slots rule).encode := (List.cons.inj head).1.symm
    subst term
    have typeEqual := Option.some.inj ((interpret_encode (headPattern slots rule) assignment).symm.trans interpreted)
    subst type
    have split := (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp same
    exact ⟨sameRole, split.1, by simpa [headPattern, Pattern.eval, lift_eval] using split.2⟩
  · rintro ⟨sameRole, first, last⟩
    refine ⟨sameRole, _, _, rfl, interpret_encode (headPattern slots rule) assignment, ?_⟩
    exact (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr ⟨first, by
      simpa [headPattern, Pattern.eval, lift_eval] using last⟩

theorem matches_terminal (role : Nat) (clockType value : Description) (assignment : Nat → Common.Ty) :
    Matches terminalImpl (pairGoal role clockType value) assignment ↔
      0 = role ∧ Common.Equivalent (assignment 0) clockType.eval ∧ Common.Equivalent (assignment 1) value.eval := by
  constructor
  · rintro ⟨sameRole, term, type, head, interpreted, same⟩
    have termEqual : term = (Pattern.pair (.var 0) (.var 1)).encode := (List.cons.inj head).1.symm
    subst term
    have typeEqual := Option.some.inj
      ((interpret_encode (Pattern.pair (.var 0) (.var 1)) assignment).symm.trans interpreted)
    subst type
    exact ⟨sameRole, (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp same⟩
  · rintro ⟨sameRole, same⟩
    exact ⟨sameRole, _, _, rfl, interpret_encode (Pattern.pair (.var 0) (.var 1)) assignment,
      (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr same⟩

@[simp] theorem child_interpreted (slots : Nat) (rule : CommonRoleLinearClock.Rule) (assignment : Nat → Description) :
    interpretGoal ⟨rule.target, [(childPattern slots rule).encode]⟩ assignment =
      some (pairGoal rule.target (forkDescription slots (assignment rule.fresh))
        (instantiate (liftPattern rule.right) assignment)) := by
  simp [interpretGoal, childPattern, pairGoal, instantiate, clockChild, fork_instantiate]

end Yulang.CommonRoleFiniteTailRegistry
