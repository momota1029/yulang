import Yulang.CommonRoleMergedPayload

/-! Actual finite declarations after tag merging. N removes hidden record
fields; there are no records or tails in this family. Canonical payload
matching and tag uniqueness do not contract the stored syntax measured by
Paterson. No extra declaration hypothesis is used at the final boundary. -/
namespace Yulang.CommonRoleMergedRegistry

open CommonRoleLinearClock (Pattern Rule Linear Ground)
open CommonRoleMergedPayload
open CommonRoleRegularRegistry (registry)

def compile (key : Nat) (rule : Rule) : Roles.Impl :=
  ⟨rule.source, [headTerm rule.padding rule.left], [⟨rule.target, [plainTerm rule.right]⟩], key⟩

def terminalImpl : Roles.Impl := ⟨0, [plainTerm (.var 0)], [], 0⟩

theorem normalize_head (copies : Nat) (pattern : Pattern) :
    CommonRoleNormalizedDeclarations.normalizeTerm (headTerm copies pattern) = headTerm copies pattern := by
  cases copies with
  | zero =>
      change CommonRoleNormalizedDeclarations.normalizeTerm
        (CommonRoleInspectedSemantics.Pattern.variant 0 (CommonRoleInspectedSemantics.liftPattern pattern)).encode = _
      rw [CommonRoleNormalizedDeclarations.normalizeTerm_encode]
      simp [CommonRoleInspectedSemantics.Pattern.visible, CommonRoleFiniteTailClock.lift_normal]
      rfl
  | succ copies => rfl

theorem compile_normal (key : Nat) (rule : Rule) :
    CommonRoleNormalizedDeclarations.normalizeImpl (compile key rule) = compile key rule := by
  simp [CommonRoleNormalizedDeclarations.normalizeImpl, CommonRoleNormalizedDeclarations.normalizeGoal,
    compile, normalize_head, plainTerm]

theorem compile_wellFormed (key : Nat) (rule : Rule) (linear : Linear rule) : (compile key rule).WellFormed := by
  intro child member
  have same : child = ⟨rule.target, [plainTerm rule.right]⟩ := by simpa [compile] using member
  subst child
  constructor
  · have positive := rule.left.encode.size_pos
    simp only [compile, plainTerm, headTerm, Roles.argsSize, Roles.Term.size, Nat.add_zero,
      padded_size, data_size, CommonRoleLinearClock.Rule.padding]
    have large := Nat.mul_le_mul_right rule.left.encode.size (show 1 ≤ rule.right.encode.size + 1 + 1 by omega)
    omega
  · intro name
    have counts := linear name
    have inflated := Nat.mul_le_mul_right (rule.left.encode.occurrences name)
      (show 1 ≤ rule.padding + 1 by omega)
    simp only [compile, plainTerm, headTerm, Roles.argsOccurrences, Roles.Term.occurrences,
      padded_occurrences, data_occurrences, Nat.add_zero]
    omega

def checkImpl (implementation : Roles.Impl) : Bool :=
  (decodeHead implementation.head).isSome &&
    implementation.constraints.all (fun child => (decodeHead child.args).isSome) &&
    CheckedRoles.checkImpl (CommonRoleNormalizedDeclarations.normalizeImpl implementation)

theorem checkImpl_sound (implementation : Roles.Impl) (accepted : checkImpl implementation = true) :
    (CommonRoleNormalizedDeclarations.normalizeImpl implementation).WellFormed :=
  (CheckedRoles.checkImpl_exact _).mp (Bool.and_eq_true_iff.mp accepted).2

theorem compile_checked (key : Nat) (rule : Rule) (linear : Linear rule) : checkImpl (compile key rule) = true := by
  have checked := (CheckedRoles.checkImpl_exact _).mpr (compile_wellFormed key rule linear)
  unfold checkImpl
  rw [compile_normal]
  simpa [compile, plainTerm] using checked

def visible (code : CommonRoleComputation.Code) : List Roles.Impl :=
  terminalImpl :: (registry code).map (fun entry => compile (entry.1 + 1) entry.2)

/-- The actual singleton tag row is stored as an actual unary variant head. -/
def headFromRow (row : Variants.Merged.Row Nat Roles.Term) : Option (List Roles.Term) :=
  match row.entries with
  | [(0, payload)] => some [.app 3 [payload]]
  | _ => none

theorem merged_head (copies : Nat) (pattern : Pattern) :
    headFromRow (mergedRow copies pattern) = some [headTerm copies pattern] := by
  simp [headFromRow, merged_entries, headTerm]

theorem all_heads_from_merge (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ visible code) :
    ∃ copies pattern, headFromRow (mergedRow copies pattern) = some implementation.head := by
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨0, .var 0, merged_head _ _⟩
  · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    exact ⟨entry.2.padding, entry.2.left, merged_head _ _⟩

theorem declarations_wellFormed (code : CommonRoleComputation.Code) : Roles.WellFormed (visible code) := by
  intro implementation member
  rcases List.mem_cons.mp member with rfl | member
  · intro child impossible; cases impossible
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    exact compile_wellFormed _ _ (CommonRoleRegularRegistry.registry_linear code entry present)

theorem declarations_normal (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ visible code) :
    CommonRoleNormalizedDeclarations.normalizeImpl implementation = implementation := by
  rcases List.mem_cons.mp member with rfl | member
  · simp [CommonRoleNormalizedDeclarations.normalizeImpl, terminalImpl, plainTerm, normalize_head]
  · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    exact compile_normal _ _

def annotate (implementation : Roles.Impl) : Roles.AssocImpl := ⟨implementation, [(0, dataTerm .int)], by decide⟩

def environment (code : CommonRoleComputation.Code) : Roles.AssocEnv where
  impls := (visible code).map annotate
  coherent := by
    intro first firstMember last lastMember _
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp lastMember
    rfl

theorem environment_cores (code : CommonRoleComputation.Code) : (environment code).cores = visible code := by
  simp [environment, Roles.AssocEnv.cores, List.map_map, Function.comp_def, annotate]

def HeadDeterminesAssociated (declarations : Roles.AssocEnv) : Prop :=
  ∀ implementation ∈ declarations.impls, ∀ σ τ : Nat → Common.Ty,
    (∀ term ∈ implementation.impl.head, ∃ first last,
      interpret term σ = some first ∧ interpret term τ = some last ∧ Common.Equivalent first last) →
    ∀ name rhs, (name, rhs) ∈ implementation.assoc → ∃ first last,
      interpret rhs σ = some first ∧ interpret rhs τ = some last ∧ Common.Equivalent first last

def checkEnvironment (declarations : Roles.AssocEnv) : Bool :=
  declarations.impls.all (fun implementation => checkImpl implementation.impl &&
    implementation.assoc.all (fun body => decide (body.2 = dataTerm .int)))

theorem checkEnvironment_sound (declarations : Roles.AssocEnv) (accepted : checkEnvironment declarations = true) :
    CommonRoleNormalizedDeclarations.NormalizedWellFormed declarations.cores ∧ HeadDeterminesAssociated declarations := by
  have each := List.all_eq_true.mp accepted
  constructor
  · intro implementation member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨annotated, annotatedMember, rfl⟩ := List.mem_map.mp present
    exact checkImpl_sound _ (Bool.and_eq_true_iff.mp (each annotated annotatedMember)).1
  · intro implementation member σ τ _ name rhs body
    have same : rhs = dataTerm .int := of_decide_eq_true
      ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp (each implementation member)).2) (name, rhs) body)
    subst rhs
    exact ⟨.base .int, .base .int, rfl, rfl, Common.equivalent_refl _⟩

theorem environment_checked (code : CommonRoleComputation.Code) : checkEnvironment (environment code) = true := by
  apply List.all_eq_true.mpr
  intro implementation member
  obtain ⟨core, present, rfl⟩ := List.mem_map.mp member
  have checked : checkImpl core = true := by
    rcases List.mem_cons.mp present with rfl | present
    · decide +kernel
    · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp present
      exact compile_checked _ _ (CommonRoleRegularRegistry.registry_linear code entry entryMember)
  simpa [annotate] using checked

abbrev roles := CommonRolePackedRegistry.roles

theorem visible_declared (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ visible code) : implementation.role < 5 ∧ implementation.head.length = 1 := by
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨by decide, rfl⟩
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    exact ⟨CommonRoleRegularRegistry.rule_source_bound code ((CommonRoleRegularRegistry.mem_registry code entry).mp present).1, rfl⟩

theorem constraints_declared (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ visible code) (child : Roles.Goal) (required : child ∈ implementation.constraints) :
    child.role < 5 ∧ child.args.length = (roles child.role).arity := by
  rcases List.mem_cons.mp member with rfl | member
  · cases required
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    have same : child = ⟨entry.2.target, [plainTerm entry.2.right]⟩ := by simpa [compile] using required
    subst child
    have bound := CommonRoleRegularRegistry.rule_target_bound code ((CommonRoleRegularRegistry.mem_registry code entry).mp present).1
    exact ⟨bound, by simp [roles, CommonRolePackedRegistry.roles, bound, CommonRolePackedRegistry.requiredRole]⟩

theorem associated_wellFormed (code : CommonRoleComputation.Code) : Roles.AssocWellFormed (environment code) roles := by
  intro annotated member
  obtain ⟨implementation, present, rfl⟩ := List.mem_map.mp member
  have shape := visible_declared code implementation present
  have signature : roles implementation.role = CommonRolePackedRegistry.requiredRole := by
    simp [roles, CommonRolePackedRegistry.roles, shape.1]
  constructor
  · intro name rhs body variableName occurs
    have same : (name, rhs) = (0, dataTerm .int) := by simpa [annotate] using body
    cases same
    simp [dataTerm, CommonRoleInspectedSemantics.liftPattern, CommonRoleInspectedSemantics.Pattern.encode,
      Roles.Term.occurrences, Roles.argsOccurrences] at occurs
  · constructor
    · constructor
      · simpa [annotate, signature, CommonRolePackedRegistry.requiredRole] using shape.2
      · intro name default declared
        change (roles implementation.role).assoc name = some default at declared
        rw [signature] at declared
        by_cases same : name = 0
        · subst name; exact Or.inl ⟨dataTerm .int, rfl⟩
        · simp [CommonRolePackedRegistry.requiredRole, same] at declared
    · intro name rhs body
      have same : (name, rhs) = (0, dataTerm .int) := by simpa [annotate] using body
      cases same
      exact ⟨none, by change (roles implementation.role).assoc 0 = _; rw [signature]; rfl⟩

end Yulang.CommonRoleMergedRegistry
