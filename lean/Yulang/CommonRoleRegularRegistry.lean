import Yulang.CommonRoleLinearProgram
import Yulang.CommonRoleLinearDictionaries
import Yulang.RolesAssoc

/-! Concrete finite, checked, nonoverlapping registries for every finite program.
Repeated subprograms share one declaration and one key. Associated bodies are
the actual constant int, so the approved semantic condition is established at
declaration time and does not restrict resolution success. -/

namespace Yulang.CommonRoleRegularRegistry

open CommonRoleComputation (Code Tree)
open CommonRoleLinearClock
open CommonRoleLinearEvidence
open CommonRoleLinearProgram

def registry (code : Code) : Registry :=
  (Roles.distinct (rules code)).map (fun rule => ((rules code).idxOf rule, rule))

theorem mem_registry (code : Code) (entry : Nat × Rule) :
    entry ∈ registry code ↔ entry.2 ∈ rules code ∧ entry.1 = (rules code).idxOf entry.2 := by
  constructor
  · intro member
    obtain ⟨rule, present, rfl⟩ := List.mem_map.mp member
    exact ⟨(Roles.mem_distinct _ _).mp present, rfl⟩
  · rintro ⟨member, key⟩
    apply List.mem_map.mpr
    exact ⟨entry.2, (Roles.mem_distinct _ _).mpr member, by cases entry; simp_all⟩

theorem registry_linear (code : Code) : LinearRegistry (registry code) := by
  intro entry member
  exact rules_linear code entry.2 ((mem_registry code entry).mp member).1

theorem declarations_accepted (code : Code) :
    CheckedRoles.checkDatabase (visible (registry code) 0) = true :=
  compiled_registry_accepted _ _ (registry_linear code)

theorem declarations_wellFormed (code : Code) : Roles.WellFormed (visible (registry code) 0) :=
  compiled_registry_wellFormed _ _ (registry_linear code)

theorem no_overlap (code : Code) (configuration : Configuration) :
    NoOverlapAt (registry code) 0 configuration := by
  constructor
  · intro finished entry member target transition
    obtain ⟨_, role, _, _, _⟩ := transition
    exact no_terminal_source code ((mem_registry code entry).mp member).1 (role.symm.trans finished)
  · intro first firstMember last lastMember a b firstStep lastStep
    obtain ⟨firstIn, firstKey⟩ := (mem_registry code first).mp firstMember
    obtain ⟨lastIn, lastKey⟩ := (mem_registry code last).mp lastMember
    obtain ⟨σ, firstRole, _, firstHead, _⟩ := firstStep
    obtain ⟨τ, lastRole, _, lastHead, _⟩ := lastStep
    have same := rules_matches_unique code firstIn lastIn σ τ
      (firstRole.symm.trans lastRole) (firstHead.trans lastHead.symm)
    apply Prod.ext
    · rw [firstKey, lastKey, same]
    · exact same

theorem registry_safe (code : Code) (start : Configuration) : SafeFrom (registry code) 0 start :=
  fun configuration _ => no_overlap code configuration

theorem entry_key_unique (code : Code) {first last : Nat × Rule}
    (firstMember : first ∈ registry code) (lastMember : last ∈ registry code)
    (same : first.1 = last.1) : first = last := by
  obtain ⟨firstIn, firstKey⟩ := (mem_registry code first).mp firstMember
  obtain ⟨lastIn, lastKey⟩ := (mem_registry code last).mp lastMember
  have indices : (rules code).idxOf first.2 = (rules code).idxOf last.2 := by
    rw [← firstKey, ← lastKey, same]
  have a := List.getElem_idxOf (List.idxOf_lt_length_of_mem firstIn)
  have b := List.getElem_idxOf (List.idxOf_lt_length_of_mem lastIn)
  apply Prod.ext same
  rw [← a, ← b]
  simp only [indices]

def annotate (implementation : Roles.Impl) : Roles.AssocImpl :=
  ⟨implementation, [(0, Pattern.int.encode)], by decide⟩

def environment (code : Code) : Roles.AssocEnv where
  impls := (visible (registry code) 0).map annotate
  coherent := by
    intro first firstMember last lastMember _
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp lastMember
    rfl

theorem environment_cores (code : Code) : (environment code).cores = visible (registry code) 0 := by
  simp [environment, Roles.AssocEnv.cores, List.map_map, Function.comp_def, annotate]

def requiredRole : Roles.RoleDecl := ⟨2, fun name => if name = 0 then some none else none,
  by intro name rhs member; split at member <;> cases member⟩

def undeclaredRole : Roles.RoleDecl := ⟨0, fun _ => none, by intros; contradiction⟩

def roleDeclarations : List Roles.RoleDecl := List.replicate 5 requiredRole

def roles : Roles.RoleDecls := fun name => (roleDeclarations[name]?).getD undeclaredRole

theorem roles_lt {name : Nat} (bound : name < 5) : roles name = requiredRole := by
  unfold roles roleDeclarations
  rw [List.getElem?_replicate]
  simp [bound]

theorem rule_source_bound (code : Code) {rule : Rule} (member : rule ∈ rules code) : rule.source < 5 := by
  rcases List.mem_append.mp member with generic | entry
  · have checked : CommonRoleLinearInterpreterRules.genericRules.all
        (fun rule => decide (rule.source < 5)) = true := by decide +kernel
    exact of_decide_eq_true ((List.all_eq_true.mp checked) rule generic)
  · obtain ⟨part, _, present⟩ := List.mem_flatMap.mp entry
    rw [entry_source part present]
    decide

theorem rule_target_bound (code : Code) {rule : Rule} (member : rule ∈ rules code) : rule.target < 5 := by
  rcases List.mem_append.mp member with generic | entry
  · have checked : CommonRoleLinearInterpreterRules.genericRules.all
        (fun rule => decide (rule.target < 5)) = true := by decide +kernel
    exact of_decide_eq_true ((List.all_eq_true.mp checked) rule generic)
  · obtain ⟨part, _, present⟩ := List.mem_flatMap.mp entry
    cases part <;>
      simp only [CommonRoleLinearInterpreterRules.entryRules, List.mem_cons,
        List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl
    all_goals simp only; omega

theorem visible_shape (code : Code) {implementation : Roles.Impl}
    (member : implementation ∈ visible (registry code) 0) :
    implementation.role < 5 ∧ implementation.head.length = 2 := by
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨by decide, rfl⟩
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    exact ⟨rule_source_bound code ((mem_registry code entry).mp present).1, rfl⟩

theorem constraints_declared (code : Code) {implementation : Roles.Impl}
    (member : implementation ∈ visible (registry code) 0)
    {child : Roles.Goal} (required : child ∈ implementation.constraints) :
    child.role < 5 ∧ child.args.length = (roles child.role).arity := by
  rcases List.mem_cons.mp member with rfl | member
  · cases required
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    have equality : child = ⟨entry.2.target, [.var entry.2.fresh, entry.2.right.encode]⟩ := by
      simpa [compile] using required
    subst child
    have bound := rule_target_bound code ((mem_registry code entry).mp present).1
    exact ⟨bound, by rw [roles_lt bound]; rfl⟩

theorem associated_wellFormed (code : Code) : Roles.AssocWellFormed (environment code) roles := by
  intro annotated member
  obtain ⟨implementation, present, rfl⟩ := List.mem_map.mp member
  have shape := visible_shape code present
  have signature := roles_lt shape.1
  constructor
  · intro name rhs body varName occurs
    have pair : (name, rhs) = (0, Pattern.int.encode) := by simpa [annotate] using body
    cases pair
    simp [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] at occurs
  · constructor
    · constructor
      · simpa [annotate, signature, requiredRole] using shape.2
      · intro name default declared
        change (roles implementation.role).assoc name = some default at declared
        rw [signature] at declared
        by_cases same : name = 0
        · subst name
          exact Or.inl ⟨Pattern.int.encode, rfl⟩
        · simp [requiredRole, same] at declared
    · intro name rhs body
      have pair : (name, rhs) = (0, Pattern.int.encode) := by simpa [annotate] using body
      cases pair
      exact ⟨none, by change (roles implementation.role).assoc 0 = _; rw [signature]; rfl⟩

/-- The approved condition for these fixed pattern meanings, with arbitrary
Common substitutions and every explicit associated RHS. -/
def HeadDeterminesAssociated (head : List Pattern) (associated : List Pattern) : Prop :=
  ∀ σ τ : Nat → Common.Ty,
    (∀ pattern ∈ head, Common.Equivalent (pattern.eval σ) (pattern.eval τ)) →
    ∀ rhs ∈ associated, Common.Equivalent (rhs.eval σ) (rhs.eval τ)

def checkConstantAssociated (associated : List Pattern) : Bool :=
  associated.all (fun rhs => decide (rhs = .int))

theorem checkConstantAssociated_sound (head associated : List Pattern)
    (accepted : checkConstantAssociated associated = true) : HeadDeterminesAssociated head associated := by
  intro σ τ _ rhs member
  have same := of_decide_eq_true ((List.all_eq_true.mp accepted) rhs member)
  subst rhs
  exact Common.equivalent_refl _

theorem head_determines_associated (head : List Pattern) : HeadDeterminesAssociated head [.int] :=
  checkConstantAssociated_sound head [.int] rfl

/-- An actual declaration-time test, not a premise of successful resolution. -/
def checkDeclaration (implementation : Roles.Impl) (associated : List Pattern) : Bool :=
  CheckedRoles.checkImpl implementation && checkConstantAssociated associated

theorem checkDeclaration_sound (implementation : Roles.Impl) (head associated : List Pattern)
    (accepted : checkDeclaration implementation associated = true) :
    implementation.WellFormed ∧ HeadDeterminesAssociated head associated := by
  obtain ⟨paterson, constant⟩ := Bool.and_eq_true_iff.mp accepted
  exact ⟨(CheckedRoles.checkImpl_exact implementation).mp paterson,
    checkConstantAssociated_sound head associated constant⟩

theorem each_declaration_checked (code : Code) (implementation : Roles.Impl)
    (member : implementation ∈ visible (registry code) 0) :
    checkDeclaration implementation [.int] = true := by
  have checked := (List.all_eq_true.mp (declarations_accepted code)) implementation member
  simpa [checkDeclaration, checkConstantAssociated] using checked

end Yulang.CommonRoleRegularRegistry
