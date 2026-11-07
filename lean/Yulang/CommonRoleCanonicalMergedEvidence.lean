import Yulang.CommonRoleMergedRegistry

/-! Independent evidence for a determined, tail-free single-tag row family.
The stored merged payload is contracted by idempotence; its ordinary rigid
data variables are then captured from the concrete payload. No assignment is
chosen by arbitrary Common head equivalence, and there is no record tail.
This finite input subset suffices to refute a total resolver on all regular
goals, if the success bit already cannot be decided here. -/
namespace Yulang.CommonRoleCanonicalMergedEvidence

open CommonRoleLinearClock (Pattern Ground Rule)
open CommonRoleMergedPayload
open CommonRoleMergedRegistry (compile terminalImpl)

structure Goal where
  role : Nat
  value : Ground
  deriving DecidableEq, Repr

def Goal.description (goal : Goal) : CommonRoleInspectedSemantics.Goal :=
  ⟨goal.role, .variant 0 (.ground goal.value)⟩

theorem goal_finite (goal : Goal) : goal.description.argument.finite = true := rfl

theorem goal_ready (visible : List Roles.Impl) (goal : Goal) :
    CommonRoleInspectedSemantics.Ready visible goal.description :=
  CommonRoleInspectedSemantics.finite_ready _ _ rfl

def Matches (implementation : Roles.Impl) (goal : Goal) (substitution : Nat → Ground) : Prop :=
  implementation.role = goal.role ∧ ∃ pattern, decodeHead implementation.head = some pattern ∧
    pattern.instantiate substitution = goal.value

def Unique (visible : List Roles.Impl) (implementation : Roles.Impl) (goal : Goal) : Prop :=
  ∀ other ∈ visible, (∃ substitution, Matches other goal substitution) → other = implementation

def capture (pattern : Pattern) (goal : Ground) : Nat → Ground :=
  CommonRoleLinearClock.matchingAssignment pattern goal

def headMatches (implementation : Roles.Impl) (goal : Goal) : Bool :=
  match decodeHead implementation.head with
  | none => false
  | some pattern => decide (implementation.role = goal.role ∧ pattern.instantiate (capture pattern goal.value) = goal.value)

theorem capture_reconstructs (pattern : Pattern) (value : Ground) (substitution : Nat → Ground)
    (matched : pattern.instantiate substitution = value) : pattern.instantiate (capture pattern value) = value := by
  apply CommonRoleLinearClock.matchingAssignment_head pattern value (fun name => (substitution name).eval)
  rw [← CommonRoleLinearClock.instantiate_eval, matched]
  exact Common.equivalent_refl _

theorem capture_agrees (pattern : Pattern) (value : Ground) (substitution : Nat → Ground)
    (matched : pattern.instantiate substitution = value) (name : Nat) (used : 0 < pattern.encode.occurrences name) :
    capture pattern value name = substitution name := by
  apply (CommonRoleLinearClock.Ground.equivalent_iff _ _).mp
  apply Common.equivalent_symm
  apply CommonRoleLinearClock.matchingAssignment_agrees pattern value (fun name => (substitution name).eval)
  · rw [← CommonRoleLinearClock.instantiate_eval, matched]
    exact Common.equivalent_refl _
  · exact used

theorem head_matches_exact (implementation : Roles.Impl) (goal : Goal) :
    headMatches implementation goal = true ↔ ∃ substitution, Matches implementation goal substitution := by
  unfold headMatches
  cases decoded : decodeHead implementation.head with
  | none => simp [Matches, decoded]
  | some pattern =>
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨role, matched⟩
        exact ⟨capture pattern goal.value, role, pattern, decoded, matched⟩
      · rintro ⟨substitution, role, source, read, matched⟩
        have equal := Option.some.inj (decoded.symm.trans read)
        subst source
        exact ⟨role, capture_reconstructs pattern goal.value substitution matched⟩

theorem captures_unique_on_used (pattern : Pattern) (value : Ground) (σ τ : Nat → Ground)
    (first : pattern.instantiate σ = value) (last : pattern.instantiate τ = value)
    (name : Nat) (used : 0 < pattern.encode.occurrences name) : σ name = τ name :=
  (capture_agrees pattern value σ first name used).symm.trans (capture_agrees pattern value τ last name used)

theorem requirements_determined (rule : Rule) (linear : CommonRoleLinearClock.Linear rule)
    (value : Ground) (σ τ : Nat → Ground) (first : rule.left.instantiate σ = value) (last : rule.left.instantiate τ = value) :
    rule.right.instantiate σ = rule.right.instantiate τ := by
  apply (CommonRoleLinearClock.Ground.equivalent_iff _ _).mp
  rw [CommonRoleLinearClock.instantiate_eval, CommonRoleLinearClock.instantiate_eval]
  apply CommonRoleLinearClock.Pattern.eval_congr
  intro name used
  have covered := linear name
  have equal := captures_unique_on_used rule.left value σ τ first last name (by omega)
  rw [equal]
  exact Common.equivalent_refl _

@[simp] theorem matches_compile (key : Nat) (rule : Rule) (goal : Goal) (substitution : Nat → Ground) :
    Matches (compile key rule) goal substitution ↔
      rule.source = goal.role ∧ rule.left.instantiate substitution = goal.value := by
  simp [Matches, CommonRoleMergedRegistry.compile]

@[simp] theorem matches_terminal (goal : Goal) (substitution : Nat → Ground) :
    Matches terminalImpl goal substitution ↔ 0 = goal.role ∧ substitution 0 = goal.value := by
  simp [Matches, terminalImpl, plainTerm, CommonRoleLinearClock.Pattern.instantiate]

def interpretGoal (requirement : Roles.Goal) (substitution : Nat → Ground) : Option Goal :=
  (decodeHead requirement.args).map (fun pattern => ⟨requirement.role, pattern.instantiate substitution⟩)

@[simp] theorem child_interpreted (rule : Rule) (substitution : Nat → Ground) :
    interpretGoal ⟨rule.target, [plainTerm rule.right]⟩ substitution = some ⟨rule.target, rule.right.instantiate substitution⟩ := by
  simp [interpretGoal, plainTerm]

mutual
  inductive Dictionary (visible : List Roles.Impl) : Goal → Type where
    | impl {goal} (implementation : Roles.Impl) (substitution : Nat → Ground)
        (member : implementation ∈ visible) (matched : Matches implementation goal substitution)
        (unique : Unique visible implementation goal)
        (children : Children visible substitution implementation.constraints) : Dictionary visible goal
  inductive Children (visible : List Roles.Impl) : (Nat → Ground) → List Roles.Goal → Type where
    | nil {substitution} : Children visible substitution []
    | cons {substitution} (requirement : Roles.Goal) (child : Goal) (rest : List Roles.Goal)
        (interpreted : interpretGoal requirement substitution = some child)
        (dictionary : Dictionary visible child) (children : Children visible substitution rest) :
        Children visible substitution (requirement :: rest)
end

mutual
  def Dictionary.erase {visible : List Roles.Impl} {goal : Goal} : Dictionary visible goal → RoleDictionaries.Plan
    | .impl implementation _ _ _ _ children => .node implementation children.erase
  def Children.erase {visible : List Roles.Impl} {substitution : Nat → Ground} {requirements : List Roles.Goal} :
      Children visible substitution requirements → List RoleDictionaries.Plan
    | .nil => []
    | .cons _ _ _ _ dictionary children => dictionary.erase :: children.erase
end

theorem Dictionary.all_visible {visible : List Roles.Impl} {goal : Goal} (dictionary : Dictionary visible goal) :
    ∀ implementation ∈ dictionary.erase.declarations, implementation ∈ visible := by
  induction dictionary using Dictionary.rec (motive_2 := fun _ _ children =>
    ∀ implementation ∈ children.erase.flatMap RoleDictionaries.Plan.declarations, implementation ∈ visible) with
  | impl implementation substitution member matched unique children ih =>
      intro wanted present
      simp only [Dictionary.erase, RoleDictionaries.Plan.declarations, List.mem_cons] at present
      exact present.elim (fun same => same ▸ member) (ih wanted)
  | nil => contradiction
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      rename_i wanted present
      simp only [Children.erase, List.flatMap_cons, List.mem_append] at present
      exact present.elim (ihChild wanted) (ihRest wanted)

end Yulang.CommonRoleCanonicalMergedEvidence
