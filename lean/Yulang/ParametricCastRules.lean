import Yulang.CheckedRoles

/-!
# Non-growing first-order cast declarations

Spec §6.5 (2026-11-05, decision 22) permits parametric casts when target size
and every variable occurrence count do not exceed the source. We use the same
first-order terms, one-way matching, and exact substitution-size formula as role
resolution. Unlike role premises, cast sizes need not strictly decrease.

Ground declarations remain permitted, including a fixed larger target. Their
finite target sizes contribute to the global bound used by the search layer.
No nominal-only restriction is imposed on an instantiated target: `box 'a -> 'a`
can instantiate its result with an arbitrary ground term.

This layer concerns endpoint instances. Cast bodies/purity and duplicate-direct
rule diagnostics are separate checks; neither is a premise of the finiteness
argument. Constructor identifiers are arbitrary naturals, not an assumed finite
global type signature.
-/

namespace Yulang.ParametricCasts

open Roles

def Ground (term : Term) : Prop := term.bound = 0

mutual
  def symbols : Term → List Nat
    | .var _ => []
    | .app name args => name :: argsSymbols args
  def argsSymbols : List Term → List Nat
    | [] => []
    | head :: tail => symbols head ++ argsSymbols tail
end

mutual
  /-- Ground trees over the explicitly supplied finite constructor alphabet. -/
  def Over (alphabet : List Nat) : Term → Prop
    | .var _ => False
    | .app name args => name ∈ alphabet ∧ ArgsOver alphabet args
  def ArgsOver (alphabet : List Nat) : List Term → Prop
    | [] => True
    | head :: tail => Over alphabet head ∧ ArgsOver alphabet tail
end

mutual
  theorem over_ground {alphabet : List Nat} (term : Term) (over : Over alphabet term) :
      Ground term := by
    cases term with
    | var _ => exact False.elim over
    | app name args => exact argsOver_ground args over.2
  theorem argsOver_ground {alphabet : List Nat} (args : List Term)
      (over : ArgsOver alphabet args) : argsBound args = 0 := by
    cases args with
    | nil => rfl
    | cons head tail =>
        have headGround : head.bound = 0 := over_ground head over.1
        simp only [argsBound, headGround, argsOver_ground tail over.2, Nat.max_self]
end

mutual
  theorem over_of_ground (alphabet : List Nat) (term : Term) (ground : Ground term)
      (supported : ∀ name ∈ symbols term, name ∈ alphabet) : Over alphabet term := by
    cases term with
    | var name => simp [Ground, Term.bound] at ground
    | app name args =>
        exact ⟨supported name (by simp [symbols]),
          argsOver_of_ground alphabet args ground
            (fun name member => supported name (by simp [symbols, member]))⟩
  theorem argsOver_of_ground (alphabet : List Nat) (args : List Term)
      (ground : argsBound args = 0)
      (supported : ∀ name ∈ argsSymbols args, name ∈ alphabet) : ArgsOver alphabet args := by
    cases args with
    | nil => trivial
    | cons head tail =>
        have components : head.bound = 0 ∧ argsBound tail = 0 := by
          simpa [argsBound, Nat.max_eq_zero_iff] using ground
        exact ⟨over_of_ground alphabet head components.1
            (fun name member => supported name (by simp [argsSymbols, member])),
          argsOver_of_ground alphabet tail components.2
            (fun name member => supported name (by simp [argsSymbols, member]))⟩
end

mutual
  theorem ground_subst (term : Term) (ground : Ground term) (σ : Subst) :
      term.subst σ = term := by
    cases term with
    | var name => simp [Ground, Term.bound] at ground
    | app name args =>
        exact congrArg (Term.app name) (ground_args_subst args ground σ)
  theorem ground_args_subst (args : List Term) (ground : argsBound args = 0) (σ : Subst) :
      substArgs σ args = args := by
    cases args with
    | nil => rfl
    | cons head tail =>
        have components : head.bound = 0 ∧ argsBound tail = 0 := by
          simpa [argsBound, Nat.max_eq_zero_iff] using ground
        simp [substArgs, ground_subst head components.1 σ,
          ground_args_subst tail components.2 σ]
end

mutual
  /-- Every image of a used pattern variable occurs inside the instance. -/
  theorem image_over (pattern : Term) (σ : Subst) (alphabet : List Nat)
      (over : Over alphabet (pattern.subst σ)) (v : Nat)
      (used : 0 < pattern.occurrences v) : Over alphabet (σ v) := by
    cases pattern with
    | var name =>
        by_cases same : v = name
        · subst v
          exact over
        · simp [Term.occurrences, same] at used
    | app name args => exact args_image_over args σ alphabet over.2 v used
  theorem args_image_over (args : List Term) (σ : Subst) (alphabet : List Nat)
      (over : ArgsOver alphabet (substArgs σ args)) (v : Nat)
      (used : 0 < argsOccurrences v args) : Over alphabet (σ v) := by
    cases args with
    | nil => simp [argsOccurrences] at used
    | cons head tail =>
        by_cases first : 0 < head.occurrences v
        · exact image_over head σ alphabet over.1 v first
        · exact args_image_over tail σ alphabet over.2 v
            (by simp only [argsOccurrences] at used; omega)
end

mutual
  theorem subst_over (pattern : Term) (σ : Subst) (alphabet : List Nat)
      (supported : ∀ name ∈ symbols pattern, name ∈ alphabet)
      (images : ∀ v, 0 < pattern.occurrences v → Over alphabet (σ v)) :
      Over alphabet (pattern.subst σ) := by
    cases pattern with
    | var v => exact images v (by simp [Term.occurrences])
    | app name args =>
        exact ⟨supported name (by simp [symbols]),
          args_subst_over args σ alphabet
            (fun name member => supported name (by simp [symbols, member])) images⟩
  theorem args_subst_over (args : List Term) (σ : Subst) (alphabet : List Nat)
      (supported : ∀ name ∈ argsSymbols args, name ∈ alphabet)
      (images : ∀ v, 0 < argsOccurrences v args → Over alphabet (σ v)) :
      ArgsOver alphabet (substArgs σ args) := by
    cases args with
    | nil => trivial
    | cons head tail =>
        exact ⟨subst_over head σ alphabet
            (fun name member => supported name (by simp [argsSymbols, member]))
            (fun v used => images v (by simp only [argsOccurrences]; omega)),
          args_subst_over tail σ alphabet
            (fun name member => supported name (by simp [argsSymbols, member]))
            (fun v used => images v (by simp only [argsOccurrences]; omega))⟩
end

structure Rule where
  source : Term
  target : Term
  deriving DecidableEq, Repr

def Rule.ParametricValid (rule : Rule) : Prop :=
  rule.target.size ≤ rule.source.size ∧
    ∀ v, rule.target.occurrences v ≤ rule.source.occurrences v

def Rule.Valid (rule : Rule) : Prop :=
  (Ground rule.source ∧ Ground rule.target) ∨ rule.ParametricValid

def Rule.check (rule : Rule) : Bool :=
  decide (rule.source.bound = 0 ∧ rule.target.bound = 0) ||
    (decide (rule.target.size ≤ rule.source.size) &&
      CheckedRoles.checkOccurrences [rule.source] [rule.target])

theorem Rule.check_exact (rule : Rule) : rule.check = true ↔ rule.Valid := by
  simp [Rule.check, Rule.Valid, Rule.ParametricValid, Ground,
    CheckedRoles.checkOccurrences_exact, argsOccurrences]

def Valid (rules : List Rule) : Prop := ∀ rule ∈ rules, rule.Valid

def checkRules (rules : List Rule) : Bool := rules.all Rule.check

theorem checkRules_exact (rules : List Rule) : checkRules rules = true ↔ Valid rules := by
  simp [checkRules, Valid, List.all_eq_true, Rule.check_exact]

theorem Rule.variables_in_source (rule : Rule) (valid : rule.Valid) (v : Nat) :
    rule.target.occurrences v ≤ rule.source.occurrences v := by
  rcases valid with ⟨_, closed⟩ | parametric
  · rw [rule.target.occurrences_above_bound v (by simp [Ground] at closed; omega)]
    exact Nat.zero_le _
  · exact parametric.2 v

/-- Non-strict Paterson bound for *every* substitution, including ground images. -/
theorem Rule.substitution_nonincrease (rule : Rule) (valid : rule.ParametricValid)
    (σ : Subst) : (rule.target.subst σ).size ≤ (rule.source.subst σ).size := by
  let bound := max rule.target.bound rule.source.bound
  rw [rule.target.subst_size σ bound (Nat.le_max_left ..),
    rule.source.subst_size σ bound (Nat.le_max_right ..)]
  have weighted := sumBelow_mono bound (fun v =>
    Nat.mul_le_mul_right ((σ v).size - 1) (valid.2 v))
  have base := valid.1
  omega

def Rule.Instantiates (rule : Rule) (source target : Term) : Prop :=
  ∃ σ : Subst, rule.source.subst σ = source ∧ rule.target.subst σ = target

def Rule.fire (rule : Rule) (source : Term) : Option Term :=
  let σ := matchingSubst [rule.source] [source]
  if rule.source.subst σ = source then some (rule.target.subst σ) else none

theorem Rule.fire_sound (rule : Rule) (source target : Term)
    (fired : rule.fire source = some target) : rule.Instantiates source target := by
  dsimp only [Rule.fire] at fired
  split at fired
  next equal => exact ⟨_, equal, Option.some.inj fired⟩
  next => cases fired

theorem Rule.fire_complete (rule : Rule) (valid : rule.Valid) (source target : Term)
    (instanceOf : rule.Instantiates source target) : rule.fire source = some target := by
  rcases instanceOf with ⟨σ, sourceEq, targetEq⟩
  let τ := matchingSubst [rule.source] [source]
  have agrees (v : Nat) (used : 0 < rule.source.occurrences v) :
      τ v = σ v := by
    unfold τ
    rw [← sourceEq]
    exact matchingSubst_agrees [rule.source] σ v (by simpa [argsOccurrences] using used)
  have sourceMatches : rule.source.subst τ = source := by
    rw [rule.source.subst_congr τ σ agrees, sourceEq]
  have targetMatches : rule.target.subst τ = target := by
    rw [rule.target.subst_congr τ σ (fun v used =>
      agrees v (by have := rule.variables_in_source valid v; omega)), targetEq]
  dsimp only [τ] at sourceMatches targetMatches
  simp [Rule.fire, sourceMatches, targetMatches]

theorem Rule.fire_exact (rule : Rule) (valid : rule.Valid) (source target : Term) :
    rule.fire source = some target ↔ rule.Instantiates source target :=
  ⟨rule.fire_sound source target, rule.fire_complete valid source target⟩

def Step (rules : List Rule) (source target : Term) : Prop :=
  ∃ rule ∈ rules, rule.Instantiates source target

def successors (rules : List Rule) (source : Term) : List Term :=
  rules.filterMap (fun rule => rule.fire source)

theorem mem_successors (rules : List Rule) (valid : Valid rules) (source target : Term) :
    target ∈ successors rules source ↔ Step rules source target := by
  simp only [successors, List.mem_filterMap, Step]
  constructor
  · rintro ⟨rule, member, fired⟩
    exact ⟨rule, member, (rule.fire_exact (valid rule member) source target).mp fired⟩
  · rintro ⟨rule, member, instantiated⟩
    exact ⟨rule, member, (rule.fire_exact (valid rule member) source target).mpr instantiated⟩

inductive Path (rules : List Rule) (source : Term) : Term → Prop where
  | refl : Path rules source source
  | step : Path rules source middle → Step rules middle target → Path rules source target

def targetSize : List Rule → Nat
  | [] => 0
  | rule :: rules => max rule.target.size (targetSize rules)

theorem targetSize_bounds (rules : List Rule) (rule : Rule) (member : rule ∈ rules) :
    rule.target.size ≤ targetSize rules := by
  induction rules with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih later) (Nat.le_max_right ..)

theorem step_size (rules : List Rule) (valid : Valid rules) (source target : Term)
    (step : Step rules source target) : target.size ≤ max source.size (targetSize rules) := by
  rcases step with ⟨rule, member, σ, sourceEq, targetEq⟩
  rcases valid rule member with ⟨_, targetGround⟩ | parametric
  · have targetFixed := ground_subst rule.target targetGround σ
    rw [targetFixed] at targetEq
    rw [← targetEq]
    exact Nat.le_trans (targetSize_bounds rules rule member) (Nat.le_max_right ..)
  · have smaller := rule.substitution_nonincrease parametric σ
    rw [sourceEq, targetEq] at smaller
    exact Nat.le_trans smaller (Nat.le_max_left ..)

theorem path_size (rules : List Rule) (valid : Valid rules) {source target : Term}
    (path : Path rules source target) : target.size ≤ max source.size (targetSize rules) := by
  induction path with
  | refl => exact Nat.le_max_left ..
  | step path edge ih =>
      have bound := step_size rules valid _ _ edge
      exact Nat.le_trans bound (Nat.max_le.mpr ⟨ih, Nat.le_max_right ..⟩)

def alphabet (rules : List Rule) (source : Term) : List Nat :=
  symbols source ++ rules.flatMap (fun rule => symbols rule.target)

theorem step_over (rules : List Rule) (valid : Valid rules) (names : List Nat)
    (included : ∀ rule ∈ rules, ∀ name ∈ symbols rule.target, name ∈ names)
    (source target : Term) (over : Over names source) (step : Step rules source target) :
    Over names target := by
  rcases step with ⟨rule, member, σ, sourceEq, targetEq⟩
  rw [← targetEq]
  apply subst_over rule.target σ names (included rule member)
  intro v used
  apply image_over rule.source σ names (sourceEq ▸ over) v
  have := rule.variables_in_source (valid rule member) v
  omega

theorem path_over (rules : List Rule) (valid : Valid rules) {source target : Term}
    (ground : Ground source) (path : Path rules source target) :
    Over (alphabet rules source) target := by
  induction path with
  | refl =>
      apply over_of_ground _ _ ground
      intro name member
      exact List.mem_append.mpr (Or.inl member)
  | step path edge ih =>
      apply step_over rules valid _ ?_ _ _ ih edge
      intro rule member name present
      exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨rule, member, present⟩))

end Yulang.ParametricCasts
