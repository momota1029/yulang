import Yulang.CommonRoleStateMaterializedFrontier

/-! A source-computed bound on actual int-materialization changes. This is not
termination of saturation: ordinary changes, unchanged revisits, new templates,
source identities, graph sizes and language classification are outside scope. -/
namespace Yulang.CommonRoleMaterializationProgress
open CommonRoleCaptureNormalization (Form)
open CommonRoleIntervalPaterson (Argument Goal)
open CommonRoleStateMaterializedFrontier (materialize arguments materializeGoal)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)

/-- Counts occurrences, not distinct source names or ambient slots. -/
def remaining : Form → Nat
  | .var _ => 1
  | .int => 0
  | .pair a b | .join a b => remaining a + remaining b
  | .tick a => remaining a

theorem materialize_le (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (form : Form) :
    remaining (materialize atoms slots form) ≤ remaining form := by
  induction form with
  | var name => simp only [materialize]; split <;> simp [remaining]
  | int => exact Nat.le_refl _
  | pair a b ha hb => exact Nat.add_le_add ha hb
  | join a b ha hb => exact Nat.add_le_add ha hb
  | tick a ha => exact ha

/-- Equality of this concrete potential rules out any syntactic replacement. -/
theorem materialize_equal_of_count (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (form : Form) (equal : remaining (materialize atoms slots form) = remaining form) :
    materialize atoms slots form = form := by
  induction form with
  | var name => simp only [materialize] at *; split at equal <;> simp_all [remaining]
  | int => rfl
  | pair a b ha hb =>
      have la := materialize_le atoms slots a
      have lb := materialize_le atoms slots b
      simp only [materialize,remaining] at equal ⊢
      rw [ha (by omega),hb (by omega)]
  | join a b ha hb =>
      have la := materialize_le atoms slots a
      have lb := materialize_le atoms slots b
      simp only [materialize,remaining] at equal ⊢
      rw [ha (by omega),hb (by omega)]
  | tick a ha => exact congrArg Form.tick (ha equal)

def argumentCount : List Argument → Nat
  | [] => 0
  | (lo,hi) :: rest => remaining lo + remaining hi + argumentCount rest

theorem arguments_le (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (original : List Argument) : argumentCount (arguments atoms slots original) ≤ argumentCount original := by
  induction original with
  | nil => exact Nat.le_refl _
  | cons pair rest ih =>
      exact Nat.add_le_add (Nat.add_le_add (materialize_le atoms slots pair.1)
        (materialize_le atoms slots pair.2)) ih

theorem arguments_equal_of_count (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (original : List Argument)
    (equal : argumentCount (arguments atoms slots original) = argumentCount original) :
    arguments atoms slots original = original := by
  induction original with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨lo,hi⟩
      have ll := materialize_le atoms slots lo
      have lh := materialize_le atoms slots hi
      have lr := arguments_le atoms slots rest
      change remaining (materialize atoms slots lo) + remaining (materialize atoms slots hi) +
        argumentCount (arguments atoms slots rest) = remaining lo + remaining hi + argumentCount rest at equal
      change (materialize atoms slots lo,materialize atoms slots hi) :: arguments atoms slots rest = _
      rw [materialize_equal_of_count atoms slots lo (by omega),
        materialize_equal_of_count atoms slots hi (by omega),ih (by omega)]

def potential (goal : Goal) : Nat := argumentCount goal.arguments

theorem goal_le (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (original : Goal) :
    potential (materializeGoal atoms slots original) ≤ potential original :=
  arguments_le atoms slots original.arguments

theorem goal_equal_of_count (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (original : Goal) (equal : potential (materializeGoal atoms slots original) = potential original) :
    materializeGoal atoms slots original = original := by
  cases original with
  | mk role args =>
      exact congrArg (Goal.mk role) (arguments_equal_of_count atoms slots args equal)

theorem goal_fusion (before after : List (Atom (Fin n)))
    (included : ∀ atom ∈ before, atom ∈ after) (slots : Nat → Fin n)
    (assignment : Fin n → Comp Common.model) (models : All Common.model assignment after)
    (original : Goal) :
    materializeGoal after slots (materializeGoal before slots original) =
      materializeGoal after slots original := by
  cases original with
  | mk role args =>
      apply congrArg (Goal.mk role)
      change arguments after slots (arguments before slots args) = arguments after slots args
      simp only [arguments, List.map_map]
      apply List.map_congr_left
      intro pair _
      exact Prod.ext
        (CommonRoleStateMaterializedFrontier.rematerialize_fusion before after included slots assignment models pair.1)
        (CommonRoleStateMaterializedFrontier.rematerialize_fusion before after included slots assignment models pair.2)

/-- A semantic condition for the theorem, never supplied to execution. It permits
reordered and duplicated atoms and arbitrary fresh constraints. -/
def Extension (before after : List (Atom (Fin n))) : Prop :=
  (∀ atom ∈ before, atom ∈ after) ∧ ∃ assignment, All Common.model assignment after

theorem extension_le (before after : List (Atom (Fin n))) (extension : Extension before after)
    (slots : Nat → Fin n) (original : Goal) :
    potential (materializeGoal after slots original) ≤ potential (materializeGoal before slots original) := by
  obtain ⟨included,assignment,models⟩ := extension
  rw [← goal_fusion before after included slots assignment models original]
  exact goal_le after slots _

/-- Every changed materialized Goal consumes at least one original variable
occurrence. No uniqueness of an impl, source name, or slot map is assumed. -/
theorem extension_strict (before after : List (Atom (Fin n))) (extension : Extension before after)
    (slots : Nat → Fin n) (original : Goal)
    (changed : materializeGoal after slots original ≠ materializeGoal before slots original) :
    potential (materializeGoal after slots original) < potential (materializeGoal before slots original) := by
  have le := extension_le before after extension slots original
  have different : potential (materializeGoal after slots original) ≠
      potential (materializeGoal before slots original) := by
    intro equal
    obtain ⟨included,assignment,models⟩ := extension
    have fusion := goal_fusion before after included slots assignment models original
    apply changed
    rw [← fusion]
    apply goal_equal_of_count
    rw [fusion]
    exact equal
  omega

/-- Adjacent consistent, inclusive actual ordinary states; length is unrestricted. -/
def Chain (initial : List (Atom (Fin n))) : List (List (Atom (Fin n))) → Prop
  | [] => True
  | next :: rest => Extension initial next ∧ Chain next rest

/-- Count actual syntactic changes, including transitions across arbitrary
plateaus. Equal neighboring goals consume no budget and are not a stop signal. -/
def changes (slots : Nat → Fin n) (original : Goal) (initial : List (Atom (Fin n))) :
    List (List (Atom (Fin n))) → Nat
  | [] => 0
  | next :: rest =>
      (if materializeGoal next slots original = materializeGoal initial slots original then 0 else 1) +
        changes slots original next rest

def finalState (initial : List (Atom (Fin n))) : List (List (Atom (Fin n))) → List (Atom (Fin n))
  | [] => initial
  | next :: rest => finalState next rest

/-- The telescoping measure keeps remaining work explicit. This is a bound on
refinement events in a supplied trace, not a theorem that a solver produces one. -/
theorem changes_with_remaining (slots : Nat → Fin n) (original : Goal)
    (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (chain : Chain initial states) :
    changes slots original initial states +
      potential (materializeGoal (finalState initial states) slots original) ≤
      potential (materializeGoal initial slots original) := by
  induction states generalizing initial with
  | nil => simp [changes,finalState]
  | cons next rest ih =>
      have tail := ih next chain.2
      have le := extension_le initial next chain.1 slots original
      simp only [changes,finalState]
      split
      · rename_i same
        rw [same] at tail
        omega
      · rename_i different
        have strict := extension_strict initial next chain.1 slots original different
        omega

/-- Bound computed solely from the fixed original Goal, independent of the
number of ordinary updates, source sharing, registry or supplied trace length. -/
theorem changes_bounded (slots : Nat → Fin n) (original : Goal)
    (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (chain : Chain initial states) : changes slots original initial states ≤ potential original := by
  have sum := changes_with_remaining slots original initial states chain
  have start := goal_le initial slots original
  omega

/-- Actual public graph runs regenerate identical complete diagnostic trees when
materialized goals agree. Old demands may differ; their graphs need not agree. -/
theorem run_tree_equal (registry : List CommonRoleStablePaterson.Declaration)
    (slots : Nat → Fin n) (sources : CommonRoleGuardedIntervalPlans.Sources)
    (before after : List (Atom (Fin n)))
    (oldBefore oldAfter : CommonRoleGuardedIntervalPlans.Plan (Fin n)) (original : Goal)
    (same : materializeGoal before slots original = materializeGoal after slots original) :
    (CommonRoleStateMaterializedFrontier.run registry slots sources before oldBefore original).map Prod.fst =
      (CommonRoleStateMaterializedFrontier.run registry slots sources after oldAfter original).map Prod.fst := by
  simp only [CommonRoleStateMaterializedFrontier.run, CommonRoleFrontierGraphs.run_tree_exact]
  rw [same]

/-- A change in the actual complete diagnostic tree consumes the same source
potential. This says nothing about changes to ordinary graph contents. -/
theorem run_tree_strict (registry : List CommonRoleStablePaterson.Declaration)
    (slots : Nat → Fin n) (sources : CommonRoleGuardedIntervalPlans.Sources)
    (before after : List (Atom (Fin n))) (extension : Extension before after)
    (oldBefore oldAfter : CommonRoleGuardedIntervalPlans.Plan (Fin n)) (original : Goal)
    (changed :
      (CommonRoleStateMaterializedFrontier.run registry slots sources before oldBefore original).map Prod.fst ≠
        (CommonRoleStateMaterializedFrontier.run registry slots sources after oldAfter original).map Prod.fst) :
    potential (materializeGoal after slots original) < potential (materializeGoal before slots original) := by
  apply extension_strict before after extension slots original
  intro same
  exact changed (run_tree_equal registry slots sources before after oldBefore oldAfter original same.symm)

/-- Equal remaining counts force equal full diagnostic trees at these two
states. A later state can still change; this is not a saturation stop test. -/
theorem run_tree_plateau (registry : List CommonRoleStablePaterson.Declaration)
    (slots : Nat → Fin n) (sources : CommonRoleGuardedIntervalPlans.Sources)
    (before after : List (Atom (Fin n))) (extension : Extension before after)
    (oldBefore oldAfter : CommonRoleGuardedIntervalPlans.Plan (Fin n)) (original : Goal)
    (same : potential (materializeGoal after slots original) =
      potential (materializeGoal before slots original)) :
    (CommonRoleStateMaterializedFrontier.run registry slots sources before oldBefore original).map Prod.fst =
      (CommonRoleStateMaterializedFrontier.run registry slots sources after oldAfter original).map Prod.fst := by
  apply run_tree_equal
  by_cases equal : materializeGoal before slots original = materializeGoal after slots original
  · exact equal
  · have strict := extension_strict before after extension slots original (Ne.symm equal)
    omega

end Yulang.CommonRoleMaterializationProgress
