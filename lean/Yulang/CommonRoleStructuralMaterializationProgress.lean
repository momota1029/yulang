import Yulang.CommonRoleStructuralOrdinaryMaterialization
import Yulang.CommonRoleMaterializationProgress
import Yulang.CommonRoleCheckedOrdinaryReplay

/-! A two-phase progress budget for actual closed structural evidence.
Syntactically different but equivalent payloads can turn unique evidence into
unresolved evidence. Each original occurrence can therefore change twice.
This bounds materialization changes, not termination of a supplied batch stream. -/
namespace Yulang.CommonRoleStructuralMaterializationProgress
open CommonRoleCaptureNormalization (Form)
open CommonRoleStructuralOrdinaryMaterialization (Evidence candidates detect materialize materializeGoal)
open CommonRoleIntervalPaterson (Goal Argument)
open PresenceNormalForm (Atom)

abbrev Included (before after : List (Atom (Fin n))) : Prop := ∀ a ∈ before, a ∈ after

variable {n : Nat} {before after : List (Atom (Fin n))}

theorem evidence_mono (included : Included before after) (slot : Fin n) (f : Form)
    (evidence : Evidence before slot f) : Evidence after slot f := by
  obtain ⟨⟨a,ha,da⟩,b,hb,db⟩ := evidence
  exact ⟨⟨a,included _ ha,da⟩,b,included _ hb,db⟩

theorem detected_nonempty (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form)
    (found : detect atoms slot = some f) : candidates atoms slot ≠ [] := by
  have member := (CommonRoleStructuralOrdinaryMaterialization.candidates_exact atoms slot f).mpr
    ((CommonRoleStructuralOrdinaryMaterialization.detect_exact atoms slot f).mp found).1
  intro empty
  rw [empty] at member
  cases member

theorem nonempty_mono (included : Included before after) (slot : Fin n)
    (nonempty : candidates before slot ≠ []) : candidates after slot ≠ [] := by
  cases eq : candidates before slot with
  | nil => exact False.elim (nonempty eq)
  | cons f rest =>
    have evidence := (CommonRoleStructuralOrdinaryMaterialization.candidates_exact before slot f).mp
      (by rw [eq]; exact List.mem_cons_self)
    have member := (CommonRoleStructuralOrdinaryMaterialization.candidates_exact after slot f).mpr
      (evidence_mono included slot f evidence)
    intro empty
    rw [empty] at member
    cases member

/-- Different singleton payloads cannot replace one another on inclusive states. -/
theorem detected_same (included : Included before after) (slot : Fin n) (f g : Form)
    (old : detect before slot = some f) (new : detect after slot = some g) : f = g := by
  have oldEvidence := ((CommonRoleStructuralOrdinaryMaterialization.detect_exact before slot f).mp old).1
  exact ((CommonRoleStructuralOrdinaryMaterialization.detect_exact after slot g).mp new).2 f
    (evidence_mono included slot f oldEvidence)

/-- Once several distinct payloads are present, later additions cannot restore
syntactic uniqueness, even if every payload has the same semantic meaning. -/
theorem conflict_persists (included : Included before after) (slot : Fin n)
    (nonempty : candidates before slot ≠ []) (old : detect before slot = none) :
    detect after slot = none := by
  cases new : detect after slot with
  | none => rfl
  | some g =>
    have unique := ((CommonRoleStructuralOrdinaryMaterialization.detect_exact after slot g).mp new).2
    cases eq : candidates before slot with
    | nil => exact False.elim (nonempty eq)
    | cons f rest =>
      have evidence := (CommonRoleStructuralOrdinaryMaterialization.candidates_exact before slot f).mp
        (by rw [eq]; exact List.mem_cons_self)
      have same := unique f (evidence_mono included slot f evidence)
      subst f
      have found : detect before slot = some g :=
        (CommonRoleStructuralOrdinaryMaterialization.detect_exact before slot g).mpr
          ⟨evidence,fun other h => unique other (evidence_mono included slot other h)⟩
      rw [old] at found
      cases found

/-- 2 = no payload, 1 = one distinct syntax, 0 = irreversible conflict. -/
def budget (atoms : List (Atom (Fin n))) (slot : Fin n) : Nat :=
  if candidates atoms slot = [] then 2 else if detect atoms slot = none then 0 else 1

theorem budget_le_two (atoms : List (Atom (Fin n))) (slot : Fin n) : budget atoms slot ≤ 2 := by
  unfold budget
  split <;> (try split) <;> omega

theorem budget_mono (included : Included before after) (slot : Fin n) :
    budget after slot ≤ budget before slot := by
  by_cases empty : candidates before slot = []
  · simpa [budget,empty] using budget_le_two after slot
  · have later := nonempty_mono included slot empty
    cases old : detect before slot with
    | none => simp [budget,empty,later,old,conflict_persists included slot empty old]
    | some f =>
      simp only [budget,empty,later,ite_false,old,reduceCtorEq]
      split <;> omega

theorem detector_equal_of_budget (included : Included before after) (slot : Fin n)
    (equal : budget after slot = budget before slot) : detect after slot = detect before slot := by
  by_cases empty : candidates before slot = []
  · by_cases later : candidates after slot = []
    · simp [CommonRoleStructuralOrdinaryMaterialization.detect,empty,later]
    · simp only [budget,empty,later,ite_true,ite_false] at equal
      split at equal <;> omega
  · have later := nonempty_mono included slot empty
    cases old : detect before slot with
    | none => exact conflict_persists included slot empty old
    | some f =>
      cases new : detect after slot with
      | none => simp [budget,empty,later,old,new] at equal
      | some g => rw [← detected_same included slot f g old new]

def formBudget (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) : Form → Nat
  | .var name => budget atoms (slots name)
  | .int => 0
  | .pair a b | .join a b => formBudget atoms slots a + formBudget atoms slots b
  | .tick a => formBudget atoms slots a

theorem form_budget_mono (included : Included before after) (slots : Nat → Fin n) (f : Form) :
    formBudget after slots f ≤ formBudget before slots f := by
  induction f with
  | var name => exact budget_mono included (slots name)
  | int => exact Nat.le_refl _
  | pair a b ha hb | join a b ha hb => exact Nat.add_le_add ha hb
  | tick a ha => exact ha

theorem form_budget_bound (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (f : Form) :
    formBudget atoms slots f ≤ 2 * CommonRoleMaterializationProgress.remaining f := by
  induction f with
  | var name => exact budget_le_two atoms (slots name)
  | int => exact Nat.le_refl _
  | pair a b ha hb | join a b ha hb =>
    simp only [formBudget,CommonRoleMaterializationProgress.remaining,Nat.mul_add]
    omega
  | tick a ha => exact ha

theorem form_equal_of_budget (included : Included before after) (slots : Nat → Fin n) (f : Form)
    (equal : formBudget after slots f = formBudget before slots f) :
    materialize after slots f = materialize before slots f := by
  induction f with
  | var name => simp only [materialize]; rw [detector_equal_of_budget included (slots name) equal]
  | int => rfl
  | pair a b ha hb | join a b ha hb =>
    have la := form_budget_mono included slots a
    have lb := form_budget_mono included slots b
    simp only [formBudget] at equal
    simp only [materialize,ha (by omega),hb (by omega)]
  | tick a ha => exact congrArg Form.tick (ha equal)

def argumentsBudget (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) : List Argument → Nat
  | [] => 0
  | (lo,hi) :: rest => formBudget atoms slots lo + formBudget atoms slots hi + argumentsBudget atoms slots rest

def potential (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (goal : Goal) : Nat :=
  argumentsBudget atoms slots goal.arguments

theorem arguments_budget_mono (included : Included before after) (slots : Nat → Fin n) (args : List Argument) :
    argumentsBudget after slots args ≤ argumentsBudget before slots args := by
  induction args with
  | nil => exact Nat.le_refl _
  | cons arg rest ih =>
    exact Nat.add_le_add (Nat.add_le_add (form_budget_mono included slots arg.1) (form_budget_mono included slots arg.2)) ih

theorem arguments_budget_bound (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (args : List Argument) :
    argumentsBudget atoms slots args ≤ 2 * CommonRoleMaterializationProgress.argumentCount args := by
  induction args with
  | nil => exact Nat.le_refl _
  | cons arg rest ih =>
    have lo := form_budget_bound atoms slots arg.1
    have hi := form_budget_bound atoms slots arg.2
    simp only [argumentsBudget,CommonRoleMaterializationProgress.argumentCount,Nat.mul_add]
    omega

theorem arguments_equal_of_budget (included : Included before after) (slots : Nat → Fin n)
    (args : List Argument) (equal : argumentsBudget after slots args = argumentsBudget before slots args) :
    args.map (fun p => (materialize after slots p.1,materialize after slots p.2)) =
      args.map (fun p => (materialize before slots p.1,materialize before slots p.2)) := by
  induction args with
  | nil => rfl
  | cons arg rest ih =>
    have lo := form_budget_mono included slots arg.1
    have hi := form_budget_mono included slots arg.2
    have tail := arguments_budget_mono included slots rest
    simp only [argumentsBudget] at equal
    simp only [List.map_cons,form_equal_of_budget included slots arg.1 (by omega),
      form_equal_of_budget included slots arg.2 (by omega),ih (by omega)]

theorem goal_equal_of_budget (included : Included before after) (slots : Nat → Fin n)
    (goal : Goal) (equal : potential after slots goal = potential before slots goal) :
    materializeGoal after slots goal = materializeGoal before slots goal :=
  congrArg (Goal.mk goal.role) (arguments_equal_of_budget included slots goal.arguments equal)

theorem goal_strict (included : Included before after) (slots : Nat → Fin n) (goal : Goal)
    (changed : materializeGoal after slots goal ≠ materializeGoal before slots goal) :
    potential after slots goal < potential before slots goal := by
  have le := arguments_budget_mono included slots goal.arguments
  have different : potential after slots goal ≠ potential before slots goal :=
    fun equal => changed (goal_equal_of_budget included slots goal equal)
  change potential after slots goal ≤ potential before slots goal at le
  omega

def Chain (initial : List (Atom (Fin n))) : List (List (Atom (Fin n))) → Prop
  | [] => True
  | next :: rest => Included initial next ∧ Chain next rest

def changes (slots : Nat → Fin n) (goal : Goal) (initial : List (Atom (Fin n))) :
    List (List (Atom (Fin n))) → Nat
  | [] => 0
  | next :: rest => (if materializeGoal next slots goal = materializeGoal initial slots goal then 0 else 1) +
      changes slots goal next rest

def finalState (initial : List (Atom (Fin n))) : List (List (Atom (Fin n))) → List (Atom (Fin n))
  | [] => initial
  | next :: rest => finalState next rest

theorem changes_with_remaining (slots : Nat → Fin n) (goal : Goal)
    (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n)))) (chain : Chain initial states) :
    changes slots goal initial states + potential (finalState initial states) slots goal ≤
      potential initial slots goal := by
  induction states generalizing initial with
  | nil => simp [changes,finalState]
  | cons next rest ih =>
    have tail := ih next chain.2
    have le := arguments_budget_mono chain.1 slots goal.arguments
    change potential next slots goal ≤ potential initial slots goal at le
    simp only [changes,finalState]
    split
    · omega
    · rename_i different
      have strict := goal_strict chain.1 slots goal different
      omega

/-- Every inclusive ordinary trace changes this original goal at most twice
per source variable occurrence, regardless of payload depth or consistency. -/
theorem changes_bounded (slots : Nat → Fin n) (goal : Goal)
    (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n)))) (chain : Chain initial states) :
    changes slots goal initial states ≤ 2 * CommonRoleMaterializationProgress.potential goal := by
  have sum := changes_with_remaining slots goal initial states chain
  have bound := arguments_budget_bound initial slots goal.arguments
  change potential initial slots goal ≤ 2 * CommonRoleMaterializationProgress.potential goal at bound
  omega

/-- The actual append operation constructs the required inclusive trace.
No model, consistency result, execution trace or Chain is supplied. -/
theorem computed_chain (initial : CommonRoleSettledConstraints.State n)
    (batches : List (CommonRoleSettledConstraints.State n)) :
    Chain initial.atoms ((CommonRoleCheckedOrdinaryReplay.trace initial batches).map
      CommonRoleSettledConstraints.State.atoms) := by
  induction batches generalizing initial with
  | nil => trivial
  | cons batch rest ih =>
    exact ⟨fun _ member => List.mem_append_left _ member,
      ih (CommonRoleCheckedOrdinaryReplay.append initial batch)⟩

theorem computed_changes_bounded (slots : Nat → Fin n) (goal : Goal)
    (initial : CommonRoleSettledConstraints.State n)
    (batches : List (CommonRoleSettledConstraints.State n)) :
    changes slots goal initial.atoms ((CommonRoleCheckedOrdinaryReplay.trace initial batches).map
      CommonRoleSettledConstraints.State.atoms) ≤ 2 * CommonRoleMaterializationProgress.potential goal :=
  changes_bounded slots goal initial.atoms _ (computed_chain initial batches)

end Yulang.CommonRoleStructuralMaterializationProgress
