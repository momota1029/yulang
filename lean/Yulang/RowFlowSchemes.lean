import Yulang.StructuralBase
import Yulang.FiniteWorklist

/-!
# Shared-parameter schemes for core row-flow constraints

Core row terms contain only variables, the empty row, and joins. This solver
supports a variable or empty row on the right of each inequality. Left joins
decompose into variable-flow edges and upper bounds by the empty row.

A variable forced below empty contributes no free parameter. Every other
parameter flows to all of its reachable successors. Their finite joins form
an unconstrained scheme representing every original row assignment, up to
mutual inclusion. Correlations are retained by shared parameter identities;
unconstrained variables are not all defaulted to the empty row.

Right joins are reported as unsupported. There is no inconsistent result in
this fragment: the all-empty assignment satisfies every core row constraint.
Operation heads, protection, release, and signed row weights are separate
layers and are not added to this syntax or its proof.
-/

namespace Yulang.RowFlowSchemes

open Inference (RowTerm)

universe u v

/-- A join semilattice up to mutual inclusion; antisymmetry is unnecessary. -/
structure Algebra (Row : Type u) where
  empty : Row
  join : Row → Row → Row
  le : Row → Row → Prop
  refl : ∀ row, le row row
  trans : ∀ {a b c}, le a b → le b c → le a c
  empty_le : ∀ row, le empty row
  join_le_iff : ∀ left right upper, le (join left right) upper ↔ le left upper ∧ le right upper

variable {n : Nat} {Row : Type u}

theorem Algebra.le_join_left (algebra : Algebra Row) (left right : Row) :
    algebra.le left (algebra.join left right) :=
  ((algebra.join_le_iff left right _).mp (algebra.refl _)).1

theorem Algebra.le_join_right (algebra : Algebra Row) (left right : Row) :
    algebra.le right (algebra.join left right) :=
  ((algebra.join_le_iff left right _).mp (algebra.refl _)).2

theorem Algebra.join_mono (algebra : Algebra Row) {a b c d : Row}
    (left : algebra.le a c) (right : algebra.le b d) :
    algebra.le (algebra.join a b) (algebra.join c d) :=
  (algebra.join_le_iff _ _ _).mpr
    ⟨algebra.trans left (algebra.le_join_left _ _), algebra.trans right (algebra.le_join_right _ _)⟩

def Equivalent (algebra : Algebra Row) (left right : Row) : Prop :=
  algebra.le left right ∧ algebra.le right left

abbrev Valuation (n : Nat) (Row : Type u) := Fin n → Row

def PointwiseEquivalent (algebra : Algebra Row) (left right : Valuation n Row) : Prop :=
  ∀ index, Equivalent algebra (left index) (right index)

def eval (algebra : Algebra Row) (valuation : α → Row) : RowTerm α → Row
  | .var index => valuation index
  | .empty => algebra.empty
  | .join left right => algebra.join (eval algebra valuation left) (eval algebra valuation right)

theorem eval_core (model : Inference.Model) (algebra : Algebra model.Row)
    (empty : algebra.empty = model.empty)
    (join : ∀ left right, algebra.join left right = model.join left right)
    (environment : α → Inference.Comp model) (term : RowTerm α) :
    eval algebra (fun index => (environment index).2) term = term.eval model environment := by
  induction term <;> simp_all [eval, RowTerm.eval]

theorem eval_equivalent (algebra : Algebra Row) (left right : Valuation n Row)
    (equivalent : PointwiseEquivalent algebra left right) (term : RowTerm (Fin n)) :
    Equivalent algebra (eval algebra left term) (eval algebra right term) := by
  induction term with
  | var index => exact equivalent index
  | empty => exact ⟨algebra.refl _, algebra.refl _⟩
  | join a b iha ihb => exact ⟨algebra.join_mono iha.1 ihb.1, algebra.join_mono iha.2 ihb.2⟩

def variables : RowTerm α → List α
  | .var index => [index]
  | .empty => []
  | .join left right => variables left ++ variables right

theorem eval_le_iff (algebra : Algebra Row) (valuation : α → Row)
    (term : RowTerm α) (upper : Row) :
    algebra.le (eval algebra valuation term) upper ↔
      ∀ index ∈ variables term, algebra.le (valuation index) upper := by
  induction term with
  | var index => simp [eval, variables]
  | empty =>
      constructor
      · intro _ _ impossible
        cases impossible
      · intro _
        exact algebra.empty_le _
  | join left right ihl ihr =>
      simp only [eval, algebra.join_le_iff, ihl, ihr, variables,
        List.mem_append, or_imp, forall_and]

abbrev Constraint (n : Nat) := RowTerm (Fin n) × RowTerm (Fin n)
abbrev Problem (n : Nat) := List (Constraint n)

def Constraint.Holds (algebra : Algebra Row) (valuation : Valuation n Row) (constraint : Constraint n) : Prop :=
  algebra.le (eval algebra valuation constraint.1) (eval algebra valuation constraint.2)

def Models (algebra : Algebra Row) (problem : Problem n) (valuation : Valuation n Row) : Prop :=
  ∀ constraint ∈ problem, constraint.Holds algebra valuation

theorem models_equivalent (algebra : Algebra Row) (problem : Problem n)
    (left right : Valuation n Row) (model : Models algebra problem left)
    (equivalent : PointwiseEquivalent algebra left right) : Models algebra problem right := by
  intro constraint member
  exact algebra.trans (eval_equivalent algebra left right equivalent constraint.1).2
    (algebra.trans (model constraint member) (eval_equivalent algebra left right equivalent constraint.2).1)

/-- Unsupported syntax is not an inconsistency result: every problem in
the empty/join/variable language has this assignment. -/
theorem empty_assignment_models (algebra : Algebra Row) (problem : Problem n) :
    Models algebra problem (fun _ => algebra.empty) := by
  intro constraint _
  exact algebra.trans ((eval_le_iff algebra (fun _ => algebra.empty) constraint.1 algebra.empty).mpr
    (fun _ _ => algebra.refl _)) (algebra.empty_le _)

def supportedConstraint (constraint : Constraint n) : Bool :=
  match constraint.2 with
  | .var _ | .empty => true
  | .join _ _ => false

def supported (problem : Problem n) : Bool := problem.all supportedConstraint

inductive FlatConstraint (n : Nat) where
  | flow (source target : Fin n)
  | pure (source : Fin n)
  deriving DecidableEq, Repr

abbrev FlatProblem (n : Nat) := List (FlatConstraint n)

def FlatConstraint.Holds (algebra : Algebra Row) (valuation : Valuation n Row) : FlatConstraint n → Prop
  | .flow source target => algebra.le (valuation source) (valuation target)
  | .pure source => algebra.le (valuation source) algebra.empty

def FlatModels (algebra : Algebra Row) (problem : FlatProblem n) (valuation : Valuation n Row) : Prop :=
  ∀ constraint ∈ problem, constraint.Holds algebra valuation

def flattenConstraint (constraint : Constraint n) : FlatProblem n :=
  match constraint.2 with
  | .var target => (variables constraint.1).map fun source => .flow source target
  | .empty => (variables constraint.1).map FlatConstraint.pure
  | .join _ _ => []

def flatten (problem : Problem n) : FlatProblem n := problem.flatMap flattenConstraint

theorem flattenConstraint_exact (algebra : Algebra Row) (constraint : Constraint n)
    (valuation : Valuation n Row) (checked : supportedConstraint constraint = true) :
    FlatModels algebra (flattenConstraint constraint) valuation ↔ constraint.Holds algebra valuation := by
  obtain ⟨left, right⟩ := constraint
  cases right with
  | var target =>
      simpa only [FlatModels, flattenConstraint, List.forall_mem_map, FlatConstraint.Holds,
        Constraint.Holds, eval] using (eval_le_iff algebra valuation left (valuation target)).symm
  | empty =>
      simpa only [FlatModels, flattenConstraint, List.forall_mem_map, FlatConstraint.Holds,
        Constraint.Holds, eval] using (eval_le_iff algebra valuation left algebra.empty).symm
  | join => cases checked

theorem flatten_models_iff (algebra : Algebra Row) (problem : Problem n)
    (checked : supported problem = true) (valuation : Valuation n Row) :
    FlatModels algebra (flatten problem) valuation ↔ Models algebra problem valuation := by
  constructor
  · intro model constraint member
    apply (flattenConstraint_exact algebra constraint valuation (List.all_eq_true.mp checked constraint member)).mp
    intro flat present
    exact model flat (List.mem_flatMap.mpr ⟨constraint, member, present⟩)
  · intro model flat member
    obtain ⟨constraint, originalMember, present⟩ := List.mem_flatMap.mp member
    exact ((flattenConstraint_exact algebra constraint valuation
      (List.all_eq_true.mp checked constraint originalMember)).mpr (model constraint originalMember)) flat present

/-! ## Finite propagation and elimination of pure parameters -/

def successors (problem : FlatProblem n) (source : Fin n) : List (Fin n) :=
  problem.filterMap fun
    | .flow start target => if start = source then some target else none
    | .pure _ => none

@[simp] theorem mem_successors (problem : FlatProblem n) (source target : Fin n) :
    target ∈ successors problem source ↔ .flow source target ∈ problem := by
  simp only [successors, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, found⟩
    cases constraint with
    | flow start finish =>
        change (if start = source then some finish else none) = some target at found
        split at found
        · rename_i same
          subst start
          have equal : finish = target := Option.some.inj found
          subst finish
          exact member
        · cases found
    | pure => cases found
  · intro member
    exact ⟨.flow source target, member, by simp⟩

abbrev Reaches (problem : FlatProblem n) (source target : Fin n) : Prop :=
  FiniteWorklist.Path (successors problem) source target

def reachable (problem : FlatProblem n) (source : Fin n) : List (Fin n) :=
  FiniteWorklist.reachable (successors problem) n source

theorem reachable_exact (problem : FlatProblem n) (source target : Fin n) :
    target ∈ reachable problem source ↔ Reaches problem source target := by
  apply FiniteWorklist.reachable_exact (successors problem) n (List.finRange n)
  · intro vertex
    simp
  · simp

def pureTargets (problem : FlatProblem n) : List (Fin n) :=
  problem.filterMap fun
    | .pure source => some source
    | .flow _ _ => none

@[simp] theorem mem_pureTargets (problem : FlatProblem n) (target : Fin n) :
    target ∈ pureTargets problem ↔ .pure target ∈ problem := by
  simp only [pureTargets, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, found⟩
    cases constraint with
    | pure source =>
        have same := Option.some.inj found
        subst source
        exact member
    | flow => cases found
  · intro member
    exact ⟨.pure target, member, rfl⟩

def forcedPure (problem : FlatProblem n) (source : Fin n) : Bool :=
  (pureTargets problem).any fun target => decide (target ∈ reachable problem source)

theorem forcedPure_exact (problem : FlatProblem n) (source : Fin n) :
    forcedPure problem source = true ↔
      ∃ target, .pure target ∈ problem ∧ Reaches problem source target := by
  simp only [forcedPure, List.any_eq_true, decide_eq_true_eq, mem_pureTargets, reachable_exact]

theorem forcedPure_of_reaches (problem : FlatProblem n) {source target : Fin n}
    (path : Reaches problem source target) (pure : forcedPure problem target = true) :
    forcedPure problem source = true := by
  obtain ⟨finish, upper, rest⟩ := (forcedPure_exact problem target).mp pure
  exact (forcedPure_exact problem source).mpr ⟨finish, upper, path.append rest⟩

def ancestors (problem : FlatProblem n) (target : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun source => target ∈ reachable problem source

theorem mem_ancestors (problem : FlatProblem n) (source target : Fin n) :
    source ∈ ancestors problem target ↔ Reaches problem source target := by
  simp only [ancestors, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, reachable_exact]

def contributors (problem : FlatProblem n) (target : Fin n) : List (Fin n) :=
  (ancestors problem target).filter fun source => !(forcedPure problem source)

theorem mem_contributors (problem : FlatProblem n) (source target : Fin n) :
    source ∈ contributors problem target ↔ Reaches problem source target ∧ forcedPure problem source = false := by
  simp [contributors, mem_ancestors]

theorem reaches_le (algebra : Algebra Row) {problem : FlatProblem n} {valuation : Valuation n Row}
    (model : FlatModels algebra problem valuation) {source target : Fin n} (path : Reaches problem source target) :
    algebra.le (valuation source) (valuation target) := by
  induction path with
  | nil => exact algebra.refl _
  | @cons source middle target edge _ ih =>
      exact algebra.trans (model (.flow source middle) ((mem_successors problem source middle).mp edge)) ih

theorem forcedPure_le_empty (algebra : Algebra Row) {problem : FlatProblem n} {valuation : Valuation n Row}
    (model : FlatModels algebra problem valuation) (source : Fin n) (pure : forcedPure problem source = true) :
    algebra.le (valuation source) algebra.empty := by
  obtain ⟨target, upper, path⟩ := (forcedPure_exact problem source).mp pure
  exact algebra.trans (reaches_le algebra model path) (model (.pure target) upper)

def joinRows (algebra : Algebra Row) : List Row → Row
  | [] => algebra.empty
  | row :: rest => algebra.join row (joinRows algebra rest)

theorem joinRows_le_iff (algebra : Algebra Row) (rows : List Row) (upper : Row) :
    algebra.le (joinRows algebra rows) upper ↔ ∀ row ∈ rows, algebra.le row upper := by
  induction rows with
  | nil =>
      constructor
      · intro _ _ impossible
        cases impossible
      · intro _
        exact algebra.empty_le _
  | cons row rest ih =>
      simp only [joinRows, algebra.join_le_iff, ih, List.mem_cons, forall_eq_or_imp]

def expand (algebra : Algebra Row) (problem : FlatProblem n) (parameter : Valuation n Row) : Valuation n Row :=
  fun target => joinRows algebra ((contributors problem target).map parameter)

theorem expand_le_iff (algebra : Algebra Row) (problem : FlatProblem n) (parameter : Valuation n Row)
    (target : Fin n) (upper : Row) :
    algebra.le (expand algebra problem parameter target) upper ↔
      ∀ source, Reaches problem source target → forcedPure problem source = false →
        algebra.le (parameter source) upper := by
  simp only [expand, joinRows_le_iff, List.forall_mem_map, mem_contributors, and_imp]

theorem contribution_le (algebra : Algebra Row) (problem : FlatProblem n) (parameter : Valuation n Row)
    (source target : Fin n) (path : Reaches problem source target) (live : forcedPure problem source = false) :
    algebra.le (parameter source) (expand algebra problem parameter target) :=
  (expand_le_iff algebra problem parameter target _).mp (algebra.refl _) source path live

theorem expand_flow (algebra : Algebra Row) (problem : FlatProblem n) (parameter : Valuation n Row)
    (source target : Fin n) (member : .flow source target ∈ problem) :
    algebra.le (expand algebra problem parameter source) (expand algebra problem parameter target) := by
  apply (expand_le_iff algebra problem parameter source _).mpr
  intro start path live
  exact contribution_le algebra problem parameter start target
    (path.append (.cons ((mem_successors problem source target).mpr member) (.nil target))) live

theorem expand_pure (algebra : Algebra Row) (problem : FlatProblem n) (parameter : Valuation n Row)
    (source : Fin n) (member : .pure source ∈ problem) :
    algebra.le (expand algebra problem parameter source) algebra.empty := by
  apply (expand_le_iff algebra problem parameter source _).mpr
  intro start path live
  have pure := (forcedPure_exact problem start).mpr ⟨source, member, path⟩
  simp only [pure, Bool.true_eq_false] at live

/-- Every arbitrary free-parameter assignment gives a model. No bounds are
left for a caller to satisfy at instantiation. -/
theorem expand_models (algebra : Algebra Row) (problem : FlatProblem n) (parameter : Valuation n Row) :
    FlatModels algebra problem (expand algebra problem parameter) := by
  intro constraint member
  cases constraint with
  | flow source target => exact expand_flow algebra problem parameter source target member
  | pure source => exact expand_pure algebra problem parameter source member

/-- The original model itself is a parameter assignment recovering all of
its rows, including the rows of variables constrained to be pure. -/
theorem expand_equivalent (algebra : Algebra Row) {problem : FlatProblem n} {valuation : Valuation n Row}
    (model : FlatModels algebra problem valuation) :
    PointwiseEquivalent algebra (expand algebra problem valuation) valuation := by
  intro target
  constructor
  · apply (expand_le_iff algebra problem valuation target _).mpr
    intro source path _
    exact reaches_le algebra model path
  · by_cases pure : forcedPure problem target = true
    · exact algebra.trans (forcedPure_le_empty algebra model target pure) (algebra.empty_le _)
    · exact contribution_le algebra problem valuation target target (.nil target) (Bool.eq_false_iff.mpr pure)

/-! ## Finite schemes and their exact model families -/

abbrev Scheme (n : Nat) := Fin n → RowTerm (Fin n)

def joinTerms : List (RowTerm α) → RowTerm α
  | [] => .empty
  | term :: rest => .join term (joinTerms rest)

def coalesce (problem : FlatProblem n) : Scheme n :=
  fun target => joinTerms ((contributors problem target).map RowTerm.var)

def instantiate (algebra : Algebra Row) (scheme : Scheme n) (parameter : Valuation n Row) : Valuation n Row :=
  fun index => eval algebra parameter (scheme index)

theorem joinTerms_eval (algebra : Algebra Row) (parameter : α → Row) (terms : List (RowTerm α)) :
    eval algebra parameter (joinTerms terms) = joinRows algebra (terms.map (eval algebra parameter)) := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp only [joinTerms, eval, List.map, joinRows, ih]

theorem instantiate_coalesce (algebra : Algebra Row) (problem : FlatProblem n) (parameter : Valuation n Row) :
    instantiate algebra (coalesce problem) parameter = expand algebra problem parameter := by
  funext index
  simp only [instantiate, coalesce, joinTerms_eval, List.map_map, Function.comp_def, eval, expand]

/-- An unconstrained slot keeps its own arbitrary parameter. In particular,
using one slot in both rows of an identity function keeps their correlation. -/
theorem unconstrained_equivalent (algebra : Algebra Row) (parameter : Valuation n Row) :
    PointwiseEquivalent algebra (instantiate algebra (coalesce []) parameter) parameter := by
  rw [instantiate_coalesce]
  apply expand_equivalent algebra
  intro constraint impossible
  cases impossible

inductive Result (n : Nat) where
  | unsupported
  | solved (scheme : Scheme n)

/-- Unsupported right joins are distinguished from type errors. Supported
problems always have the constructed all-parameter solution family. -/
def solve (problem : Problem n) : Result n :=
  if supported problem then .solved (coalesce (flatten problem)) else .unsupported

theorem solve_unsupported_iff (problem : Problem n) :
    solve problem = .unsupported ↔ supported problem = false := by
  cases checked : supported problem <;> simp [solve, checked]

theorem solve_solved_iff (problem : Problem n) (scheme : Scheme n) :
    solve problem = .solved scheme ↔ scheme = coalesce (flatten problem) ∧ supported problem = true := by
  simp only [solve]
  split
  · rename_i checked
    constructor
    · intro same
      exact ⟨(Result.solved.inj same).symm, checked⟩
    · rintro ⟨rfl, _⟩
      rfl
  · rename_i unsupported
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨_, checked⟩
      exact False.elim (unsupported checked)

theorem solve_instantiates_model (algebra : Algebra Row) (problem : Problem n) (scheme : Scheme n)
    (solved : solve problem = .solved scheme) (parameter : Valuation n Row) :
    Models algebra problem (instantiate algebra scheme parameter) := by
  obtain ⟨rfl, checked⟩ := (solve_solved_iff problem scheme).mp solved
  rw [instantiate_coalesce]
  exact (flatten_models_iff algebra problem checked _).mp (expand_models algebra (flatten problem) parameter)

/-- Every model of the original row terms is represented, with no remaining
constraint predicate on the free parameters. -/
theorem solve_models_exact (algebra : Algebra Row) (problem : Problem n) (scheme : Scheme n)
    (solved : solve problem = .solved scheme) (valuation : Valuation n Row) :
    Models algebra problem valuation ↔
      ∃ parameter, PointwiseEquivalent algebra (instantiate algebra scheme parameter) valuation := by
  constructor
  · intro model
    obtain ⟨rfl, checked⟩ := (solve_solved_iff problem scheme).mp solved
    refine ⟨valuation, ?_⟩
    rw [instantiate_coalesce]
    exact expand_equivalent algebra ((flatten_models_iff algebra problem checked valuation).mpr model)
  · rintro ⟨parameter, equivalent⟩
    exact models_equivalent algebra problem _ valuation
      (solve_instantiates_model algebra problem scheme solved parameter) equivalent

/-- Exactness can be used in any output semantics respecting row equivalence.
It requires no positive-occurrence restriction on that output. -/
theorem solve_outputs_exact (algebra : Algebra Row) (problem : Problem n) (scheme : Scheme n)
    (solved : solve problem = .solved scheme) {Output : Type v}
    (leOutput : Output → Output → Prop)
    (outputTrans : ∀ {a b c}, leOutput a b → leOutput b c → leOutput a c)
    (output : Valuation n Row → Output)
    (respects : ∀ left right, PointwiseEquivalent algebra left right →
      leOutput (output left) (output right) ∧ leOutput (output right) (output left)) (expected : Output) :
    (∃ valuation, Models algebra problem valuation ∧ leOutput (output valuation) expected) ↔
      ∃ parameter, leOutput (output (instantiate algebra scheme parameter)) expected := by
  constructor
  · rintro ⟨valuation, model, below⟩
    obtain ⟨parameter, equivalent⟩ := (solve_models_exact algebra problem scheme solved valuation).mp model
    exact ⟨parameter, outputTrans (respects _ _ equivalent).1 below⟩
  · rintro ⟨parameter, below⟩
    exact ⟨instantiate algebra scheme parameter, solve_instantiates_model algebra problem scheme solved parameter, below⟩

theorem solve_rowTerm_instances_exact (algebra : Algebra Row) (problem : Problem n) (scheme : Scheme n)
    (solved : solve problem = .solved scheme) (term : RowTerm (Fin n)) (expected : Row) :
    (∃ valuation, Models algebra problem valuation ∧ algebra.le (eval algebra valuation term) expected) ↔
      ∃ parameter, algebra.le (eval algebra (instantiate algebra scheme parameter) term) expected :=
  solve_outputs_exact algebra problem scheme solved algebra.le algebra.trans
    (fun valuation => eval algebra valuation term) (fun left right equivalent => eval_equivalent algebra left right equivalent term) expected

/-- A function's input row is contravariant and its output row covariant.
Mutual inclusion preserves both directions, including shared input/output rows. -/
theorem arrow_rows_equivalent (algebra : Algebra Row) (left right : Valuation n Row)
    (equivalent : PointwiseEquivalent algebra left right)
    (input output : RowTerm (Fin n)) (domain codomain : StructuralBase.Ty Row) :
    StructuralBase.Subtype algebra.le
      (.arrow domain (eval algebra left input) codomain (eval algebra left output))
      (.arrow domain (eval algebra right input) codomain (eval algebra right output)) ∧
    StructuralBase.Subtype algebra.le
      (.arrow domain (eval algebra right input) codomain (eval algebra right output))
      (.arrow domain (eval algebra left input) codomain (eval algebra left output)) := by
  have inputs := eval_equivalent algebra left right equivalent input
  have outputs := eval_equivalent algebra left right equivalent output
  exact ⟨.arrow (.refl _) inputs.2 (.refl _) outputs.1,
    .arrow (.refl _) inputs.1 (.refl _) outputs.2⟩

theorem solve_arrow_instances_exact (algebra : Algebra Row) (problem : Problem n) (scheme : Scheme n)
    (solved : solve problem = .solved scheme) (input output : RowTerm (Fin n))
    (domain codomain expected : StructuralBase.Ty Row) :
    (∃ valuation, Models algebra problem valuation ∧ StructuralBase.Subtype algebra.le
      (.arrow domain (eval algebra valuation input) codomain (eval algebra valuation output)) expected) ↔
      ∃ parameter, StructuralBase.Subtype algebra.le
        (.arrow domain (eval algebra (instantiate algebra scheme parameter) input)
          codomain (eval algebra (instantiate algebra scheme parameter) output)) expected :=
  solve_outputs_exact algebra problem scheme solved (StructuralBase.Subtype algebra.le) StructuralBase.Subtype.trans
    (fun valuation => .arrow domain (eval algebra valuation input) codomain (eval algebra valuation output))
    (fun left right equivalent => arrow_rows_equivalent algebra left right equivalent input output domain codomain) expected

/-! ## Executed examples -/

namespace Examples

/-- A nontrivial row interpretation used only to execute the examples. -/
def boolAlgebra : Algebra Bool where
  empty := false
  join := Bool.or
  le left right := left = true → right = true
  refl _ := id
  trans first second := second ∘ first
  empty_le _ := by intro impossible; cases impossible
  join_le_iff left right upper := by cases left <;> cases right <;> cases upper <;> decide

def identityRows : Scheme 1 := coalesce []

/-- The unrestricted row parameter can be nonempty. Reusing slot zero in
the input and result yields the same nonempty row on both sides. -/
theorem identity_keeps_nonempty_row :
    instantiate boolAlgebra identityRows (fun _ => true) 0 = true := by decide +kernel

theorem identity_input_output_shared (parameter : Valuation 1 Bool) :
    (eval boolAlgebra (instantiate boolAlgebra identityRows parameter) (.var 0),
      eval boolAlgebra (instantiate boolAlgebra identityRows parameter) (.var 0)) =
      (parameter 0, parameter 0) := by
  have equivalent := unconstrained_equivalent boolAlgebra parameter 0
  change ((instantiate boolAlgebra identityRows parameter) 0,
    (instantiate boolAlgebra identityRows parameter) 0) = (parameter 0, parameter 0)
  have equal : instantiate boolAlgebra identityRows parameter 0 = parameter 0 := by
    cases actual : instantiate boolAlgebra identityRows parameter 0 <;> cases expected : parameter 0
    · rfl
    · exact False.elim (Bool.false_ne_true (actual.symm.trans (equivalent.2 expected)))
    · exact False.elim (Bool.false_ne_true (expected.symm.trans (equivalent.1 actual)))
    · rfl
  rw [equal]

/-- The cycle is forced pure, while the unrelated third row remains free. -/
def pureCycle : Problem 3 :=
  [(.var 0, .var 1), (.var 1, .var 0), (.var 1, .empty)]

theorem pure_cycle_propagates_without_defaulting_unrelated_row :
    ((List.finRange 3).map fun index =>
      instantiate boolAlgebra (coalesce (flatten pureCycle)) (fun _ => true) index) =
      [false, false, true] := by decide +kernel

/-- Both summands flow to the upper variable. Pure constraints remove only
the appropriate free parameter, not the other summand. -/
def joinedLower : Problem 3 :=
  [(.join (.var 0) (.var 1), .var 2), (.var 0, .empty)]

theorem joined_lower_propagates_live_summand :
    ((List.finRange 3).map fun index =>
      instantiate boolAlgebra (coalesce (flatten joinedLower)) (fun index => index == 1) index) =
      [false, true, true] := by decide +kernel

def rightJoin : Problem 1 := [(.var 0, .join (.var 0) .empty)]

theorem right_join_is_unsupported : solve rightJoin = .unsupported := rfl

theorem unsupported_does_not_mean_unsatisfiable :
    Models boolAlgebra rightJoin (fun _ => false) := empty_assignment_models boolAlgebra rightJoin

end Examples

end Yulang.RowFlowSchemes
