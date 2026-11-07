import Yulang.FiniteWorklist

/-!
# Eliminating finite positive systems without guardedness

An equation may mention any unknown at the same observation depth. For a
finite family of positive Boolean equations `F`, the construction first
iterates `x ↦ x ∨ F x` and then `x ↦ x ∧ F x`. Each phase takes the size of
a complete coordinates of unknowns, a finite-lattice capacity rather than an
observation-depth cutoff. The result is a positive formula in independent
parameters and atoms, with no recursive equations left to solve.

Every parameter assignment yields a fixed point, and every fixed point is
recovered by using itself as the parameter assignment. Atoms are arbitrary
propositions; in particular, they need not be decidable or finite. This
module concerns positive equations, not arbitrary producer subtyping.
-/

namespace Yulang.PositiveEquationElimination

variable {Index Atom : Type}

abbrev Valuation (Index : Type) := Index → Prop

def Below (left right : Valuation Index) : Prop :=
  ∀ index, left index → right index

def Monotone (step : Valuation Index → Valuation Index) : Prop :=
  ∀ left right, Below left right → Below (step left) (step right)

/-- The argument is a justified finite coordinate capacity, not search fuel. -/
def iterate {Value : Type} (step : Value → Value) : Nat → Value → Value
  | 0, value => value
  | capacity + 1, value => iterate step capacity (step value)

@[simp] theorem iterate_zero {Value : Type} (step : Value → Value) (value : Value) :
    iterate step 0 value = value := rfl

@[simp] theorem iterate_succ {Value : Type} (step : Value → Value)
    (capacity : Nat) (value : Value) :
    iterate step (capacity + 1) value = iterate step capacity (step value) := rfl

theorem iterate_fixed {Value : Type} (step : Value → Value) (value : Value)
    (fixed : step value = value) (capacity : Nat) :
    iterate step capacity value = value := by
  induction capacity with
  | zero => rfl
  | succ capacity ih => simpa only [iterate_succ, fixed] using ih

/-- An inflationary map on a finite family of propositions stabilizes within
one step per coordinate. Neither decidable propositions nor monotonicity of
the map are hypotheses. -/
theorem inflationary_stabilizes (coordinates : List Index)
    (complete : ∀ index, index ∈ coordinates)
    (step : Valuation Index → Valuation Index)
    (inflationary : ∀ value, Below value (step value))
    (initial : Valuation Index) :
    step (iterate step coordinates.length initial) =
      iterate step coordinates.length initial := by
  classical
  have enough : ∀ (capacity : Nat) (seen : List Index) (value : Valuation Index),
      seen.Nodup → (∀ index ∈ seen, value index) →
      coordinates.length ≤ seen.length + capacity →
      step (iterate step capacity value) = iterate step capacity value := by
    intro capacity
    induction capacity with
    | zero =>
        intro seen value distinct known bound
        funext index
        apply propext
        refine ⟨fun _ => known index ?_, inflationary value index⟩
        exact FiniteWorklist.saturated coordinates seen complete distinct (by simpa using bound) index
    | succ capacity ih =>
        intro seen value distinct known bound
        by_cases fixed : step value = value
        · rw [iterate_fixed step value fixed]
          exact fixed
        · have fresh : ∃ index, step value index ∧ ¬ value index := by
            apply Classical.byContradiction
            intro absent
            apply fixed
            funext index
            apply propext
            exact ⟨fun next => Classical.byContradiction fun previous =>
              absent ⟨index, next, previous⟩, inflationary value index⟩
          obtain ⟨index, next, previous⟩ := fresh
          have missing : index ∉ seen := fun present => previous (known index present)
          apply ih (index :: seen) (step value) (List.nodup_cons.mpr ⟨missing, distinct⟩)
          · intro candidate present
            rcases List.mem_cons.mp present with rfl | earlier
            · exact next
            · exact inflationary value candidate (known candidate earlier)
          · simp only [List.length_cons]
            omega
  exact enough coordinates.length [] initial (by simp) (by simp) (by simp)

/-- The dual finite-height argument for a deflationary map. -/
theorem deflationary_stabilizes (coordinates : List Index)
    (complete : ∀ index, index ∈ coordinates)
    (step : Valuation Index → Valuation Index)
    (deflationary : ∀ value, Below (step value) value)
    (initial : Valuation Index) :
    step (iterate step coordinates.length initial) =
      iterate step coordinates.length initial := by
  classical
  have enough : ∀ (capacity : Nat) (seen : List Index) (value : Valuation Index),
      seen.Nodup → (∀ index ∈ seen, ¬ value index) →
      coordinates.length ≤ seen.length + capacity →
      step (iterate step capacity value) = iterate step capacity value := by
    intro capacity
    induction capacity with
    | zero =>
        intro seen value distinct known bound
        funext index
        apply propext
        refine ⟨deflationary value index, fun current => False.elim (known index ?_ current)⟩
        exact FiniteWorklist.saturated coordinates seen complete distinct (by simpa using bound) index
    | succ capacity ih =>
        intro seen value distinct known bound
        by_cases fixed : step value = value
        · rw [iterate_fixed step value fixed]
          exact fixed
        · have fresh : ∃ index, value index ∧ ¬ step value index := by
            apply Classical.byContradiction
            intro absent
            apply fixed
            funext index
            apply propext
            exact ⟨deflationary value index, fun previous => Classical.byContradiction fun next =>
              absent ⟨index, previous, next⟩⟩
          obtain ⟨index, previous, next⟩ := fresh
          have missing : index ∉ seen := fun present => known index present previous
          apply ih (index :: seen) (step value) (List.nodup_cons.mpr ⟨missing, distinct⟩)
          · intro candidate present
            rcases List.mem_cons.mp present with rfl | earlier
            · exact next
            · exact fun current => known candidate earlier (deflationary value candidate current)
          · simp only [List.length_cons]
            omega
  exact enough coordinates.length [] initial (by simp) (by simp) (by simp)

def ascend (step : Valuation Index → Valuation Index) (value : Valuation Index) :
    Valuation Index := fun index => value index ∨ step value index

def descend (step : Valuation Index → Valuation Index) (value : Valuation Index) :
    Valuation Index := fun index => value index ∧ step value index

/-- A total retraction onto all fixed points of a finite monotone system. -/
def project (coordinates : List Index) (step : Valuation Index → Valuation Index)
    (parameter : Valuation Index) : Valuation Index :=
  iterate (descend step) coordinates.length
    (iterate (ascend step) coordinates.length parameter)

theorem descend_prefixpoint (step : Valuation Index → Valuation Index)
    (monotone : Monotone step) (value : Valuation Index)
    (prefixpoint : Below (step value) value) :
    Below (step (descend step value)) (descend step value) := by
  have smaller := monotone (descend step value) value (fun _ present => present.1)
  intro index present
  exact ⟨prefixpoint index (smaller index present), smaller index present⟩

theorem descend_iterate_prefixpoint (step : Valuation Index → Valuation Index)
    (monotone : Monotone step) (capacity : Nat) (value : Valuation Index)
    (prefixpoint : Below (step value) value) :
    Below (step (iterate (descend step) capacity value))
      (iterate (descend step) capacity value) := by
  induction capacity generalizing value with
  | zero => exact prefixpoint
  | succ capacity ih =>
      exact ih (descend step value) (descend_prefixpoint step monotone value prefixpoint)

theorem project_sound (coordinates : List Index) (complete : ∀ index, index ∈ coordinates)
    (step : Valuation Index → Valuation Index) (monotone : Monotone step)
    (parameter : Valuation Index) :
    step (project coordinates step parameter) = project coordinates step parameter := by
  have up := inflationary_stabilizes coordinates complete (ascend step)
    (fun _ _ present => Or.inl present) parameter
  let ceiling := iterate (ascend step) coordinates.length parameter
  have prefixpoint : Below (step ceiling) ceiling := by
    intro index present
    have known : ascend step ceiling index := Or.inr present
    rw [up] at known
    exact known
  have down := deflationary_stabilizes coordinates complete (descend step)
    (fun _ _ present => present.1) ceiling
  have retained := descend_iterate_prefixpoint step monotone coordinates.length ceiling prefixpoint
  funext index
  apply propext
  refine ⟨retained index, ?_⟩
  intro present
  have both : descend step (project coordinates step parameter) index := by
    change descend step (iterate (descend step) coordinates.length ceiling) index
    rw [down]
    exact present
  exact both.2

theorem project_retract (coordinates : List Index)
    (step : Valuation Index → Valuation Index) (solution : Valuation Index)
    (fixed : step solution = solution) : project coordinates step solution = solution := by
  have up : ascend step solution = solution := by
    funext index
    simp [ascend, fixed]
  have down : descend step solution = solution := by
    funext index
    simp [descend, fixed]
  unfold project
  rw [iterate_fixed _ _ up, iterate_fixed _ _ down]

inductive Formula (Index Atom : Type) where
  | var : Index → Formula Index Atom
  | atom : Atom → Formula Index Atom
  | bottom : Formula Index Atom
  | top : Formula Index Atom
  | union : Formula Index Atom → Formula Index Atom → Formula Index Atom
  | inter : Formula Index Atom → Formula Index Atom → Formula Index Atom
  deriving DecidableEq

namespace Formula

def eval (atoms : Valuation Atom) (variables : Valuation Index) : Formula Index Atom → Prop
  | .var index => variables index
  | .atom symbol => atoms symbol
  | .bottom => False
  | .top => True
  | .union left right => eval atoms variables left ∨ eval atoms variables right
  | .inter left right => eval atoms variables left ∧ eval atoms variables right

/-- Substitution removes equation references; remaining variables are free
parameters of the resulting finite formula. -/
def bind {Target : Type} (variables : Index → Formula Target Atom) :
    Formula Index Atom → Formula Target Atom
  | .var index => variables index
  | .atom symbol => .atom symbol
  | .bottom => .bottom
  | .top => .top
  | .union left right => .union (bind variables left) (bind variables right)
  | .inter left right => .inter (bind variables left) (bind variables right)

theorem eval_bind {Target : Type} (formula : Formula Index Atom)
    (variables : Index → Formula Target Atom)
    (atoms : Valuation Atom) (parameters : Valuation Target) :
    eval atoms parameters (formula.bind variables) =
      eval atoms (fun index => eval atoms parameters (variables index)) formula := by
  induction formula with
  | var | atom | bottom | top => rfl
  | union _ _ ihLeft ihRight => simp only [bind, eval, ihLeft, ihRight]
  | inter _ _ ihLeft ihRight => simp only [bind, eval, ihLeft, ihRight]

theorem eval_monotone (formula : Formula Index Atom) (atoms : Valuation Atom)
    (left right : Valuation Index) (below : Below left right) :
    eval atoms left formula → eval atoms right formula := by
  induction formula with
  | var index => exact below index
  | atom | bottom | top => exact id
  | union _ _ ihLeft ihRight => exact Or.imp ihLeft ihRight
  | inter _ _ ihLeft ihRight => exact And.imp ihLeft ihRight

end Formula

abbrev System (Index Atom : Type) := Index → Formula Index Atom

def evaluate (system : System Index Atom) (atoms : Valuation Atom)
    (variables : Valuation Index) : Valuation Index :=
  fun index => (system index).eval atoms variables

theorem evaluate_monotone (system : System Index Atom) (atoms : Valuation Atom) :
    Monotone (evaluate system atoms) :=
  fun left right below index => (system index).eval_monotone atoms left right below

def ascendFormula (system : System Index Atom) (value : System Index Atom) :
    System Index Atom :=
  fun index => .union (value index) ((system index).bind value)

def descendFormula (system : System Index Atom) (value : System Index Atom) :
    System Index Atom :=
  fun index => .inter (value index) ((system index).bind value)

/-- An executable finite expression for every solution. There are exactly
`2 * coordinates.length` parallel substitution rounds. -/
def solve (coordinates : List Index) (system : System Index Atom) : System Index Atom :=
  iterate (descendFormula system) coordinates.length
    (iterate (ascendFormula system) coordinates.length Formula.var)

theorem evaluate_ascend (system value : System Index Atom) (atoms : Valuation Atom)
    (parameters : Valuation Index) :
    evaluate (ascendFormula system value) atoms parameters =
      ascend (evaluate system atoms) (evaluate value atoms parameters) := by
  funext index
  simp only [evaluate, ascendFormula, ascend, Formula.eval, Formula.eval_bind]
  rfl

theorem evaluate_descend (system value : System Index Atom) (atoms : Valuation Atom)
    (parameters : Valuation Index) :
    evaluate (descendFormula system value) atoms parameters =
      descend (evaluate system atoms) (evaluate value atoms parameters) := by
  funext index
  simp only [evaluate, descendFormula, descend, Formula.eval, Formula.eval_bind]
  rfl

theorem iterate_commute {Left Right : Type} (leftStep : Left → Left)
    (rightStep : Right → Right) (map : Left → Right)
    (commute : ∀ value, map (leftStep value) = rightStep (map value))
    (capacity : Nat) (value : Left) :
    map (iterate leftStep capacity value) = iterate rightStep capacity (map value) := by
  induction capacity generalizing value with
  | zero => rfl
  | succ capacity ih => rw [iterate_succ, ih, commute, iterate_succ]

/-- Reindexing need not be injective. This is the naturality required when
adding a mask merges several finite `(node, hidden-labels)` states. -/
def pullback (indexMap : Index → Index) (value : Valuation Index) : Valuation Index :=
  fun index => value (indexMap index)

theorem project_natural (coordinates : List Index) (indexMap : Index → Index)
    (leftStep rightStep : Valuation Index → Valuation Index)
    (commute : ∀ value, pullback indexMap (leftStep value) =
      rightStep (pullback indexMap value)) (parameters : Valuation Index) :
    pullback indexMap (project coordinates leftStep parameters) =
      project coordinates rightStep (pullback indexMap parameters) := by
  have up : ∀ value, pullback indexMap (ascend leftStep value) =
      ascend rightStep (pullback indexMap value) := by
    intro value
    funext index
    change (value (indexMap index) ∨ leftStep value (indexMap index)) = _
    change _ = (value (indexMap index) ∨ rightStep (pullback indexMap value) index)
    rw [← congrFun (commute value) index]
    rfl
  have down : ∀ value, pullback indexMap (descend leftStep value) =
      descend rightStep (pullback indexMap value) := by
    intro value
    funext index
    change (value (indexMap index) ∧ leftStep value (indexMap index)) = _
    change _ = (value (indexMap index) ∧ rightStep (pullback indexMap value) index)
    rw [← congrFun (commute value) index]
    rfl
  unfold project
  rw [iterate_commute (descend leftStep) (descend rightStep)
    (pullback indexMap) down]
  rw [iterate_commute (ascend leftStep) (ascend rightStep)
    (pullback indexMap) up]

theorem evaluate_solve (coordinates : List Index) (system : System Index Atom)
    (atoms : Valuation Atom) (parameters : Valuation Index) :
    evaluate (solve coordinates system) atoms parameters =
      project coordinates (evaluate system atoms) parameters := by
  unfold solve project
  rw [iterate_commute (descendFormula system) (descend (evaluate system atoms))
    (fun value => evaluate value atoms parameters)
    (fun value => evaluate_descend system value atoms parameters)]
  rw [iterate_commute (ascendFormula system) (ascend (evaluate system atoms))
    (fun value => evaluate value atoms parameters)
    (fun value => evaluate_ascend system value atoms parameters)]
  rfl

/-- For every finite positive system and every assignment to its arbitrary
atoms and free parameters, the constructed expressions satisfy all equations. -/
theorem solve_sound (coordinates : List Index) (complete : ∀ index, index ∈ coordinates)
    (system : System Index Atom) (atoms : Valuation Atom) (parameters : Valuation Index) :
    evaluate system atoms (evaluate (solve coordinates system) atoms parameters) =
      evaluate (solve coordinates system) atoms parameters := by
  rw [evaluate_solve]
  exact project_sound coordinates complete (evaluate system atoms)
    (evaluate_monotone system atoms) parameters

/-- Every independently given solution is recovered by the explicit choice
of that same assignment as the free parameters. -/
theorem solve_retract (coordinates : List Index) (system : System Index Atom)
    (atoms : Valuation Atom) (solution : Valuation Index)
    (fixed : evaluate system atoms solution = solution) :
    evaluate (solve coordinates system) atoms solution = solution := by
  rw [evaluate_solve]
  exact project_retract coordinates (evaluate system atoms) solution fixed

/-- Exact solved instances, with no success, solution-existence or fuel
hypothesis: finite positive systems always admit this complete scheme. -/
theorem solved_instances_exact (coordinates : List Index)
    (complete : ∀ index, index ∈ coordinates) (system : System Index Atom)
    (atoms : Valuation Atom) (value : Valuation Index) :
    evaluate system atoms value = value ↔
      ∃ parameters, evaluate (solve coordinates system) atoms parameters = value := by
  constructor
  · intro fixed
    exact ⟨value, solve_retract coordinates system atoms value fixed⟩
  · rintro ⟨parameters, rfl⟩
    exact solve_sound coordinates complete system atoms parameters

end Yulang.PositiveEquationElimination
