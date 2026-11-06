import Yulang.TypeSimplificationCheckCost

/-!
# Syntax-work bounds for the actual four-stage simplification pass

Each function computes a result and an operation count. The value projections
are the existing `TypeSimplification` operations; no successful-certificate or
supported-input premise is needed by the final bound. The eager certificate
interpreter from `TypeSimplificationCheckCost` supplies a conservative cost.
Value/row substitutions visit the actual syntax, and occurrence checks are
charged again at every substitution lookup, as in the simple reference pass.

The units count constructor visits, atom comparisons, Boolean dispatch and
candidate processing. Identifier bit cost and allocator implementation costs
are outside the model. The finite parameter inventory `List.finRange n` is
the input table; copying that table and constructing/concatenating candidate
lists are charged below. Its library-internal materialization is not charged.
This is not a measured Rust runtime claim.
-/

namespace Yulang.TypeSimplificationCost

open Inference TypeSimplification
open InferenceSubstitutionCost (tyNodes rowNodes)
open TypeSimplificationCheckCost (symbolicCount symbolicCount_value
  symbolicCount_size_bound checkBudget spineCount spineCount_value spineCount_bound nodes_le_total)

def occursCount (positive : Bool) (index : Fin n) : TyTerm (Fin n) → Bool × Nat
  | .var actual => (positive && decide (index = actual), 1)
  | .base _ | .bottom | .top | .emptyRecord => (false, 1)
  | .union a b | .inter a b | .pair a b | .record _ a b =>
      let first := occursCount positive index a
      let last := occursCount positive index b
      (first.1 || last.1, 1 + first.2 + last.2)
  | .variant _ payload =>
      let value := occursCount positive index payload
      (value.1, 1 + value.2)
  | .arrow input _ output _ =>
      let first := occursCount (!positive) index input
      let last := occursCount positive index output
      (first.1 || last.1, 1 + first.2 + last.2)

theorem occursCount_value (positive : Bool) (index : Fin n) (term : TyTerm (Fin n)) :
    (occursCount positive index term).1 = occurs positive index term := by
  induction term generalizing positive <;> cases positive <;> simp_all [occursCount, occurs]

theorem occursCount_steps (positive : Bool) (index : Fin n) (term : TyTerm (Fin n)) :
    (occursCount positive index term).2 = nodes term := by
  induction term generalizing positive <;> cases positive <;> simp_all [occursCount, nodes]

def supportedCount : TyTerm (Fin n) → Bool × Nat
  | .var _ | .base _ | .bottom | .top | .emptyRecord => (true, 1)
  | .union a b | .inter a b | .pair a b =>
      let first := supportedCount a
      let last := supportedCount b
      (first.1 && last.1, 1 + first.2 + last.2)
  | .record _ value rest =>
      let shape := spineCount rest
      let first := supportedCount value
      let last := supportedCount rest
      (shape.1 && first.1 && last.1, 1 + shape.2 + first.2 + last.2)
  | .variant _ payload =>
      let value := supportedCount payload
      (value.1, 1 + value.2)
  | .arrow input _ output _ =>
      let first := supportedCount input
      let last := supportedCount output
      (first.1 && last.1, 1 + first.2 + last.2)

theorem supportedCount_value (term : TyTerm (Fin n)) :
    (supportedCount term).1 = supported term := by
  induction term <;> simp_all [supportedCount, supported, spineCount_value]

theorem supportedCount_bound (term : TyTerm (Fin n)) (size : Nat)
    (fits : tyNodes term ≤ size) :
    (supportedCount term).2 ≤ tyNodes term * (size + 1) := by
  induction term with
  | var | base | bottom | top | emptyRecord => simp [supportedCount, tyNodes]
  | union a b iha ihb | inter a b iha ihb | pair a b iha ihb =>
      simp only [tyNodes] at fits
      have first := iha (by omega)
      have last := ihb (by omega)
      simp only [supportedCount, tyNodes, Nat.add_mul, Nat.one_mul]
      omega
  | variant label payload ih =>
      simp only [tyNodes] at fits
      have value := ih (by omega)
      simp only [supportedCount, tyNodes, Nat.add_mul, Nat.one_mul]
      omega
  | record label value rest ihv ihr =>
      simp only [tyNodes] at fits
      have shape := spineCount_bound rest
      have first := ihv (by omega)
      have last := ihr (by omega)
      simp only [supportedCount, tyNodes, Nat.add_mul, Nat.one_mul]
      omega
  | arrow input inputRow output outputRow ihi iho =>
      simp only [tyNodes] at fits
      have first := ihi (by omega)
      have last := iho (by omega)
      simp only [supportedCount, tyNodes, Nat.add_mul, Nat.one_mul]
      omega

def replacementCount (term : TyTerm (Fin n)) (index : Fin n) : TyTerm (Fin n) × Nat :=
  let negative := occursCount false index term
  if negative.1 then
    let positive := occursCount true index term
    (if positive.1 then .var index else .top, 1 + negative.2 + positive.2)
  else (.bottom, 1 + negative.2)

theorem replacementCount_value (term : TyTerm (Fin n)) (index : Fin n) :
    (replacementCount term index).1 = replacement term index := by
  simp only [replacementCount, occursCount_value, replacement]
  split <;> rfl

theorem replacementCount_bound (term : TyTerm (Fin n)) (index : Fin n) :
    (replacementCount term index).2 ≤ 1 + 2 * tyNodes term := by
  have smaller := nodes_le_total term
  simp only [replacementCount, occursCount_steps]
  split <;> omega

def valuesCount (term : TyTerm (Fin n))
    (replacement : Fin n → TyTerm (Fin n) × Nat) : TyTerm (Fin n) × Nat :=
  InferenceSubstitutionCost.tySubst
    (fun index => (⟨(replacement index).1, .var index⟩, (replacement index).2)) term

theorem valuesCount_value (term : TyTerm (Fin n))
    (replacement : Fin n → TyTerm (Fin n) × Nat) :
    (valuesCount term replacement).1 = substituteValues term (fun index => (replacement index).1) := by
  exact InferenceSubstitutionCost.tySubst_value _ _

theorem valuesCount_bound (term : TyTerm (Fin n))
    (replacement : Fin n → TyTerm (Fin n) × Nat) (cost : Nat)
    (bounded : ∀ index, (replacement index).2 ≤ cost) :
    (valuesCount term replacement).2 ≤ tyNodes term * (cost + 1) :=
  InferenceSubstitutionCost.tySubst_bound _ cost bounded term

def simplifyCount (term : TyTerm (Fin n)) : TyTerm (Fin n) × Nat :=
  valuesCount term (replacementCount term)

theorem simplifyCount_value (term : TyTerm (Fin n)) :
    (simplifyCount term).1 = simplify term := by
  simp only [simplifyCount, valuesCount_value, replacementCount_value, substituteValues, simplify]

theorem simplifyCount_bound (term : TyTerm (Fin n)) (size : Nat) (fits : tyNodes term ≤ size) :
    (simplifyCount term).2 ≤ size * (2 + 2 * size) := by
  have bounded := valuesCount_bound term (replacementCount term) (1 + 2 * size)
    (fun index => Nat.le_trans (replacementCount_bound term index) (by omega))
  exact Nat.le_trans bounded (Nat.mul_le_mul fits (by omega))

def simplifySafeCount (term : TyTerm (Fin n)) : TyTerm (Fin n) × Nat :=
  let shape := supportedCount term
  if shape.1 then
    let value := simplifyCount term
    (value.1, 1 + shape.2 + value.2)
  else (term, 1 + shape.2)

theorem simplifySafeCount_value (term : TyTerm (Fin n)) :
    (simplifySafeCount term).1 = simplifySafe term := by
  simp only [simplifySafeCount, supportedCount_value, simplifySafe]
  split <;> simp only [simplifyCount_value]

def varianceBudget (size : Nat) : Nat :=
  1 + size * (size + 1) + size * (2 + 2 * size)

theorem simplifySafeCount_bound (term : TyTerm (Fin n)) (size : Nat) (fits : tyNodes term ≤ size) :
    (simplifySafeCount term).2 ≤ varianceBudget size := by
  have shape := Nat.le_trans (supportedCount_bound term size fits)
    (Nat.mul_le_mul_right (size + 1) fits)
  have value := simplifyCount_bound term size fits
  simp only [simplifySafeCount, varianceBudget]
  split <;> omega

/-- The certificate and accepted replacement share the computed candidate.
The value theorem below justifies this local reuse; both polarity occurrence
tests and the certificate are still evaluated in this eager reference pass. -/
def applySandwichCount (index : Fin n) (fixed term : TyTerm (Fin n)) : TyTerm (Fin n) × Nat :=
  let positive := occursCount true index fixed
  let negative := occursCount false index fixed
  let candidate := valuesCount term (fun i => (if i = index then fixed else .var i, 1))
  let checked := symbolicCount candidate.1 term
  (if !positive.1 && !negative.1 && checked.1 then candidate.1 else term,
    5 + positive.2 + negative.2 + candidate.2 + checked.2)

theorem applySandwichCount_value (index : Fin n) (fixed term : TyTerm (Fin n)) :
    (applySandwichCount index fixed term).1 = applySandwich index fixed term := by
  simp only [applySandwichCount, occursCount_value, symbolicCount_value, valuesCount_value,
    applySandwich, sandwichCheck, sandwich]
  rfl

def sandwichBudget (size : Nat) : Nat := 7 + 2 * size + checkBudget (2 * size)

theorem applySandwichCount_bound (index : Fin n) (fixed term : TyTerm (Fin n)) (size : Nat)
    (fixedSmall : tyNodes fixed ≤ 1) (fits : tyNodes term ≤ size) :
    (applySandwichCount index fixed term).2 ≤ sandwichBudget size := by
  have fixedNodes := nodes_le_total fixed
  have substitution := valuesCount_bound term
    (fun i => (if i = index then fixed else .var i, 1)) 1 (fun _ => Nat.le_refl _)
  have substitutionBound : (valuesCount term
      (fun i => (if i = index then fixed else .var i, 1))).2 ≤ 2 * size := by
    have upper := Nat.mul_le_mul_right 2 fits
    simp only [Nat.mul_comm] at upper
    omega
  have candidateSize := (TypeSimplificationSize.sandwich_sizes index fixed term
    (by omega) fixedSmall).2
  have comparison := symbolicCount_size_bound
    (valuesCount term (fun i => (if i = index then fixed else .var i, 1))).1 term (2 * size) (by
      simp only [valuesCount_value]
      change tyNodes (sandwich index fixed term) + tyNodes term ≤ 2 * size
      omega)
  simp only [applySandwichCount, sandwichBudget, occursCount_steps]
  omega

def mergeCheckCount (positive : Bool) (first second : Fin n) (term : TyTerm (Fin n)) : Bool × Nat :=
  let candidate := valuesCount term (fun index => (jointReplacement positive first second index, 3))
  let checked := symbolicCount candidate.1 term
  (checked.1, 1 + candidate.2 + checked.2)

theorem mergeCheckCount_value (positive : Bool) (first second : Fin n) (term : TyTerm (Fin n)) :
    (mergeCheckCount positive first second term).1 = mergeCheck positive first second term := by
  simp only [mergeCheckCount, symbolicCount_value, valuesCount_value, mergeCheck]

theorem mergeCheckCount_bound (positive : Bool) (first second : Fin n)
    (term : TyTerm (Fin n)) (size : Nat) (fits : tyNodes term ≤ size) :
    (mergeCheckCount positive first second term).2 ≤ 1 + 4 * size + checkBudget (4 * size) := by
  have substitution := valuesCount_bound term
    (fun index => (jointReplacement positive first second index, 3)) 3 (fun _ => Nat.le_refl _)
  have substitutionBound : (valuesCount term
      (fun index => (jointReplacement positive first second index, 3))).2 ≤ 4 * size := by
    have upper := Nat.mul_le_mul_right 4 fits
    simp only [Nat.mul_comm] at upper
    omega
  have candidateSize := (TypeSimplificationSize.jointSubstitution_sizes positive first second term).2
  have comparison := symbolicCount_size_bound
    (valuesCount term (fun index => (jointReplacement positive first second index, 3))).1 term
    (4 * size) (by
      simp only [valuesCount_value]
      change tyNodes (substituteValues term (jointReplacement positive first second)) + tyNodes term ≤ 4 * size
      omega)
  simp only [mergeCheckCount]
  omega

def applyMergeCount (first second : Fin n) (term : TyTerm (Fin n)) : TyTerm (Fin n) × Nat :=
  let positive := mergeCheckCount true first second term
  let negative := mergeCheckCount false first second term
  let merged := valuesCount term (fun index => (if index = first then .var second else .var index, 1))
  (if positive.1 || negative.1 then merged.1 else term, 1 + positive.2 + negative.2 + merged.2)

theorem applyMergeCount_value (first second : Fin n) (term : TyTerm (Fin n)) :
    (applyMergeCount first second term).1 = applyMerge first second term := by
  simp only [applyMergeCount, mergeCheckCount_value, valuesCount_value, applyMerge, mergeChecked, merge]
  split <;> rfl

def mergeBudget (size : Nat) : Nat := 3 + 10 * size + 2 * checkBudget (4 * size)

theorem applyMergeCount_bound (first second : Fin n) (term : TyTerm (Fin n)) (size : Nat)
    (fits : tyNodes term ≤ size) :
    (applyMergeCount first second term).2 ≤ mergeBudget size := by
  have positive := mergeCheckCount_bound true first second term size fits
  have negative := mergeCheckCount_bound false first second term size fits
  have substitution := valuesCount_bound term
    (fun index => (if index = first then .var second else .var index, 1)) 1 (fun _ => Nat.le_refl _)
  have upper := Nat.mul_le_mul_right 2 fits
  simp only [Nat.mul_comm] at upper
  simp only [applyMergeCount, mergeBudget]
  omega

def mergeCandidatesCount : List (Fin n × Fin n) → TyTerm (Fin n) → TyTerm (Fin n) × Nat
  | [], term => (term, 0)
  | (first, second) :: rest, term =>
      let candidate := applyMergeCount first second term
      let tail := mergeCandidatesCount rest candidate.1
      (tail.1, 1 + candidate.2 + tail.2)

theorem mergeCandidatesCount_value (candidates : List (Fin n × Fin n)) (term : TyTerm (Fin n)) :
    (mergeCandidatesCount candidates term).1 = mergeCandidates candidates term := by
  induction candidates generalizing term with
  | nil => rfl
  | cons pair rest ih =>
      cases pair
      simp only [mergeCandidatesCount, mergeCandidates, ih, applyMergeCount_value]

theorem mergeCandidatesCount_bound (candidates : List (Fin n × Fin n)) (term : TyTerm (Fin n))
    (size : Nat) (fits : tyNodes term ≤ size) :
    (mergeCandidatesCount candidates term).2 ≤ candidates.length * (mergeBudget size + 1) := by
  induction candidates generalizing term with
  | nil => simp [mergeCandidatesCount]
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      have candidate := applyMergeCount_bound first second term size fits
      have candidateSize : tyNodes (applyMergeCount first second term).1 ≤ size := by
        rw [applyMergeCount_value]
        exact Nat.le_trans (TypeSimplificationSize.applyMerge_sizes first second term).2 fits
      have tail := ih (applyMergeCount first second term).1 candidateSize
      simp only [mergeCandidatesCount, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

def sandwichCandidatesCount : List (Fin n × TyTerm (Fin n)) → TyTerm (Fin n) → TyTerm (Fin n) × Nat
  | [], term => (term, 0)
  | (index, fixed) :: rest, term =>
      let candidate := applySandwichCount index fixed term
      let tail := sandwichCandidatesCount rest candidate.1
      (tail.1, 1 + candidate.2 + tail.2)

theorem sandwichCandidatesCount_value (candidates : List (Fin n × TyTerm (Fin n)))
    (term : TyTerm (Fin n)) :
    (sandwichCandidatesCount candidates term).1 = sandwichCandidates candidates term := by
  induction candidates generalizing term with
  | nil => rfl
  | cons pair rest ih =>
      cases pair
      simp only [sandwichCandidatesCount, sandwichCandidates, ih, applySandwichCount_value]

theorem sandwichCandidatesCount_bound (candidates : List (Fin n × TyTerm (Fin n)))
    (small : ∀ pair ∈ candidates, tyNodes pair.2 ≤ 1) (term : TyTerm (Fin n))
    (size : Nat) (fits : tyNodes term ≤ size) :
    (sandwichCandidatesCount candidates term).2 ≤ candidates.length * (sandwichBudget size + 1) := by
  induction candidates generalizing term with
  | nil => simp [sandwichCandidatesCount]
  | cons pair rest ih =>
      rcases pair with ⟨index, fixed⟩
      have fixedSize := small (index, fixed) List.mem_cons_self
      have candidate := applySandwichCount_bound index fixed term size fixedSize fits
      have candidateSize : tyNodes (applySandwichCount index fixed term).1 ≤ size := by
        rw [applySandwichCount_value]
        exact Nat.le_trans (TypeSimplificationSize.applySandwich_sizes index fixed term
          (Nat.le_trans (nodes_le_total fixed) fixedSize) fixedSize).2 fits
      have tail := ih (fun pair member => small pair (List.mem_cons_of_mem _ member))
        (applySandwichCount index fixed term).1 candidateSize
      simp only [sandwichCandidatesCount, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-! Candidate discovery traverses the finite parameter table and explicitly
builds its products. Appending a produced row is charged by its actual spine
length. Thus the candidate-count factor is connected to real enumeration. -/

def mapCount (map : α → β) : List α → List β × Nat
  | [] => ([], 0)
  | first :: rest =>
      let tail := mapCount map rest
      (map first :: tail.1, 1 + tail.2)

theorem mapCount_value (map : α → β) (entries : List α) :
    (mapCount map entries).1 = entries.map map := by
  induction entries <;> simp_all [mapCount]

theorem mapCount_steps (map : α → β) (entries : List α) :
    (mapCount map entries).2 = entries.length := by
  induction entries <;> simp_all [mapCount, Nat.add_comm]

def appendCount : List α → List α → List α × Nat
  | [], last => (last, 0)
  | first :: rest, last =>
      let tail := appendCount rest last
      (first :: tail.1, 1 + tail.2)

theorem appendCount_value (first last : List α) :
    (appendCount first last).1 = first ++ last := by
  induction first <;> simp_all [appendCount]

theorem appendCount_steps (first last : List α) :
    (appendCount first last).2 = first.length := by
  induction first <;> simp_all [appendCount, Nat.add_comm]

def productCount : List α → List β → List (α × β) × Nat
  | [], _ => ([], 0)
  | first :: rest, last =>
      let row := mapCount (first, ·) last
      let tail := productCount rest last
      let joined := appendCount row.1 tail.1
      (joined.1, 1 + row.2 + tail.2 + joined.2)

theorem productCount_value (first : List α) (last : List β) :
    (productCount first last).1 = first.flatMap (fun entry => last.map (entry, ·)) := by
  induction first <;> simp_all [productCount, appendCount_value, mapCount_value]

theorem productCount_steps (first : List α) (last : List β) :
    (productCount first last).2 = first.length * (1 + 2 * last.length) := by
  induction first with
  | nil => simp [productCount]
  | cons entry rest ih =>
      simp only [productCount, mapCount_steps, appendCount_steps, mapCount_value,
        List.length_map, List.length_cons, Nat.add_mul, Nat.one_mul, ih]
      omega

def mergeAllCount (term : TyTerm (Fin n)) : TyTerm (Fin n) × Nat :=
  let indices := mapCount id (List.finRange n)
  let candidates := productCount indices.1 indices.1
  let result := mergeCandidatesCount candidates.1 term
  (result.1, indices.2 + candidates.2 + result.2)

theorem mergeAllCount_value (term : TyTerm (Fin n)) :
    (mergeAllCount term).1 = mergeAll term := by
  simp only [mergeAllCount, mergeCandidatesCount_value, productCount_value, mapCount_value, List.map_id, mergeAll]

def mergeAllBudget (parameters size : Nat) : Nat :=
  parameters + parameters * (1 + 2 * parameters) +
    parameters * parameters * (mergeBudget size + 1)

theorem mergeAllCount_bound (term : TyTerm (Fin n)) (size : Nat) (fits : tyNodes term ≤ size) :
    (mergeAllCount term).2 ≤ mergeAllBudget n size := by
  have processed := mergeCandidatesCount_bound
    (productCount (mapCount id (List.finRange n)).1 (mapCount id (List.finRange n)).1).1 term size fits
  simp only [productCount_value, mapCount_value, List.map_id,
    TypeSimplificationSize.merge_candidate_count] at processed
  simp only [mergeAllCount, mapCount_steps, productCount_steps, mapCount_value, List.map_id,
    List.length_finRange, mergeAllBudget, productCount_value]
  exact Nat.add_le_add_left processed _

def sandwichAllCount (term : TyTerm (Fin n)) : TyTerm (Fin n) × Nat :=
  let indices := mapCount id (List.finRange n)
  let fixed := mapCount (TyTerm.base : Base → TyTerm (Fin n)) [.int, .str, .bool, .unit]
  let candidates := productCount indices.1 fixed.1
  let result := sandwichCandidatesCount candidates.1 term
  (result.1, indices.2 + fixed.2 + candidates.2 + result.2)

theorem sandwichAllCount_value (term : TyTerm (Fin n)) :
    (sandwichAllCount term).1 = sandwichAll term := by
  simp only [sandwichAllCount, sandwichCandidatesCount_value, productCount_value,
    mapCount_value, List.map_id, List.map_map, sandwichAll]
  rfl

def sandwichAllBudget (parameters size : Nat) : Nat :=
  4 + 10 * parameters + 4 * parameters * (sandwichBudget size + 1)

theorem sandwichAllCount_bound (term : TyTerm (Fin n)) (size : Nat) (fits : tyNodes term ≤ size) :
    (sandwichAllCount term).2 ≤ sandwichAllBudget n size := by
  let candidates := (productCount (mapCount id (List.finRange n)).1
    (mapCount (TyTerm.base : Base → TyTerm (Fin n)) [.int, .str, .bool, .unit]).1).1
  have small : ∀ pair ∈ candidates, tyNodes pair.2 ≤ 1 := by
    intro pair member
    simp only [candidates, productCount_value, mapCount_value, List.map_id, List.map_map] at member
    obtain ⟨index, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨base, _, same⟩ := List.mem_map.mp member
    subst pair
    exact Nat.le_refl _
  have processed := sandwichCandidatesCount_bound candidates small term size fits
  have count : candidates.length = 4 * n := by
    simpa only [candidates, productCount_value, mapCount_value, List.map_id, List.map_map,
      Function.comp_def] using TypeSimplificationSize.sandwich_candidate_count n
  rw [count] at processed
  simp only [candidates, mapCount_value, List.map_id] at processed
  change _ ≤ 4 + 10 * n + 4 * n * (sandwichBudget size + 1)
  simp only [sandwichAllCount, mapCount_steps, productCount_steps, mapCount_value, List.map_id,
    List.length_finRange, List.length_map, List.length_cons, List.length_nil]
  omega

def simplifyAllCount (term : TyTerm (Fin n)) : TyTerm (Fin n) × Nat :=
  let first := simplifySafeCount term
  let second := sandwichAllCount first.1
  let third := mergeAllCount second.1
  let last := simplifySafeCount third.1
  (last.1, 3 + first.2 + second.2 + third.2 + last.2)

theorem simplifyAllCount_value (term : TyTerm (Fin n)) :
    (simplifyAllCount term).1 = simplifyAll term := by
  simp only [simplifyAllCount, simplifySafeCount_value, sandwichAllCount_value,
    mergeAllCount_value, simplifyAll]

def totalBudget (parameters size : Nat) : Nat :=
  3 + 2 * varianceBudget size + sandwichAllBudget parameters size + mergeAllBudget parameters size

/-- Complete bound for all four stages, including actual finite candidate
enumeration. It assumes neither supportedness nor successful simplification. -/
theorem simplifyAllCount_bound (term : TyTerm (Fin n)) :
    (simplifyAllCount term).2 ≤ totalBudget n (tyNodes term) := by
  let size := tyNodes term
  have firstSize : tyNodes (simplifySafeCount term).1 ≤ size := by
    rw [simplifySafeCount_value]
    exact (TypeSimplificationSize.simplifySafe_sizes term).2
  have secondSize : tyNodes (sandwichAllCount (simplifySafeCount term).1).1 ≤ size := by
    rw [sandwichAllCount_value]
    exact Nat.le_trans (TypeSimplificationSize.sandwichAll_sizes _).2 firstSize
  have thirdSize : tyNodes (mergeAllCount (sandwichAllCount (simplifySafeCount term).1).1).1 ≤ size := by
    rw [mergeAllCount_value]
    exact Nat.le_trans (TypeSimplificationSize.mergeAll_sizes _).2 secondSize
  have first := simplifySafeCount_bound term size (Nat.le_refl _)
  have second := sandwichAllCount_bound (simplifySafeCount term).1 size firstSize
  have third := mergeAllCount_bound (sandwichAllCount (simplifySafeCount term).1).1 size secondSize
  have last := simplifySafeCount_bound (mergeAllCount (sandwichAllCount (simplifySafeCount term).1).1).1 size thirdSize
  simp only [simplifyAllCount, totalBudget]
  change _ ≤ 3 + 2 * varianceBudget size + sandwichAllBudget n size + mergeAllBudget n size
  omega

theorem simplifyAllCount_instances_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (term : TyTerm (Fin n)) (expected : StructuralBase.Ty RowType) :
    Instances empty join leRow rows (simplifyAllCount term).1 expected ↔
      Instances empty join leRow rows term expected := by
  rw [simplifyAllCount_value]
  exact simplifyAll_instances_exact empty join leRow rowRefl rowTrans rows term expected

end Yulang.TypeSimplificationCost
