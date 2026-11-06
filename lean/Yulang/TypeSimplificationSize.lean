import Yulang.TypeSimplification
import Yulang.InferenceSubstitutionCost

/-!
# Size invariants for the actual automatic simplification pass

Both the subtype checker's value-node measure and the complete type/row
syntax size are bounded here. Successful or failed candidate checks retain
the invariant. Temporary joint substitutions used by merge certificates may
grow a variable to three nodes; their size is at most three times the input.
-/

namespace Yulang.TypeSimplificationSize

open Inference TypeSimplification
open InferenceSubstitutionCost (tyNodes rowNodes)

theorem row_substitution_identity (replacement : Fin n → TyTerm (Fin n)) (row : RowTerm (Fin n)) :
    row.subst (fun index => ⟨replacement index, .var index⟩) = row := by
  induction row <;> simp_all [RowTerm.subst]

theorem substitute_nodes_bound (replacement : Fin n → TyTerm (Fin n)) (factor : Nat)
    (positive : 1 ≤ factor) (bounded : ∀ index, nodes (replacement index) ≤ factor)
    (term : TyTerm (Fin n)) :
    nodes (substituteValues term replacement) ≤ factor * nodes term := by
  induction term with
  | var index => simpa [substituteValues, TyTerm.subst, nodes] using bounded index
  | base | bottom | top | emptyRecord => simpa [substituteValues, TyTerm.subst, nodes] using positive
  | union | inter | pair | record | variant | arrow =>
      simp only [substituteValues, TyTerm.subst, nodes, Nat.mul_add, Nat.mul_one] at *
      omega

theorem substitute_total_nodes_bound (replacement : Fin n → TyTerm (Fin n)) (factor : Nat)
    (positive : 1 ≤ factor) (bounded : ∀ index, tyNodes (replacement index) ≤ factor)
    (term : TyTerm (Fin n)) :
    tyNodes (substituteValues term replacement) ≤ factor * tyNodes term := by
  induction term with
  | var index => simpa [substituteValues, TyTerm.subst, tyNodes] using bounded index
  | base | bottom | top | emptyRecord => simpa [substituteValues, TyTerm.subst, tyNodes] using positive
  | union | inter | pair | record | variant =>
      simp only [substituteValues, TyTerm.subst, tyNodes, Nat.mul_add, Nat.mul_one] at *
      omega
  | arrow input inputRow output outputRow ihi iho =>
      have incoming : rowNodes inputRow ≤ factor * rowNodes inputRow := by
        simpa using Nat.mul_le_mul_right (rowNodes inputRow) positive
      have outgoing : rowNodes outputRow ≤ factor * rowNodes outputRow := by
        simpa using Nat.mul_le_mul_right (rowNodes outputRow) positive
      simp only [substituteValues, TyTerm.subst, row_substitution_identity, tyNodes,
        Nat.mul_add, Nat.mul_one] at *
      omega

theorem replacement_sizes (term : TyTerm (Fin n)) (index : Fin n) :
    nodes (replacement term index) = 1 ∧ tyNodes (replacement term index) = 1 := by
  unfold replacement
  split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem simplify_sizes (term : TyTerm (Fin n)) :
    nodes (simplify term) ≤ nodes term ∧ tyNodes (simplify term) ≤ tyNodes term := by
  constructor
  · simpa only [Nat.one_mul, substituteValues, simplify] using substitute_nodes_bound (replacement term) 1 (by omega)
      (fun index => Nat.le_of_eq (replacement_sizes term index).1) term
  · simpa only [Nat.one_mul, substituteValues, simplify] using substitute_total_nodes_bound (replacement term) 1 (by omega)
      (fun index => Nat.le_of_eq (replacement_sizes term index).2) term

theorem simplifySafe_sizes (term : TyTerm (Fin n)) :
    nodes (simplifySafe term) ≤ nodes term ∧ tyNodes (simplifySafe term) ≤ tyNodes term := by
  unfold simplifySafe
  split
  · exact simplify_sizes term
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem merge_sizes (first second : Fin n) (term : TyTerm (Fin n)) :
    nodes (merge first second term) ≤ nodes term ∧ tyNodes (merge first second term) ≤ tyNodes term := by
  constructor
  · simpa only [Nat.one_mul, merge] using substitute_nodes_bound
      (fun index => if index = first then .var second else .var index) 1 (by omega)
      (by intro index; split <;> exact Nat.le_refl _) term
  · simpa only [Nat.one_mul, merge] using substitute_total_nodes_bound
      (fun index => if index = first then .var second else .var index) 1 (by omega)
      (by intro index; split <;> exact Nat.le_refl _) term

theorem applyMerge_sizes (first second : Fin n) (term : TyTerm (Fin n)) :
    nodes (applyMerge first second term) ≤ nodes term ∧
      tyNodes (applyMerge first second term) ≤ tyNodes term := by
  unfold applyMerge mergeChecked
  split
  · exact merge_sizes first second term
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem mergeCandidates_sizes (candidates : List (Fin n × Fin n)) (term : TyTerm (Fin n)) :
    nodes (mergeCandidates candidates term) ≤ nodes term ∧
      tyNodes (mergeCandidates candidates term) ≤ tyNodes term := by
  induction candidates generalizing term with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons pair rest ih =>
      have tail := ih (applyMerge pair.1 pair.2 term)
      have head := applyMerge_sizes pair.1 pair.2 term
      exact ⟨Nat.le_trans tail.1 head.1, Nat.le_trans tail.2 head.2⟩

theorem mergeAll_sizes (term : TyTerm (Fin n)) :
    nodes (mergeAll term) ≤ nodes term ∧ tyNodes (mergeAll term) ≤ tyNodes term :=
  mergeCandidates_sizes _ term

theorem sandwich_sizes (index : Fin n) (fixed term : TyTerm (Fin n))
    (small : nodes fixed ≤ 1) (totalSmall : tyNodes fixed ≤ 1) :
    nodes (sandwich index fixed term) ≤ nodes term ∧
      tyNodes (sandwich index fixed term) ≤ tyNodes term := by
  constructor
  · simpa only [Nat.one_mul, sandwich] using substitute_nodes_bound
      (fun i => if i = index then fixed else .var i) 1 (by omega)
      (by intro i; split; exact small; exact Nat.le_refl _) term
  · simpa only [Nat.one_mul, sandwich] using substitute_total_nodes_bound
      (fun i => if i = index then fixed else .var i) 1 (by omega)
      (by intro i; split; exact totalSmall; exact Nat.le_refl _) term

theorem applySandwich_sizes (index : Fin n) (fixed term : TyTerm (Fin n))
    (small : nodes fixed ≤ 1) (totalSmall : tyNodes fixed ≤ 1) :
    nodes (applySandwich index fixed term) ≤ nodes term ∧
      tyNodes (applySandwich index fixed term) ≤ tyNodes term := by
  unfold applySandwich
  split
  · exact sandwich_sizes index fixed term small totalSmall
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem sandwichCandidates_sizes (candidates : List (Fin n × TyTerm (Fin n)))
    (small : ∀ pair ∈ candidates, nodes pair.2 ≤ 1 ∧ tyNodes pair.2 ≤ 1)
    (term : TyTerm (Fin n)) :
    nodes (sandwichCandidates candidates term) ≤ nodes term ∧
      tyNodes (sandwichCandidates candidates term) ≤ tyNodes term := by
  induction candidates generalizing term with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons pair rest ih =>
      have pairSize := small pair List.mem_cons_self
      have tail := ih (fun entry member => small entry (List.mem_cons_of_mem _ member))
        (applySandwich pair.1 pair.2 term)
      have head := applySandwich_sizes pair.1 pair.2 term pairSize.1 pairSize.2
      exact ⟨Nat.le_trans tail.1 head.1, Nat.le_trans tail.2 head.2⟩

theorem sandwichAll_sizes (term : TyTerm (Fin n)) :
    nodes (sandwichAll term) ≤ nodes term ∧ tyNodes (sandwichAll term) ≤ tyNodes term := by
  apply sandwichCandidates_sizes
  intro pair member
  obtain ⟨index, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨base, _, same⟩ := List.mem_map.mp member
  subst pair
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem simplifyAll_sizes (term : TyTerm (Fin n)) :
    nodes (simplifyAll term) ≤ nodes term ∧ tyNodes (simplifyAll term) ≤ tyNodes term := by
  have first := simplifySafe_sizes term
  have second := sandwichAll_sizes (simplifySafe term)
  have third := mergeAll_sizes (sandwichAll (simplifySafe term))
  have last := simplifySafe_sizes (mergeAll (sandwichAll (simplifySafe term)))
  exact ⟨Nat.le_trans last.1 (Nat.le_trans third.1 (Nat.le_trans second.1 first.1)),
    Nat.le_trans last.2 (Nat.le_trans third.2 (Nat.le_trans second.2 first.2))⟩

theorem jointReplacement_sizes (positive : Bool) (first second index : Fin n) :
    nodes (jointReplacement positive first second index) ≤ 3 ∧
      tyNodes (jointReplacement positive first second index) ≤ 3 := by
  unfold jointReplacement
  split
  · cases positive <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨by change 1 ≤ 3; decide, by change 1 ≤ 3; decide⟩

theorem jointSubstitution_sizes (positive : Bool) (first second : Fin n) (term : TyTerm (Fin n)) :
    nodes (substituteValues term (jointReplacement positive first second)) ≤ 3 * nodes term ∧
      tyNodes (substituteValues term (jointReplacement positive first second)) ≤ 3 * tyNodes term :=
  ⟨substitute_nodes_bound _ 3 (by decide) (fun index => (jointReplacement_sizes positive first second index).1) term,
   substitute_total_nodes_bound _ 3 (by decide) (fun index => (jointReplacement_sizes positive first second index).2) term⟩

theorem merge_candidate_count (n : Nat) :
    ((List.finRange n).flatMap fun first => (List.finRange n).map fun second => (first, second)).length = n * n := by
  simp [List.length_flatMap, List.map_const', List.sum_replicate_nat]

theorem sandwich_candidate_count (n : Nat) :
    ((List.finRange n).flatMap fun index =>
      ([.int, .str, .bool, .unit] : List Base).map fun base => (index, (TyTerm.base base : TyTerm (Fin n)))).length = 4 * n := by
  simp [List.length_flatMap, List.map_const', List.sum_replicate_nat, Nat.mul_comm]

end Yulang.TypeSimplificationSize
